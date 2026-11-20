// Spending: which notes and deposits to use, and each JoinSplit or merge as steps that are saved before they leave
// the device (storage notes, proof, attestation, relay), so `sync` resumes an operation wherever it stopped.
//
// A JoinSplit takes at most two inputs, and a deposit only as the first. A send or a withdrawal is one JoinSplit, or
// fails when none pays it. A consolidation (`Destination` `self`) is a Nova merge of up to `MAX_MERGE_INPUTS` notes
// and deposits into one note to self, proved by the merge prover (a wallet cannot: its key is 6.3 GB). More take
// another merge, once a root is over the first one's note.
//
// A relayed JoinSplit or merge is done once its change (a merge's note) is final where this wallet expects it, as sync
// sees it: only its own transaction puts that note there, as its salt is fresh and the proof binds it to the inputs'
// nullifiers. The relayer's answer alone could be a lie, a reorg could drop the transaction, and a spent input alone
// could be another device's doing: each device of a wallet locks its inputs in its own state. Only one that cannot
// land fails, which frees its inputs: one that kept reverting with no input spent, or one whose input another
// transaction spent.

import { type Receipt, type Recipient, commit, decodeCode, planPayCode, planSelf, planSend } from '@zerc20/storage-sdk';
import {
  type Address,
  type Hex,
  bytesToHex,
  decodeAbiParameters,
  hexToBytes,
  numberToHex,
  parseAbiParameters,
} from 'viem';
import { UNWRAP_INTENT } from './chain.js';
import { type Ctx, chainCtx, owner, spendKey } from './context.js';
import { core } from './core.js';
import { type ErrorCode, fail, failsOperation } from './errors.js';
import { prove } from './prove.js';
import { scan } from './scan.js';
import type { Indexer } from './servers.js';
import { attest, proofOf, relay, relayMerge, relayerFees, requestProof } from './services.js';
import { type NoteRecord, type OperationRecord, type Position, type SpendOperation, unspent } from './state.js';
import { commitmentsAt, noteReceipt, nullifiersBefore, storageState, takeRefresh, tokenIds } from './sync.js';
import { aspPath, aspPaths, commitmentPath, commitmentPaths } from './tree.js';

/** Something spendable. */
export interface Coin {
  kind: 'note' | 'burn';
  index: number;
  value: bigint;
  /** For a note paid to a receive code, the code's index: the code's own key owns it. Otherwise the wallet's key does. */
  keyIndex?: number;
  /** A note's salt. */
  salt?: Hex;
  /** A deposit's burn salt and sender. */
  burnSalt?: Hex;
  sender?: Hex;
}

export interface Output {
  publicKey: Hex;
  value: bigint;
  salt: Hex;
  role: 'recipient' | 'change' | 'relayer';
}

/** One JoinSplit and how far it got. */
export interface Step {
  inputs: Coin[];
  outputs: [Output, Output];
  /** `unwrap` pays it out as the underlying asset rather than zERC20. */
  withdraw: { recipient: Address; amount: bigint; unwrap?: boolean } | null;
  entropy: Hex;
  stage: 'planned' | 'noted' | 'proved' | 'attested' | 'relayed';
  witness?: string;
  statement?: Record<string, string>;
  request?: object;
  /** Reverts with no sign of it on chain: proved again with the same outputs a few times, then failed. */
  attempts: number;
  /** Once relayed: the block the relayer saw it mined in. */
  relayedBlock?: number;
  /** The indexer's nullifier count once it is past that block, or just after a relay that reverted on an input spent
   * already: that leaves the step `attested`, not relayed again until its change tells whose transaction spent it.
   * Final nullifiers past it, and its inputs still not among them, means whatever spent them is gone: a reorg dropped
   * it, or the relayer never sent it. */
  relayedAt?: number;
  /** The final commitment count once an input is seen spent. Final commitments past it, and the change still not among
   * them, means another transaction spent the input, and this step can never land. */
  spentAt?: number;
}

/** The most inputs one merge spends: the attester takes requests up to 2 MB, at 8 KiB of sealed witness per input
 * sent as hex, and the prover folds them in one job. */
export const MAX_MERGE_INPUTS = 100;

/** One Nova merge of a consolidation and how far it got. */
export interface MergeStep {
  inputs: Coin[];
  /** The note it makes: the inputs less `fee`. */
  output: Output;
  /** Paid publicly to `feeRecipient`, the relayer, grossed up for the protocol's cut. */
  fee: bigint;
  feeRecipient: Address;
  stage: 'planned' | 'noted' | 'attested' | 'proving' | 'proved' | 'relayed';
  /** Only until the prover has it: it holds the inputs' openings. */
  witness?: string;
  /** The attester's `Merge`, and from `attested` on the `MergeRequest` short of its proof. */
  statement?: Record<string, unknown>;
  request?: Record<string, unknown>;
  /** Refused by the prover, or reverting with no sign of it on chain: built again with the same output a few times,
   * then failed. */
  attempts: number;
  /** Built again after a relay of it reverted, which counts in `attempts` beside the prover's refusals: the request
   * out may still land, so the step is not cancelled. */
  sent?: true;
  /** As a JoinSplit's, with `proved` where a JoinSplit is `attested`. */
  relayedBlock?: number;
  relayedAt?: number;
  spentAt?: number;
}

/** Where a send or withdrawal goes; `self` merges the wallet's own notes and nothing leaves. */
export type Destination =
  | { kind: 'address'; recipient: Recipient }
  | { kind: 'code'; code: string }
  | { kind: 'public'; address: Address; unwrap?: boolean }
  | { kind: 'self' };

export interface SpendData {
  to: Destination;
  /** The largest total fee the caller allowed. */
  maxFee: bigint;
  /** A payment's one JoinSplit, or a consolidation's latest merge. */
  step: Step | MergeStep | null;
  /** A consolidation's earlier merges, in a block and not final yet, oldest first. Each stays until final: a reorg that
   * drops one has it relayed again, before any later merge, which spends its note. */
  landing?: MergeStep[];
  /** A consolidation with nothing left to merge: its merges only have to become final. */
  merged?: true;
  /** Why a `merged` consolidation fails once its merges are final: a merge of it failed, or one could not be planned. */
  failure?: { code: ErrorCode; message: string };
  /** The fees of its steps that are final. */
  paid: bigint;
  /** A consolidation of only these notes and deposits (commitment indices). */
  chosen?: number[];
  /** The notes to self its steps made (a payment's change, a consolidation's merged notes), by salt. */
  changes?: Hex[];
  /** The transactions relayed for it. */
  txHashes?: Hex[];
}

/** A pending operation's steps short of final: a consolidation's merges in a block, oldest first, then its current
 * step. */
const stepsOf = (o: SpendOperation): (Step | MergeStep)[] =>
  o.status === 'pending' ? [...(o.data.landing ?? []), ...(o.data.step ? [o.data.step] : [])] : [];

/** The notes and deposits an operation in flight spends: no other operation may take them. */
export const inputsOf = (o: OperationRecord): Coin[] =>
  o.kind === 'deposit' ? [] : stepsOf(o).flatMap((s) => s.inputs);

/** The notes and deposits an operation's transactions in a block spent, short of final: a reorg that drops one brings
 * them back, and the operation relays it again. */
export const minedInputsOf = (o: OperationRecord): Coin[] =>
  o.kind === 'deposit' ? [] : stepsOf(o).flatMap((s) => (s.stage === 'relayed' ? s.inputs : []));

/** A field element's worth of randomness: 31 bytes, so below the BN254 modulus. */
const fresh = (): Hex => bytesToHex(crypto.getRandomValues(new Uint8Array(32)).fill(0, 0, 1));
const word = (v: bigint): Hex => numberToHex(v, { size: 32 });
const bytes32 = (v: bigint): Uint8Array => hexToBytes(word(v));

/** Final, unspent, under the latest proved root of size `rootSize`, and not taken by another operation. */
export function coins(ctx: Ctx, chainId: bigint, tokenId: number, rootSize: number): Coin[] {
  const locked = new Set(
    ctx.state.ops.filter((o) => o.chainId === chainId).flatMap((o) => inputsOf(o).map((c) => c.index)),
  );
  // final or not: once a proved root the chain accepts covers it, a reorg that moves it takes that root back too, and
  // a JoinSplit against it then fails on chain, which frees its inputs
  const usable = (f: Position) => unspent(f) && f.index < rootSize && !locked.has(f.index);
  const notes = ctx.state.notes
    .filter((n) => n.chainId === chainId && n.tokenId === tokenId)
    .flatMap((n) =>
      n.found
        .filter((f) => f.confirmed && usable(f))
        .map((f) => ({
          kind: 'note' as const,
          index: f.index,
          value: n.value,
          ...(n.keyIndex === undefined ? {} : { keyIndex: n.keyIndex }),
          salt: n.salt,
        })),
    );
  const deposits = ctx.state.deposits
    .filter((d) => d.chainId === chainId)
    .flatMap((d) =>
      d.found
        .filter((f) => f.tokenId === tokenId && f.asp === 'approved' && f.amount !== null && usable(f))
        .map((f) => ({ kind: 'burn' as const, index: f.index, value: f.amount!, burnSalt: d.salt, sender: f.sender! })),
    );
  return [...notes, ...deposits].filter((c) => c.value > 0n);
}

/** Whether any of `tokenId`'s notes or deposits is on chain but not spendable yet: not final or confirmed, its spend
 * not looked for yet, not screened, or not under the proved root of size `rootSize`. A note only announced does not
 * count: it may never land. */
export function settling(ctx: Ctx, chainId: bigint, tokenId: number, rootSize: number): boolean {
  const waiting = (f: Position) => !f.spent && f.nullifiedAt === undefined && (f.unchecked || f.index >= rootSize);
  // a zero-value change is never spendable: it is there to carry its payment's receipt
  const notes = ctx.state.notes.filter((n) => n.chainId === chainId && n.tokenId === tokenId && n.value > 0n);
  const deposits = ctx.state.deposits.filter((d) => d.chainId === chainId);
  return (
    notes.some((n) => n.found.some((f) => waiting(f) || (!f.spent && !f.confirmed))) ||
    deposits.some((d) =>
      d.found.some(
        (f) => f.tokenId === tokenId && f.asp !== 'rejected' && (waiting(f) || (!f.spent && f.asp === null)),
      ),
    )
  );
}

/** The index of the first of `sorted` (ascending by value) worth at least `x`. */
function atLeast(sorted: Coin[], x: bigint): number {
  let [lo, hi] = [0, sorted.length];
  while (lo < hi) {
    const mid = (lo + hi) >> 1;
    if (sorted[mid].value < x) lo = mid + 1;
    else hi = mid;
  }
  return lo;
}

/** The inputs of one JoinSplit worth at least `need`: one coin, or a coin plus a note (a deposit can only be the
 * first input). The smallest total wins. O(n log n), for wallets holding many notes. */
export function pick(all: Coin[], need: bigint): Coin[] | null {
  const sorted = [...all].sort((a, b) => (a.value < b.value ? -1 : a.value > b.value ? 1 : 0));
  const notes = sorted.filter((c) => c.kind === 'note');
  let best: Coin[] | null = null;
  let total = 0n;
  const single = sorted[atLeast(sorted, need)];
  if (single) [best, total] = [[single], single.value];
  for (const a of sorted) {
    let i = atLeast(notes, need - a.value);
    if (notes[i] === a) i++;
    const b = notes[i];
    if (b && (!best || a.value + b.value < total)) [best, total] = [[a, b], a.value + b.value];
  }
  return best;
}

/** A consolidation's next merge: up to `MAX_MERGE_INPUTS` coins, the largest first. `null` when a merge would leave
 * nothing better: no coin, a lone note, or no more than the relayer's `fee`.
 * ponytail: one merge per root; merge disjoint sets in parallel if consolidations of thousands get slow. */
export function mergeRound(all: Coin[], fee: bigint): Coin[] | null {
  const merge = [...all]
    .sort((a, b) => (b.value > a.value ? 1 : b.value < a.value ? -1 : 0))
    .slice(0, MAX_MERGE_INPUTS);
  if (merge.length === 0 || (merge.length === 1 && merge[0].kind === 'note')) return null;
  return merge.reduce((s, c) => s + c.value, 0n) > fee ? merge : null;
}

/** How many merges consolidate `all` into one note: each spends up to `MAX_MERGE_INPUTS`, the one before's note among
 * them. A lone deposit takes one, to become a note. */
export function roundsToMerge(all: Coin[]): number {
  const n = all.length;
  if (n === 0 || (n === 1 && all[0].kind === 'note')) return 0;
  return 1 + Math.ceil(Math.max(0, n - MAX_MERGE_INPUTS) / (MAX_MERGE_INPUTS - 1));
}

/** What a consolidation merges: everything, or only the chosen notes and deposits (by commitment index) and the
 * notes its earlier rounds made of them. */
export function mergePool(all: Coin[], chosen: number[] | undefined, changes: Hex[] = []): Coin[] {
  if (!chosen) return all;
  return all.filter((c) => chosen.includes(c.index) || (c.kind === 'note' && changes.includes(c.salt!)));
}

/** The inputs of the one JoinSplit that pays `need` (see `pick`), or why there is none: merging everything worth it
 * into one note first would pay it, coins `onTheWay` might, or nothing will. A payment never waits or merges itself:
 * that is the app's call. */
export function payWith(all: Coin[], need: bigint, fee: bigint, onTheWay: boolean): Coin[] {
  const inputs = pick(all, need);
  if (inputs) return inputs;
  const merged = all.reduce((s, c) => s + c.value, 0n) - BigInt(roundsToMerge(all)) * fee;
  if (merged >= need) fail('needs-consolidation', `no single JoinSplit pays ${need}: consolidate first, then pay`);
  if (onTheWay) fail('funds-settling', `${need} is not spendable yet: notes or deposits are still settling`);
  return fail('insufficient-funds', `${need} is more than the balance`);
}

/** The smallest public withdrawal that still pays `net` after the protocol's cut. The cut is a rate of the whole
 * withdrawal, rounded down, and the rate read off one withdrawal (`fee / gross`) is at most its tier's: the smallest
 * gross that pays `net` at that rate is never more than the answer within the tier, so a read or two settles it.
 * ponytail: where a lower tier's bound lies between two reads, that bound may already pay `net`, a little less than
 * the gross this returns; a getter for the schedule's tiers would find it. */
export async function grossed(ctx: Ctx, chainId: bigint, tokenId: number, net: bigint): Promise<bigint> {
  const chain = chainCtx(ctx, chainId).chain;
  let gross = net;
  // each read moves on by a unit at least, and a few settle each tier a withdrawal crosses
  for (let i = 0; i < 64; i++) {
    const paid = gross - (await chain.withdrawFee(tokenId, gross));
    if (paid >= net) return gross;
    if (paid <= 0n) break;
    gross = ((net - 1n) * gross) / paid + 1n;
  }
  return fail('unavailable', 'the withdrawal fee schedule does not settle');
}

/** A payment's one public withdrawal, and the protocol's cut of it, which the payer pays on top: a withdrawal's pays
 * its recipient `amount` (and the relayer by a note), a private payment's pays the relayer its `fee`. */
export async function withdrawalOf(
  ctx: Ctx,
  chainId: bigint,
  tokenId: number,
  isPublic: boolean,
  amount: bigint,
  fee: bigint,
): Promise<{ withdrawn: bigint; protocol: bigint }> {
  const net = isPublic ? amount : fee;
  const withdrawn = await grossed(ctx, chainId, tokenId, net);
  return { withdrawn, protocol: withdrawn - net };
}

/** The rate, in basis points, of a protocol's `cut` out of a withdrawal of `gross`. The cut is rounded down, so this is
 * exact once `gross` is 10,000 base units or more. */
export const bpsOf = (cut: bigint, gross: bigint): number =>
  gross === 0n ? 0 : Number((cut * 10_000n + gross - 1n) / gross);

/** The most a payment out of `all` pays its recipient, the relayer's `fee` and the protocol's cut on top
 * (`withdrawalOf`): a withdrawal of what the relayer leaves, less the cut on it, or a private payment of what the
 * relayer's grossed fee leaves. Coins one JoinSplit cannot spend together (`pick`) are merged first, each merge
 * paying the relayer's grossed fee, as a consolidation's quote does. `fee` is all the fees take of `all`; where they
 * take it all, what they would be with nothing left to pay. */
export async function maxPayment(
  ctx: Ctx,
  chainId: bigint,
  tokenId: number,
  isPublic: boolean,
  all: Coin[],
  fee: bigint,
): Promise<{ amount: bigint; fee: bigint; merges: number }> {
  const whole = all.length < 2 || (all.length === 2 && all.some((c) => c.kind === 'note'));
  const merges = whole ? 0 : roundsToMerge(all);
  const gross = !isPublic || merges > 0 ? await grossed(ctx, chainId, tokenId, fee) : fee;
  const fees = BigInt(merges) * gross + (isPublic ? fee : gross);
  const total = all.reduce((s, c) => s + c.value, 0n);
  const left = total - fees;
  if (left <= 0n) return { amount: 0n, fee: fees, merges };
  const amount = isPublic ? left - (await chainCtx(ctx, chainId).chain.withdrawFee(tokenId, left)) : left;
  return { amount, fee: total - amount, merges };
}

/** Plans the next step of `op`: a payment's only JoinSplit (or throws why there is none), or a consolidation's next
 * merge. `null`: wait for the last merge's note to become spendable. `'done'`: nothing left worth merging. */
export async function planStep(ctx: Ctx, op: SpendOperation): Promise<Step | MergeStep | null | 'done'> {
  const data = op.data;
  const c = chainCtx(ctx, op.chainId);
  const root = (await c.indexer.status()).latestRoot;
  const all = coins(ctx, op.chainId, op.tokenId, root?.size ?? 0);
  const { relayer, publicKey: relayerKey, fees } = await relayerFees(c.chain);
  const fee = fees.get(op.tokenId)?.fee ?? fail('unavailable', `the relayer does not relay token ${op.tokenId}`);
  const self = owner(ctx)!.publicKey;
  const out = (publicKey: Hex, value: bigint, role: Output['role'], salt: Hex = fresh()): Output => ({
    publicKey,
    value,
    salt,
    role,
  });

  if (data.to.kind === 'self') {
    if (!ctx.network.mergeProver) fail('invalid', 'this network has no merge prover');
    // the last merge's note first has to land under a proved root
    if (hasPendingChange(ctx, op, root?.size ?? 0)) return null;
    // one still settling is waited for, not left out; those its own earlier merges spend are not settling
    const merging = new Set(inputsOf(op).map((c) => c.index));
    const left = data.chosen?.filter((i) => !merging.has(i));
    if (left && chosenSettling(ctx, op.chainId, left, all)) return null;
    const merge = mergeRound(mergePool(all, data.chosen, data.changes), fee);
    const gross = await grossed(ctx, op.chainId, op.tokenId, fee);
    const total = merge?.reduce((s, x) => s + x.value, 0n) ?? 0n;
    if (!merge || total <= gross) {
      if (data.chosen && !data.changes?.length)
        fail('invalid', 'the chosen notes and deposits are worth no more than the fee');
      return 'done';
    }
    if (feesOf(op) + gross > data.maxFee)
      fail('fee-too-high', `consolidating would exceed the fee limit ${data.maxFee}`);
    return {
      inputs: merge,
      output: out(self, total - gross, 'change'),
      fee: gross,
      feeRecipient: relayer,
      stage: 'planned',
      attempts: 0,
    };
  }

  // the only step: a private payment pays the relayer publicly (both outputs are taken), a withdrawal by a note
  const { withdrawn, protocol } = await withdrawalOf(
    ctx,
    op.chainId,
    op.tokenId,
    data.to.kind === 'public',
    op.amount,
    fee,
  );
  const need = op.amount + fee + protocol;
  const onTheWay =
    ctx.state.ops.some((o) => o !== op && o.status === 'pending') ||
    settling(ctx, op.chainId, op.tokenId, root?.size ?? 0);
  const inputs = payWith(all, need, fee, onTheWay);
  const total = inputs.reduce((s, x) => s + x.value, 0n);
  if (data.paid + fee + protocol > data.maxFee)
    fail('fee-too-high', `fees ${data.paid + fee + protocol} exceed ${data.maxFee}`);
  const change = out(self, total - need, 'change');
  let step: Step;
  if (data.to.kind === 'public') {
    step = {
      inputs,
      outputs: [out(relayerKey, fee, 'relayer'), change],
      withdraw: { recipient: data.to.address, amount: withdrawn, unwrap: data.to.unwrap },
      entropy: fresh(),
      stage: 'planned',
      attempts: 0,
    };
  } else {
    const publicKey = data.to.kind === 'address' ? data.to.recipient.publicKey : codeOf(data.to.code).publicKey;
    const recipient = out(bytesToHex(publicKey), op.amount, 'recipient');
    step = {
      inputs,
      outputs: [recipient, change],
      withdraw: { recipient: relayer, amount: withdrawn },
      entropy: fresh(),
      stage: 'planned',
      attempts: 0,
    };
  }
  return step;
}

/** Whether any of a consolidation's chosen notes and deposits (commitment indices) is still settling: not among the
 * spendable `all` yet. Throws for one that never merges: a deposit the ASP rejected. A quote and every merge go by
 * this one rule. */
export function chosenSettling(ctx: Ctx, chainId: bigint, chosen: number[], all: Coin[]): boolean {
  const found = [
    ...ctx.state.notes
      .filter((n) => n.chainId === chainId)
      .flatMap((n) => n.found.map((f) => ({ ...f, amount: n.value, rejected: false }))),
    ...ctx.state.deposits
      .filter((d) => d.chainId === chainId)
      .flatMap((d) => d.found.map((f) => ({ ...f, rejected: f.asp === 'rejected' }))),
  ].filter((f) => chosen.includes(f.index) && !f.spent);
  if (found.some((f) => f.rejected)) fail('invalid', 'a chosen deposit was rejected: only rage exit returns it');
  return found.some((f) => !all.some((c) => c.index === f.index));
}

/** A change note of this operation that is neither spendable yet (confirmed, its spend looked for, and under the root
 * of size `rootSize`, as `coins` takes it) nor already spent by a later step. */
function hasPendingChange(ctx: Ctx, op: SpendOperation, rootSize: number): boolean {
  const salts = new Set(op.data.changes ?? []);
  const settled = (f: NoteRecord['found'][number]) => f.spent || (!!f.confirmed && !f.unchecked && f.index < rootSize);
  return ctx.state.notes.some((n) => salts.has(n.salt) && !n.found.some(settled));
}

export const codeOf = (code: string) => decodeCode(code) ?? fail('invalid', 'not a receive code');

const openingOf = (op: SpendOperation, o: Output) => ({
  chainId: op.chainId,
  tokenId: op.tokenId,
  value: bytes32(o.value),
  noteSalt: hexToBytes(o.salt),
});

/** What `step` paid besides `op`'s amount, the relayer's fee and the protocol's cut: what its inputs hold beyond the
 * amount and the change. */
export const feeOf = (op: SpendOperation, step: Step): bigint =>
  step.inputs.reduce((s, c) => s + c.value, 0n) - step.outputs.find((o) => o.role === 'change')!.value - op.amount;

/** What a payment or withdrawal was, for its change to carry to the wallet's other devices. */
function receiptOf(op: SpendOperation, step: Step): Receipt {
  const to = op.data.to;
  const [kind, counterparty]: [Receipt['kind'], Uint8Array] =
    to.kind === 'address'
      ? ['sent', to.recipient.address]
      : to.kind === 'code'
        ? ['sent-to-code', codeOf(to.code).burnAddress]
        : to.kind === 'public'
          ? [to.unwrap ? 'unwrapped' : 'withdrawn', hexToBytes(to.address)]
          : fail('invalid', 'a merge has no JoinSplit');
  return { kind, amount: bytes32(op.amount), fee: bytes32(feeOf(op, step)), counterparty };
}

/** Writes the step's notes to storage before anything reaches the chain: the payment to its recipient and the
 * change to the own lane, in one batch. The change, written even at zero value, carries the payment's receipt, which
 * every device of the wallet shows once it lands; it is recorded here too, so it is found. */
async function writeNotes(ctx: Ctx, op: SpendOperation, step: Step): Promise<void> {
  const data = op.data;
  const opening = (o: Output) => openingOf(op, o);
  const recipient = step.outputs.find((o) => o.role === 'recipient');
  const change = step.outputs[1];
  const receipt = receiptOf(op, step);
  const result = await commit(ctx.storage, ctx.view, storageState(ctx), async (s) => [
    ...(recipient && data.to.kind === 'address' ? planSend(ctx.view, s, data.to.recipient, opening(recipient)) : []),
    ...(recipient && data.to.kind === 'code'
      ? await planPayCode(ctx.storage, ctx.view, s, codeOf(data.to.code), opening(recipient))
      : []),
    ...planSelf(ctx.view, s, opening(change), receipt),
  ]);
  takeRefresh(ctx, result, await tokenIds(ctx));
  recordOwn(ctx, op, change, receipt);
}

/** Writes a merge's note to the own lane before its witness leaves, and records it, as a payment's change. */
async function writeMerge(ctx: Ctx, op: SpendOperation, step: MergeStep): Promise<void> {
  const receipt: Receipt = {
    kind: 'merged',
    amount: bytes32(step.output.value),
    fee: bytes32(step.fee),
    counterparty: new Uint8Array(20),
  };
  const result = await commit(ctx.storage, ctx.view, storageState(ctx), (s) =>
    planSelf(ctx.view, s, openingOf(op, step.output), receipt),
  );
  takeRefresh(ctx, result, await tokenIds(ctx));
  recordOwn(ctx, op, step.output, receipt);
}

/** Records a note to self that `op` is making, so it is found once it lands. */
function recordOwn(ctx: Ctx, op: SpendOperation, o: Output, receipt: Receipt): void {
  const from = commitmentsAt(ctx.state.chains.find((c) => c.chainId === op.chainId)?.samples ?? [], Date.now());
  const noteHash = core.noteHash(op.chainId, o.publicKey, word(o.value), op.tokenId, o.salt) as Hex;
  const record: NoteRecord = {
    chainId: op.chainId,
    tokenId: op.tokenId,
    value: o.value,
    salt: o.salt,
    source: 'self',
    receipt: noteReceipt(receipt),
    peer: null,
    atNs: null,
    noteHash,
    watch: { key: numberToHex(core.noteTag(op.tokenId, noteHash), { size: 4 }), from, scannedTo: from },
    found: [],
  };
  if (!ctx.state.notes.some((n) => n.chainId === op.chainId && n.salt === o.salt)) ctx.state.notes.push(record);
  op.data.changes = [...(op.data.changes ?? []), o.salt];
}

const keyOf = (ctx: Ctx, op: SpendOperation, c: Coin) =>
  spendKey(ctx, c.keyIndex === undefined ? undefined : { chainId: op.chainId, tokenId: op.tokenId, index: c.keyIndex });

/** The attester's merge witness JSON (`backend/attester/README.md`) with each input's private key in place of its keys
 * and signature, which `core.signMerge` puts in, and the public inputs it proves against: every input under one proved
 * root, every deposit under one ASP root. `null` until a root is over them all. */
async function mergeWitnessOf(
  ctx: Ctx,
  op: SpendOperation,
  step: MergeStep,
): Promise<{ witness: string; inputs: Record<string, string>; size: number } | null> {
  const c = chainCtx(ctx, op.chainId);
  const paths = await commitmentPaths(
    c.indexer,
    c.chain,
    step.inputs.map((x) => x.index),
  );
  if (!paths) return null; // a root over the inputs is not proved yet
  const burns = step.inputs.filter((x) => x.kind === 'burn');
  const asps = await aspPaths(
    c.asp,
    c.chain,
    burns.map((x) => x.index),
  );
  if (!asps) return null; // not in the ASP's published root yet
  const asp = new Map(burns.map((x, i) => [x.index, asps[i]]));
  // the root the paths fold to, not a second read that a new root could overtake
  const aspRoot = asps[0]?.root ?? (await c.chain.latestAspRoot());
  const zero = Array<string>(32).fill('0');
  const witness = {
    inputs: step.inputs.map((x, i) => {
      const burn = x.kind === 'burn';
      return {
        is_burn: burn,
        private_key: keyOf(ctx, op, x).secret,
        commitment_index: `${x.index}`,
        commitment_siblings: paths[i].siblings,
        note_value: burn ? '0' : `${x.value}`,
        note_salt: burn ? '0' : x.salt!,
        burn_salt: burn ? x.burnSalt! : '0',
        burn_from: burn ? x.sender! : '0',
        burn_value: burn ? `${x.value}` : '0',
        asp_siblings: asp.get(x.index)?.siblings ?? zero,
      };
    }),
    out_public_key: step.output.publicKey,
    out_salt: step.output.salt,
  };
  const inputs = {
    tokenId: word(BigInt(op.tokenId)),
    chainId: word(op.chainId),
    commitmentRoot: paths[0].root,
    aspRoot,
    fee: word(step.fee),
    feeRecipient: step.feeRecipient,
  };
  return { witness: JSON.stringify(witness), inputs, size: paths[0].size };
}

/** `Verifier.NovaDeciderProof`, as the merge prover encodes it. */
const NOVA_PROOF = parseAbiParameters(
  '(uint256 challenge, uint256[2] runningCmE, uint256[2] cmT, uint256[2] runningCmW, uint256[2] incomingCmW, uint256[12] proof)',
);

/** The JoinSplit input JSON (snarkjs's, which `core.signTransact` turns into the attester's), and the public inputs it
 * starts from. */
async function witnessOf(
  ctx: Ctx,
  op: SpendOperation,
  step: Step,
): Promise<{ witness: Record<string, unknown>; size: number } | null> {
  const c = chainCtx(ctx, op.chainId);
  const [in0, in1] = step.inputs as [Coin, Coin | undefined];
  const p0 = await commitmentPath(c.indexer, c.chain, in0.index);
  const p1 = in1 ? await commitmentPath(c.indexer, c.chain, in1.index) : null;
  if (!p0 || (in1 && !p1)) return null; // a root over the input is not proved yet
  if (p1 && p1.size !== p0.size) return null; // a root was proved in between: try again
  const asp = in0.kind === 'burn' ? await aspPath(c.asp, c.chain, in0.index) : null;
  if (in0.kind === 'burn' && !asp) return null; // not in the ASP's published root yet
  // the root the path folds to, not a second read that a new root could overtake
  const aspRoot = asp ? asp.root : await c.chain.latestAspRoot();
  const zero = Array<string>(32).fill('0');
  const key0 = keyOf(ctx, op, in0);
  const key1 = in1 ? keyOf(ctx, op, in1) : null;
  const [o1, o2] = step.outputs;
  const burn = in0.kind === 'burn';
  return {
    size: p0.size,
    witness: {
      token_id: `${op.tokenId}`,
      chain_id: `${op.chainId}`,
      commitment_root: p0.root,
      asp_root: aspRoot,
      entropy: step.entropy,
      in0_is_burn: burn ? '1' : '0',
      in1_is_dummy: in1 ? '0' : '1',
      in_note0_public_key: burn ? '0' : key0.publicKey,
      in_note0_value: burn ? '0' : `${in0.value}`,
      in_note0_salt: burn ? '0' : in0.salt!,
      in_note1_public_key: key1 ? key1.publicKey : '0',
      in_note1_value: in1 ? `${in1.value}` : '0',
      in_note1_salt: in1 ? in1.salt! : '0',
      burn_public_key: burn ? key0.publicKey : '0',
      burn_salt: burn ? in0.burnSalt! : '0',
      burn_transfer_from: burn ? in0.sender! : '0',
      burn_transfer_value: burn ? `${in0.value}` : '0',
      withdraw_recipient_private: step.withdraw ? BigInt(step.withdraw.recipient).toString() : '0',
      withdraw_amount_private: step.withdraw ? `${step.withdraw.amount}` : '0',
      withdraw_intent_private: step.withdraw?.unwrap ? `${UNWRAP_INTENT}` : '0',
      out_note1_public_key: o1.publicKey,
      out_note1_value: `${o1.value}`,
      out_note1_salt: o1.salt,
      out_note2_public_key: o2.publicKey,
      out_note2_value: `${o2.value}`,
      out_note2_salt: o2.salt,
      private_key0: key0.secret,
      private_key1: key1 ? key1.secret : '0',
      auth_key_hash0: key0.authKeyHash,
      auth_key_hash1: key1 ? key1.authKeyHash : '0',
      commitment_index0: `${in0.index}`,
      commitment_index1: in1 ? `${in1.index}` : '0',
      in0_merkle_siblings: p0.siblings,
      in1_merkle_siblings: p1 ? p1.siblings : zero,
      in0_asp_siblings: asp ? asp.siblings : zero,
    },
  };
}

/** This wallet's records of the note or deposit at `index`: one, but for a tag that also matched a note it expects. */
const positionsAt = (ctx: Ctx, chainId: bigint, index: number): Position[] =>
  [...ctx.state.notes, ...ctx.state.deposits]
    .filter((r) => r.chainId === chainId)
    .flatMap((r) => (r.found as Position[]).filter((f) => f.index === index));

/** The final one of them: an input is final. */
const positionOf = (ctx: Ctx, chainId: bigint, index: number): Position | undefined =>
  positionsAt(ctx, chainId, index).find((f) => !f.tentative);

/** Whether an input is spent: one sync saw spent, or a nullifier the step's statement names among the indexer's, final
 * or not. By the statement rather than sync's watches: an input may be spent before it is final, which sync does not
 * watch it for. Looked for from where the earliest input's page of commitments begins, as no spend of an input comes
 * before. Reads the pages everyone polls, never asks about a nullifier. */
async function inputsSpent(ctx: Ctx, op: SpendOperation, step: Step | MergeStep): Promise<boolean> {
  if (step.inputs.some((coin) => positionOf(ctx, op.chainId, coin.index)?.spent)) return true;
  const named =
    'output' in step
      ? (step.statement!.nullifiers as string[])
      : [step.statement!.nullifier0, step.statement!.nullifier1];
  const c = chainCtx(ctx, op.chainId);
  const from = await nullifiersBefore(c.indexer)(Math.min(...step.inputs.map((coin) => coin.index)));
  const { nullifiers } = await c.indexer.status();
  const watches = named.map((n) => ({
    key: numberToHex(BigInt(n), { size: 32 }).slice(0, 18) as Hex,
    from,
    scannedTo: from,
  }));
  const hits = await scan(watches, 8, (p) => c.indexer.page('nullifiers', p), from, nullifiers);
  return hits.length > 0;
}

/** Where a relayed step stands, by its `change` (a merge's note) and its `inputs` as sync last saw them:
 * - `landed`: the change is final where this wallet expects it;
 * - `taken`: an input is spent and the final commitments passed `spentAt` without the change, so another transaction
 *   spent it, and this step can never land;
 * - `dropped`: no input is spent and the final nullifiers passed `relayedAt` without them: whatever was spending them
 *   is gone, a reorg dropped it or the relayer never sent it;
 * - `mined`: the change is in a block, not final yet;
 * - `waiting`: none of these yet. */
export function relayedState(
  change: Pick<NoteRecord, 'found' | 'watch'> | undefined,
  inputs: (Position | undefined)[],
  relayedAt: number | undefined,
  spentAt: number | undefined,
): 'landed' | 'taken' | 'dropped' | 'mined' | 'waiting' {
  const seen = change?.found.filter((f) => f.confirmed) ?? [];
  if (seen.some((f) => !f.tentative)) return 'landed';
  if (inputs.some((f) => f?.spent)) {
    // a final position not read yet may be the change
    const missed =
      spentAt !== undefined &&
      !!change?.watch &&
      change.watch.scannedTo >= spentAt &&
      !change.found.some((f) => !f.tentative);
    if (missed) return 'taken';
  } else {
    const watches = inputs.flatMap((f) => (f?.nullifier ? [f.nullifier] : []));
    if (relayedAt !== undefined && watches.length > 0 && watches.every((w) => w.scannedTo >= relayedAt))
      return 'dropped';
  }
  return seen.length > 0 ? 'mined' : 'waiting';
}

/** `relayedState` of `step`, failing the operation once another transaction took an input. The first time an input
 * is seen spent, short of the step landing, it notes the final commitment count: a later status counts no fewer, so
 * once the change's watch passes it, it has looked wherever that transaction put its notes. */
async function standing(
  ctx: Ctx,
  op: SpendOperation,
  step: Step | MergeStep,
): Promise<ReturnType<typeof relayedState>> {
  const inputs = step.inputs.map((coin) => positionOf(ctx, op.chainId, coin.index));
  const salt = 'output' in step ? step.output.salt : step.outputs[1].salt;
  const change = ctx.state.notes.find((n) => n.chainId === op.chainId && n.salt === salt);
  const now = relayedState(change, inputs, step.relayedAt, step.spentAt);
  if (now === 'taken')
    fail('spent-elsewhere', 'another device of this wallet spent a note or deposit of it first: it paid nothing');
  if (now !== 'landed' && step.spentAt === undefined && inputs.some((f) => f?.spent)) {
    step.spentAt = (await chainCtx(ctx, op.chainId).indexer.status()).commitmentsFinal;
    await ctx.save();
  }
  return now;
}

/** The indexer's nullifier count once it is past `block`, so past the nullifiers of a transaction mined there unless a
 * reorg moved them; `undefined` until then. The relayer answers once the block is mined, which may be before the
 * indexer has read it. */
export async function nullifiersPast(indexer: Pick<Indexer, 'status'>, block: number): Promise<number | undefined> {
  if ((await indexer.status()).cursor < block) return undefined;
  // a status reads its counts before its cursor, so the count comes from the next one
  return (await indexer.status()).nullifiers;
}

/** Whether `op` is on chain: done, or its transactions relayed, which the relayer answers once they are mined. Until
 * they are final a reorg may still drop one, and the operation relays it again. A consolidation is on chain once it has
 * nothing left to merge: its last merge's note is then under a proved root, so it can be spent. One that fails once its
 * merges are final is not. A deposit is on chain once done. */
export function landed(op: OperationRecord): boolean {
  if (op.status !== 'pending' || op.kind === 'deposit') return op.status === 'done';
  if (op.kind === 'consolidate')
    return !!op.data.merged && !op.data.failure && stepsOf(op).every((s) => s.stage === 'relayed');
  return op.data.step?.stage === 'relayed';
}

/** What `op` paid in fees, its transactions in a block counted before they are final. */
export function feesOf(op: SpendOperation): bigint {
  return stepsOf(op).reduce(
    (sum, s) => (s.stage !== 'relayed' ? sum : sum + ('output' in s ? s.fee : feeOf(op, s))),
    op.data.paid,
  );
}

/** Whether `op` can still be cancelled, having paid nothing: a payment, withdrawal or consolidation under way with no
 * request out to the relayer, and no merge of it in a block. A step at its relay stage has one out, as its request leaves
 * the moment it gets there; so has one built again after a relay of it reverted, as that request may still land: a
 * JoinSplit's `attempts` count only those, and a merge, whose `attempts` count its prover's refusals too, is `sent`. */
export function cancellable(op: OperationRecord): boolean {
  if (op.status !== 'pending' || op.kind === 'deposit' || op.data.paid > 0n || op.data.landing?.length) return false;
  const step = op.data.step;
  if (!step) return true;
  if ('output' in step) return !step.sent && step.stage !== 'proved' && step.stage !== 'relayed';
  return step.attempts === 0 && step.stage !== 'attested' && step.stage !== 'relayed';
}

function markSpent(ctx: Ctx, op: SpendOperation, step: { inputs: Coin[] }): void {
  for (const coin of step.inputs) for (const f of positionsAt(ctx, op.chainId, coin.index)) f.spent = true;
}

/** A note to self's position (its `salt`'s) as the relayer reported it, until sync finds it final. */
function placeChange(ctx: Ctx, op: SpendOperation, salt: Hex, index: number | null): void {
  const note = ctx.state.notes.find((n) => n.chainId === op.chainId && n.salt === salt);
  if (note && index !== null && !note.found.some((f) => f.index === index)) {
    note.found.push({ index, tentative: true, spent: false });
  }
}

/** Takes `op` as far as it can go now, saving before each step that leaves the device. One cancelled meanwhile
 * (`cancel`) finishes the stage under way and starts no other: its status is looked at after each, and nothing it does
 * later is kept, as it is out of the state. A relayer that is relaying its request already throws `Relaying`. */
export async function advanceSpend(ctx: Ctx, op: SpendOperation): Promise<void> {
  if (op.data.to.kind === 'self') return advanceConsolidation(ctx, op);
  if (op.status !== 'pending') return;
  const data = op.data;
  const c = chainCtx(ctx, op.chainId);
  const step = data.step as Step; // planned as it began: a payment is its one JoinSplit
  if (step.stage === 'planned') {
    await writeNotes(ctx, op, step);
    step.stage = 'noted';
    await ctx.save();
  }
  if (op.status !== 'pending') return;
  if (step.stage === 'noted') {
    const built = await witnessOf(ctx, op, step);
    if (!built) return;
    const inputs = {
      tokenId: word(BigInt(op.tokenId)),
      chainId: word(op.chainId),
      commitmentRoot: built.witness.commitment_root,
      aspRoot: built.witness.asp_root,
    };
    // the attester's own check, run here first: a witness it would refuse never leaves the device. What it is sent
    // holds no private key, only what the keys derive and the owners' signatures on this statement.
    let statement: Record<string, string>;
    let witness: string;
    try {
      const signed = JSON.parse(core.signTransact(JSON.stringify(inputs), JSON.stringify(built.witness))) as {
        statement: Record<string, string>;
        witness: unknown;
      };
      statement = signed.statement;
      witness = JSON.stringify(signed.witness);
    } catch (e) {
      return fail('invalid', `the attester would refuse this witness: ${(e as Error).message}`);
    }
    const { proof, signals } = await prove(ctx.network.circuits.joinsplit, built.witness, ctx.fetch);
    const order = [
      'nullifier0',
      'nullifier1',
      'withdrawRecipient',
      'withdrawAmount',
      'withdrawIntent',
      'noteHash1',
      'noteHash2',
      'tokenId',
      'chainId',
      'commitmentRoot',
      'aspRoot',
    ];
    if (order.some((k, i) => BigInt(statement[k]) !== signals[i]))
      fail('invalid', 'the proof and the statement disagree');
    step.witness = witness;
    step.statement = statement;
    step.request = { rootIndex: built.size, proof, publicSignals: statement };
    step.stage = 'proved';
    await ctx.save();
  }
  if (op.status !== 'pending') return;
  if (step.stage === 'proved') {
    const attestation = await attest(c.chain, step.statement!, step.witness!);
    step.request = { ...step.request!, attestation };
    delete step.witness; // it holds the inputs' openings; the attestation is all that is needed of it now
    step.stage = 'attested';
    await ctx.save();
  }
  if (op.status !== 'pending') return;
  if (step.stage === 'attested' && step.relayedAt !== undefined) {
    // a relay of it reverted on an input spent already: an earlier relay of it landed, one whose answer was lost, or
    // another transaction spent the input. Relaying it again would tell nothing more
    const now = await standing(ctx, op, step);
    if (now === 'waiting') return;
    if (now === 'dropped') delete step.relayedAt;
    else step.stage = 'relayed';
    await ctx.save();
  }
  if (step.stage === 'attested') {
    const relayerOut = step.outputs.find((o) => o.role === 'relayer');
    const result = await relay(
      c.chain,
      step.request!,
      relayerOut ? { value: relayerOut.value, salt: relayerOut.salt } : undefined,
    );
    if ('reverted' in result) {
      if (await inputsSpent(ctx, op, step)) {
        // the indexer counts the nullifiers of whatever spent it already
        step.relayedAt = (await c.indexer.status()).nullifiers;
        await ctx.save();
        return;
      }
      // spent on chain before the indexer shows it: by this step's own relay, whose answer was lost, or by another
      // device. Proving it again cannot land it; relayed again next sync, it reverts the same until the indexer shows
      // the spend, and an indexer that never does shows as one behind the chain
      if (result.spent) fail('indexer-mismatch', 'the relayer finds an input spent that the indexer does not show');
      // no input spent, so it is not on chain: the verifier or the relayer refuses it as it is. Proved and attested
      // again with the same outputs, next sync, it gets past a root an emergency took back or an attester replaced
      // since, though not past a fee that rose, a paused token or a blocked recipient. One that keeps reverting
      // cannot land, so failing it frees its inputs
      if (++step.attempts > 3)
        fail(
          /the fee is/.test(result.reverted) ? 'fee-too-high' : 'invalid',
          `the transaction keeps reverting: ${result.reverted}`,
        );
      step.stage = 'noted';
      await ctx.save();
      return;
    }
    placeChange(ctx, op, step.outputs[1].salt, result.noteIndex2);
    data.txHashes = [...(data.txHashes ?? []), result.txHash];
    step.relayedBlock = result.block;
    step.stage = 'relayed';
    await ctx.save();
  }
  if (step.stage === 'relayed') {
    step.relayedAt ??= await nullifiersPast(c.indexer, step.relayedBlock!);
    const now = await standing(ctx, op, step);
    if (now === 'dropped') {
      // relay it again next sync; if it did land after all, that reverts and finds it
      step.stage = 'attested';
      delete step.relayedAt;
      await ctx.save();
    }
    if (now !== 'landed') return;
    markSpent(ctx, op, step);
    data.paid += feeOf(op, step);
    data.step = null;
    op.status = 'done';
    await ctx.save();
  }
}

/** Takes a consolidation's merge as far as it can go now, saving before each step that leaves the device. True once
 * it is in a block. */
async function advanceMerge(ctx: Ctx, op: SpendOperation, step: MergeStep): Promise<boolean> {
  const data = op.data;
  const c = chainCtx(ctx, op.chainId);
  const prover = ctx.network.mergeProver ?? fail('invalid', 'this network has no merge prover');
  // built again from its inputs, after a refusal or a revert: the same output, so the same note in storage
  const again = async (why: string) => {
    if (++step.attempts > 3)
      fail(/the fee is/.test(why) ? 'fee-too-high' : 'invalid', `the merge keeps failing: ${why}`);
    step.stage = 'noted';
    await ctx.save();
    return false;
  };
  if (step.stage === 'planned') {
    await writeMerge(ctx, op, step);
    step.stage = 'noted';
    await ctx.save();
  }
  if (op.status !== 'pending') return false;
  if (step.stage === 'noted') {
    const built = await mergeWitnessOf(ctx, op, step);
    if (!built) return false;
    // the attester's own check, run here first: a witness it would refuse never leaves the device. What it and the merge
    // prover are sent holds no private key, only what the keys derive and the owners' signatures on this merge.
    let statement: Record<string, unknown>;
    let witness: string;
    try {
      const signed = JSON.parse(core.signMerge(JSON.stringify(built.inputs), built.witness)) as {
        statement: Record<string, unknown>;
        witness: unknown;
      };
      statement = signed.statement;
      witness = JSON.stringify(signed.witness);
    } catch (e) {
      return fail('invalid', `the attester would refuse this merge: ${(e as Error).message}`);
    }
    const attestation = await attest(c.chain, statement, witness, step.inputs.length);
    const { tokenId, commitmentRoot, aspRoot, noteHash, fee, feeRecipient, nullifiers } = statement;
    step.witness = witness;
    step.statement = statement;
    step.request = {
      rootIndex: built.size,
      tokenId,
      commitmentRoot,
      aspRoot,
      noteHash,
      fee,
      feeRecipient,
      nullifiers,
      attestation,
    };
    step.stage = 'attested';
    await ctx.save();
  }
  if (op.status !== 'pending') return false;
  if (step.stage === 'attested') {
    await requestProof(c.chain, prover, step.statement!, step.witness!, step.inputs.length);
    delete step.witness; // the prover has it: the inputs' openings need not stay saved here
    step.stage = 'proving';
    await ctx.save();
  }
  if (step.stage === 'proving') {
    const job = await proofOf(c.chain, prover, step.statement!.noteHash as Hex);
    if (job?.status === 'queued' || job?.status === 'proving') return false;
    if (!job) {
      // the prover lost it in a restart: built and sent again, which is no fault of the merge's
      step.stage = 'noted';
      await ctx.save();
      return false;
    }
    if (job.status !== 'done') return again(job.error ?? 'the merge prover refused it');
    const [proof] = decodeAbiParameters(NOVA_PROOF, job.proof!);
    step.request = { ...step.request!, proof };
    step.stage = 'proved';
    await ctx.save();
  }
  if (op.status !== 'pending') return false;
  if (step.stage === 'proved' && step.relayedAt !== undefined) {
    // as a JoinSplit's, told apart by its note
    const now = await standing(ctx, op, step);
    if (now === 'waiting') return false;
    if (now === 'dropped') delete step.relayedAt;
    else step.stage = 'relayed';
    await ctx.save();
  }
  if (step.stage === 'proved') {
    const result = await relayMerge(c.chain, step.request!);
    if ('reverted' in result) {
      if (await inputsSpent(ctx, op, step)) {
        step.relayedAt = (await c.indexer.status()).nullifiers;
        await ctx.save();
        return false;
      }
      // as a JoinSplit's: relayed again next sync rather than proved again
      if (result.spent) fail('indexer-mismatch', 'the relayer finds an input spent that the indexer does not show');
      // as a JoinSplit's: built again with the same output, next sync
      step.sent = true;
      return again(result.reverted);
    }
    placeChange(ctx, op, step.output.salt, result.noteIndex);
    data.txHashes = [...(data.txHashes ?? []), result.txHash];
    step.relayedBlock = result.block;
    step.stage = 'relayed';
    await ctx.save();
  }
  return step.stage === 'relayed';
}

/** Whether a relayed merge is final, its inputs then spent and its fee paid. One a reorg dropped goes back to be relayed
 * again; if it did land after all, that reverts and finds it. */
async function settleMerge(ctx: Ctx, op: SpendOperation, step: MergeStep): Promise<boolean> {
  step.relayedAt ??= await nullifiersPast(chainCtx(ctx, op.chainId).indexer, step.relayedBlock!);
  const now = await standing(ctx, op, step);
  if (now === 'dropped') {
    step.stage = 'proved';
    delete step.relayedAt;
    await ctx.save();
  }
  if (now !== 'landed') return false;
  markSpent(ctx, op, step);
  op.data.paid += step.fee;
  await ctx.save();
  return true;
}

/** Takes a merge as far as it can go now: in a block (again, after a reorg dropped it), then final. Null while it is
 * not in a block. */
async function driveMerge(ctx: Ctx, op: SpendOperation, step: MergeStep): Promise<'final' | 'mined' | null> {
  if (!(await advanceMerge(ctx, op, step))) return null;
  if (await settleMerge(ctx, op, step)) return 'final';
  return step.stage === 'relayed' ? 'mined' : null;
}

/** Takes a consolidation as far as it can go now. Each merge spends the last one's note once a proved root covers it,
 * final or not: a reorg that drops the last merge takes that root back too, and the later merge then fails on chain.
 * So each merge in a block waits in `landing` until final, and one a reorg dropped is relayed again before any later
 * one; a later one whose proof the reorg left with nowhere to land (the last note moved) fails when built again. With
 * nothing left to merge the consolidation is `merged`, and done once its merges are final. `merge` and `plan` do the
 * network's part, apart only for a test. */
export async function advanceConsolidation(
  ctx: Ctx,
  op: SpendOperation,
  merge = (step: MergeStep) => driveMerge(ctx, op, step),
  plan = () => planStep(ctx, op),
): Promise<void> {
  const data = op.data;
  const drop = (m: MergeStep) => {
    if (data.step === m) data.step = null;
    else data.landing = data.landing!.filter((x) => x !== m);
  };
  // a merge that fails (`m`, in no block), or a next one that cannot be planned (a fee past `maxFee`), fails the
  // consolidation once its merges in a block are final: failed before, it would free the coins they spent, and leave
  // out what they paid
  const failing = async (e: unknown, m?: MergeStep) => {
    if (!failsOperation(e) || op.status !== 'pending') throw e;
    if (m) drop(m);
    if (stepsOf(op).length === 0) throw e;
    data.failure ??= { code: e.code, message: e.message };
    data.merged = true;
    await ctx.save();
  };
  for (;;) {
    if (op.status !== 'pending') return;
    for (const m of stepsOf(op) as MergeStep[]) {
      const now = await merge(m).catch(async (e) => (await failing(e, m), 'failed' as const));
      if (now === null || op.status !== 'pending') return;
      if (now === 'final') {
        drop(m);
        await ctx.save();
      }
    }
    if (data.merged) {
      if (stepsOf(op).length > 0) return;
      if (data.failure) fail(data.failure.code, data.failure.message);
      op.status = 'done';
      await ctx.save();
      return;
    }
    // the next merge, once a proved root covers the last one's note
    const next = await plan().catch(async (e) => (await failing(e), null));
    if (!next || op.status !== 'pending') return;
    if (next === 'done') {
      if (data.step || data.landing?.length) data.merged = true;
      else op.status = 'done';
      await ctx.save();
      return;
    }
    if (data.step) data.landing = [...(data.landing ?? []), data.step as MergeStep];
    data.step = next;
    await ctx.save();
  }
}
