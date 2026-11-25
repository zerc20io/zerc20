// One pass of keeping up: new notes from storage, then per chain the wallet's tags and nullifiers among the
// indexer's new entries. A wallet only ever looks for what it already expects; see scan.ts.

import {
  type Deposit,
  type LaneRecord,
  type DepositArgs,
  type NewRecord,
  type Note,
  type OwnReceipt,
  type Receipt,
  type SyncState,
  burnKey,
  commit,
  emptyState,
  planBurnBlock,
  planReceipt,
  refresh,
} from '@zerc20/storage-sdk';
import { type Hex, bytesToHex, hexToBytes, numberToHex, parseAbiItem } from 'viem';
import type { Chain, Token } from './chain.js';
import { type ChainCtx, type Ctx, chainCtx, chainState, owner, refundSigner } from './context.js';
import { burnAddress, core } from './core.js';
import { type Hit, type Watch, scan } from './scan.js';
import { type Asp, type AspStatus, type Indexer, PAGE } from './servers.js';
import type { DepositAddressArgs, DepositRecord, NoteReceipt, NoteRecord, Position, Sample } from './state.js';

/** The ledger's log of each commitment, found by its index (`contracts/src/CommitmentLedger.sol`). */
const committedEvent = parseAbiItem('event Committed(uint64 indexed index, uint256[4] fields)');

const DAY_MS = 86_400_000;
/** Storage is read in full this often, in case a replica left entries out of its log. */
const FULL_REFRESH_MS = 3_600_000;
// `field0`'s high 32 bits (contracts/src/libs/Protocol.sol)
const NOTE_TAG = 0x789f26ebn;
const TRANSFER_TAG = 0xddf252adn;
/** Look at entries past the final count only this long after something was started or announced. */
export const WAIT_MS = 30 * 60_000;

const hex32 = (b: Uint8Array): Hex => bytesToHex(b);
const big = (b: Uint8Array): bigint => BigInt(hex32(b));

/** The final commitment count when the indexer last reported at or before `atMs`, so nothing announced after it
 * can be committed before it. 0 without such a sample (a restore reads from the birthday). */
export function commitmentsAt(samples: Sample[], atMs: number): number {
  let best = 0;
  for (const s of samples) if (s.atMs <= atMs) best = Math.max(best, s.commitments);
  return best;
}

/** A note's hash under the key that owns it (the wallet's, or with `keyIndex` a receive code's), and the watch for its
 * tag. Null while that key's owner is not derived. */
function watchFor(
  ctx: Ctx,
  chainId: bigint,
  tokenId: number,
  value: bigint,
  salt: Hex,
  keyIndex: number | undefined,
  from: number,
) {
  const key = owner(ctx, keyIndex === undefined ? undefined : { chainId, tokenId, index: keyIndex });
  if (!key) return null;
  const noteHash = core.noteHash(chainId, key.publicKey, `0x${value.toString(16)}`, tokenId, salt) as Hex;
  return { noteHash, watch: { key: numberToHex(core.noteTag(tokenId, noteHash), { size: 4 }), from, scannedTo: from } };
}

/** The storage state, empty until its first refresh. It watches every chain of the network, also one the network
 * gained after the state was saved: the next refresh reads that one's lanes from slot 0. */
export function storageState(ctx: Ctx): SyncState {
  const chains = ctx.chains.map((c) => c.config.chainId);
  const state = ctx.state.storage ?? emptyState(ctx.view, chains);
  const gained = chains.filter((c) => !state.chains.includes(c));
  return (ctx.state.storage = gained.length > 0 ? { ...state, chains: [...state.chains, ...gained] } : state);
}

async function syncStorage(ctx: Ctx, tokens: Map<bigint, number[]>): Promise<void> {
  const full = Date.now() - ctx.lastFullRefreshMs > FULL_REFRESH_MS;
  takeRefresh(ctx, await refresh(ctx.storage, ctx.view, storageState(ctx), { full }), tokens);
  if (full) ctx.lastFullRefreshMs = Date.now();
  await writeReceipts(ctx, tokens);
}

/** Writes each receipt storage does not hold yet to the own lane, one a batch: `planReceipt` takes the lane's next
 * slot, which a second one in the batch would take too. The refresh that follows brings it back as written. */
async function writeReceipts(ctx: Ctx, tokens: Map<bigint, number[]>): Promise<void> {
  for (const r of ctx.state.receipts.filter((r) => r.unwritten)) {
    const head = { chainId: r.chainId, tokenId: r.tokenId, burnAddress: hexToBytes(r.burnAddress) };
    const receipt: OwnReceipt =
      r.kind === 'returned'
        ? {
            ...head,
            kind: r.kind,
            index: r.index,
            recipient: hexToBytes(r.recipient),
            amount: hexToBytes(numberToHex(r.amount, { size: 32 })),
            txHash: hexToBytes(r.txHash),
          }
        : {
            ...head,
            kind: r.kind,
            depositAddress: hexToBytes(r.depositAddress),
            ...(r.args && { args: depositArgsBytes(r.args) }),
          };
    takeRefresh(
      ctx,
      await commit(ctx.storage, ctx.view, storageState(ctx), (s) => planReceipt(ctx.view, s, receipt)),
      tokens,
    );
    delete r.unwritten;
    await ctx.save();
  }
}

/** A deposit address's arguments as the wallet keeps them, from storage's. */
const depositArgs = (a: DepositArgs): DepositAddressArgs => ({
  fee: big(a.fee),
  feeRecipient: bytesToHex(a.feeRecipient),
  refundSigner: bytesToHex(a.refundSigner),
  referrer: bytesToHex(a.referrer),
  referralBps: a.referralBps,
});

/** And storage's, from the wallet's. */
const depositArgsBytes = (a: DepositAddressArgs): DepositArgs => ({
  fee: hexToBytes(numberToHex(a.fee, { size: 32 })),
  feeRecipient: hexToBytes(a.feeRecipient),
  refundSigner: hexToBytes(a.refundSigner),
  referrer: hexToBytes(a.referrer),
  referralBps: a.referralBps,
});

/** A storage receipt as the wallet keeps it. */
export const noteReceipt = (r: Receipt): NoteReceipt => ({
  kind: r.kind,
  amount: big(r.amount),
  fee: big(r.fee),
  counterparty: bytesToHex(r.counterparty),
});

/** Each chain's token ids. */
export async function tokenIds(ctx: Ctx): Promise<Map<bigint, number[]>> {
  const tokens = new Map<bigint, number[]>();
  await Promise.all(
    ctx.chains.map(async (c) =>
      tokens.set(
        c.config.chainId,
        (await c.chain.tokens()).map((t) => t.tokenId),
      ),
    ),
  );
  return tokens;
}

/** Takes a storage refresh: its state, plus what it found for this wallet: notes (to its address, its receive codes
 * and itself), deposits payers told, burn blocks recorded, deposits it paid others, and its receipts. A record is
 * announced by one refresh only, so `commit`'s refresh must come through here too: a payment to oneself, or one that
 * arrived just before, would otherwise be lost. */
export function takeRefresh(
  ctx: Ctx,
  { state, added }: { state: SyncState; added: NewRecord[] },
  tokens: Map<bigint, number[]>,
): void {
  // the wallet keeps its own records: storage's copies would only double the saved state
  for (const lane of [...state.incoming, ...state.outgoing.lanes, { chains: state.own }]) {
    for (const chain of lane.chains) chain.records = [];
  }
  ctx.state.storage = state;
  for (const a of added) {
    const r = a.record;
    // what it paid others: a note's receipt rides on its change; a deposit is watched for here
    if (a.direction === 'outgoing') {
      if (r.kind === 'deposit') takeSent(ctx, r, a.peer!, tokens);
      continue;
    }
    if (r.kind === 'deposit') takeDeposit(ctx, r, a.peer!, tokens);
    else if (r.kind === 'burn-block') takeBurnBlock(ctx, r, a.lane?.via.type === 'pos', tokens);
    else if (r.kind === 'note') upsertNote(ctx, a, r, tokens);
    else if (r.kind !== 'pos-lane') takeReceipt(ctx, r); // a point of sale's lane is read by the storage refresh
  }
}

/** A deposit this wallet paid into someone's burn address, as storage told it with the address: watched for its
 * transfer, from a day before storage held it, to show once it landed. */
function takeSent(ctx: Ctx, d: Deposit, to: Uint8Array, tokens: Map<bigint, number[]>): void {
  const { chainId, tokenId } = d;
  if (!tokens.get(chainId)?.includes(tokenId)) return;
  const address = bytesToHex(d.burnAddress);
  if (ctx.state.sent.some((s) => s.chainId === chainId && s.address === address)) return;
  const atMs = Number(d.atNs / 1_000_000n);
  const from = commitmentsAt(chainState(ctx, chainId).samples, atMs - DAY_MS);
  const watch = { key: numberToHex(core.transferTag(tokenId, address), { size: 4 }), from, scannedTo: from };
  ctx.state.sent.push({
    chainId,
    tokenId,
    address,
    to: bytesToHex(to),
    createdMs: atMs,
    watches: [{ tokenId, watch }],
    found: [],
  });
}

/** A receipt from the own lane: one this device wrote, now held by storage (dated as storage holds it, alike on every
 * device), or another device's. */
function takeReceipt(ctx: Ctx, r: OwnReceipt & { atNs: bigint }): void {
  const burnAddress = bytesToHex(r.burnAddress);
  const atMs = Number(r.atNs / 1_000_000n);
  // a return is told apart by its deposit, a deposit address by itself: one burn address can have more than one, each
  // registered with arguments of its own
  const same = ctx.state.receipts.find(
    (x) =>
      x.chainId === r.chainId &&
      x.burnAddress === burnAddress &&
      (x.kind === 'returned' && r.kind === 'returned'
        ? x.index === r.index
        : x.kind === 'deposit-address' &&
          r.kind === 'deposit-address' &&
          x.depositAddress.toLowerCase() === bytesToHex(r.depositAddress)),
  );
  // what its address was registered with, where the record tells it
  const args = r.kind === 'deposit-address' && r.args && { args: depositArgs(r.args) };
  if (same) {
    delete same.unwritten;
    same.atMs = atMs;
    Object.assign(same, args);
    return;
  }
  const head = { chainId: r.chainId, tokenId: r.tokenId, burnAddress, atMs };
  ctx.state.receipts.push(
    r.kind === 'returned'
      ? {
          ...head,
          kind: r.kind,
          index: r.index,
          recipient: bytesToHex(r.recipient),
          amount: big(r.amount),
          txHash: bytesToHex(r.txHash),
        }
      : { ...head, kind: r.kind, depositAddress: bytesToHex(r.depositAddress), ...args },
  );
}

/** A burn address of this wallet's that a payer chose and told in storage, watched as a deposit of its own once its
 * salt checks out under the wallet's key: one hash. */
export function takeDeposit(ctx: Ctx, deposit: Deposit, payer: Uint8Array, tokens: Map<bigint, number[]>): void {
  const { chainId, tokenId } = deposit;
  if (!tokens.get(chainId)?.includes(tokenId)) return;
  const salt = hex32(deposit.burnSalt);
  if (ctx.state.deposits.some((d) => d.chainId === chainId && d.salt === salt)) return;
  const address = core.burnAddressOf(chainId, owner(ctx)!.publicKey, salt) as Hex | undefined;
  if (!address) return;
  const atMs = Number(deposit.atNs / 1_000_000n);
  // storage held it before the payer's transfer; a day of margin covers clock skew
  const from = commitmentsAt(chainState(ctx, chainId).samples, atMs - DAY_MS);
  ctx.state.deposits.push({
    chainId,
    tokenId,
    burnIndex: -1,
    salt,
    address,
    createdMs: atMs,
    depositAddress: null,
    payer: hex32(payer),
    watches: [
      { tokenId, watch: { key: numberToHex(core.transferTag(tokenId, address), { size: 4 }), from, scannedTo: from } },
    ],
    found: [],
  });
}

/** Burn addresses recorded in storage, by salt: each checked to be this wallet's own, which takes one hash, and watched
 * from a day before it was recorded. A point of sale's (`pos`, from its lane) are its payment addresses, with no burn
 * index of this wallet's. This wallet's own, from another device or from before a restore, are taken as handed out:
 * none is handed out again. */
function takeBurnBlock(
  ctx: Ctx,
  b: Extract<LaneRecord, { kind: 'burn-block' }>,
  pos: boolean,
  tokens: Map<bigint, number[]>,
): void {
  if (!tokens.has(b.chainId)) return;
  const { publicKey } = owner(ctx)!;
  const atMs = Number(b.atNs / 1_000_000n);
  const from = commitmentsAt(chainState(ctx, b.chainId).samples, atMs - DAY_MS);
  b.salts.forEach((bytes, i) => {
    const salt = hex32(bytes);
    const address = core.burnAddressOf(b.chainId, publicKey, salt) as Hex | undefined;
    if (!address || ctx.state.deposits.some((d) => d.chainId === b.chainId && d.salt === salt)) return;
    const watch = { key: numberToHex(core.transferTag(b.tokenId, address), { size: 4 }), from, scannedTo: from };
    const record: DepositRecord = {
      chainId: b.chainId,
      tokenId: b.tokenId,
      burnIndex: pos ? -1 : b.first + i,
      salt,
      address,
      createdMs: atMs,
      depositAddress: null,
      watches: [{ tokenId: b.tokenId, watch }],
      found: [],
    };
    if (pos) record.managed = true;
    else record.elsewhere = true;
    ctx.state.deposits.push(record);
  });
}

/** This wallet's lowest recorded burn address of a token that it has not handed out, if any. */
export function unusedBurn(ctx: Ctx, chainId: bigint, tokenId: number): DepositRecord | undefined {
  const next = chainState(ctx, chainId).burnNext[tokenId] ?? 0;
  let best: DepositRecord | undefined;
  for (const d of ctx.state.deposits) {
    if (d.chainId !== chainId || d.tokenId !== tokenId || d.managed || d.payer || d.elsewhere || d.burnIndex < next)
      continue;
    if (!best || d.burnIndex < best.burnIndex) best = d;
  }
  return best;
}

/** The index of the next burn address of a token to record: past every one recorded, here or by another device. */
function toRecord(ctx: Ctx, chainId: bigint, tokenId: number): number {
  let index = chainState(ctx, chainId).burnNext[tokenId] ?? 0;
  for (const d of ctx.state.deposits) {
    if (d.chainId === chainId && d.tokenId === tokenId && !d.managed) index = Math.max(index, d.burnIndex + 1);
  }
  return index;
}

/** The index of the burn address of a token that is handed out next, and so of the receive code: the one recorded
 * ahead, or else the next to record. */
export const nextBurn = (ctx: Ctx, chainId: bigint, tokenId: number): number =>
  unusedBurn(ctx, chainId, tokenId)?.burnIndex ?? toRecord(ctx, chainId, tokenId);

/** Records this wallet's next burn address of a token in storage (a burn block of one), then watches it. Every device
 * of the wallet, and a restore, then watches it too and never hands it out again. About 2^16 hashes, `urgent` unless
 * it is one made ahead; needs no seed. */
export async function recordBurn(
  ctx: Ctx,
  chainId: bigint,
  tokenId: number,
  tokens: Map<bigint, number[]>,
  opts: { signal?: AbortSignal; urgent?: boolean } = {},
): Promise<DepositRecord> {
  const index = toRecord(ctx, chainId, tokenId);
  const key = burnKey(ctx.view.seed);
  const { salt, address } = await burnAddress(key, chainId, tokenId, index, owner(ctx)!.publicKey, opts);
  const { commitmentsFinal: from } = await chainCtx(ctx, chainId).indexer.status();
  const block = { chainId, tokenId, first: index, salts: [hexToBytes(salt)] };
  const result = await commit(ctx.storage, ctx.view, storageState(ctx), (s) => planBurnBlock(ctx.view, s, block));
  const record: DepositRecord = {
    chainId,
    tokenId,
    burnIndex: index,
    salt,
    address,
    createdMs: Date.now(),
    depositAddress: null,
    // watched under this token right away, and under every other token from the next sync on
    watches: [
      { tokenId, watch: { key: numberToHex(core.transferTag(tokenId, address), { size: 4 }), from, scannedTo: from } },
    ],
    found: [],
  };
  // before the refresh, which brings the block back: taken as new, it would count as handed out
  ctx.state.deposits.push(record);
  takeRefresh(ctx, result, tokens);
  await ctx.save();
  return record;
}

/** Keeps one burn address recorded ahead for each token this wallet has handed one out for, so that handing it out
 * writes nothing: a write then would mark the transfer that follows as this wallet's. A token's first one is recorded
 * as it is handed out. Reads the tokens only when one is due. */
export async function topUpBurns(ctx: Ctx, signal?: AbortSignal): Promise<void> {
  const onNetwork = new Set(ctx.chains.map((c) => c.config.chainId));
  const used = new Map(
    ctx.state.deposits
      .filter((d) => !d.managed && onNetwork.has(d.chainId))
      .map((d) => [`${d.chainId}:${d.tokenId}`, d]),
  );
  let tokens: Map<bigint, number[]> | undefined;
  for (const { chainId, tokenId } of used.values()) {
    if (!unusedBurn(ctx, chainId, tokenId))
      await recordBurn(ctx, chainId, tokenId, (tokens ??= await tokenIds(ctx)), { signal, urgent: false });
  }
}

function upsertNote(ctx: Ctx, a: NewRecord, note: Note, tokens: Map<bigint, number[]>): void {
  const { chainId, tokenId, value, noteSalt } = note.opening;
  if (!tokens.has(chainId)) return;
  const salt = hex32(noteSalt);
  const peer = a.peer && hex32(a.peer);
  const { atNs } = note;
  const existing = ctx.state.notes.find((n) => n.chainId === chainId && n.salt === salt);
  const receipt = note.receipt && noteReceipt(note.receipt);
  if (existing) {
    // recorded before storage announced it (a payment's change): keep what was found
    Object.assign(existing, { peer, atNs }, receipt && { receipt });
    return;
  }
  // a payment to one of this wallet's codes is owned by the code's key, and is in the code's token
  const via = a.lane?.via;
  const code = via?.type === 'code' && 'index' in via ? via : null;
  if (code && code.tokenId !== tokenId) return;
  const keyIndex = code?.index;
  // storage first held it before the payer committed it on chain; a day of margin covers clock skew
  const from = commitmentsAt(chainState(ctx, chainId).samples, Number(atNs / 1_000_000n) - DAY_MS);
  ctx.state.notes.push({
    chainId,
    tokenId,
    value: big(value),
    salt,
    source: a.direction === 'own' ? 'self' : 'received',
    ...(receipt && { receipt }),
    peer,
    atNs,
    ...(keyIndex === undefined ? {} : { keyIndex }),
    // storage tells of a note once: one whose key waits for the seed is kept, not dropped
    ...(watchFor(ctx, chainId, tokenId, big(value), salt, keyIndex, from) ?? {
      unkeyed: true,
      noteHash: '0x',
      watch: null,
    }),
    found: [],
  });
}

/** Receive codes of each token whose keys are derived while the seed is held, to hand out while it is not, and as many
 * deposit addresses' refund signers. */
export const CODES_AHEAD = 4;

/** With the seed held, each owner not derived yet: the wallet's own, each of its burn addresses' (a receive code each),
 * the next `CODES_AHEAD` codes' of each of `tokens` with their deposit addresses' refund signers, and each note's key's;
 * and the watch of each note that waited for its key. Without it, the watch of each note whose key was derived before. */
export function keyAll(ctx: Ctx, tokens: Token[]): void {
  owner(ctx);
  // ponytail: one derivation per own burn address as the wallet opens; keep owners in the saved state if wallets grow
  // to thousands of them
  for (const d of ctx.state.deposits) {
    if (d.burnIndex >= 0 && !d.managed) owner(ctx, { chainId: d.chainId, tokenId: d.tokenId, index: d.burnIndex });
  }
  for (const { chainId, tokenId } of tokens) {
    const next = nextBurn(ctx, chainId, tokenId);
    for (let index = next; index < next + CODES_AHEAD; index++) {
      owner(ctx, { chainId, tokenId, index });
      refundSigner(ctx, { chainId, tokenId, index });
    }
  }
  for (const n of ctx.state.notes) {
    if (n.keyIndex === undefined) continue;
    owner(ctx, { chainId: n.chainId, tokenId: n.tokenId, index: n.keyIndex });
    if (!n.unkeyed) continue;
    const from = commitmentsAt(chainState(ctx, n.chainId).samples, Number((n.atNs ?? 0n) / 1_000_000n) - DAY_MS);
    const watched = watchFor(ctx, n.chainId, n.tokenId, n.value, n.salt, n.keyIndex, from);
    if (!watched) continue; // still waits for the seed
    Object.assign(n, watched);
    delete n.unkeyed;
  }
}

/** Whether something was started or announced recently enough to look past the final count for it. */
function waiting(ctx: Ctx, chainId: bigint, now: number): boolean {
  const recent = (ms: number | null) => ms !== null && now - ms < WAIT_MS;
  return (
    ctx.state.ops.some((o) => o.chainId === chainId && o.status === 'pending' && recent(o.createdMs)) ||
    [...ctx.state.deposits, ...ctx.state.sent].some(
      (d) => d.chainId === chainId && d.found.length === 0 && recent(d.createdMs),
    ) ||
    ctx.state.notes.some(
      (n) =>
        n.chainId === chainId &&
        !n.unkeyed &&
        n.found.length === 0 &&
        n.atNs !== null &&
        recent(Number(n.atNs / 1_000_000n)),
    )
  );
}

/** One chain: new tags, deposit details, nullifiers, then the ASP's decisions. What it finds counts once it has looked
 * for its spend: until then, a note or deposit spent long ago (found again on a new device, or spent by another one)
 * would add to the balance, also where the sync fails before. */
async function syncChain(ctx: Ctx, c: ChainCtx, tokens: number[]): Promise<void> {
  const chainId = c.config.chainId;
  const s = chainState(ctx, chainId);
  const status = await c.indexer.status();
  const now = Date.now();
  const last = s.samples.at(-1);
  if (!last || status.commitmentsFinal >= last.commitments + PAGE) {
    s.samples.push({ atMs: now, commitments: status.commitmentsFinal, nullifiers: status.nullifiersFinal });
  }

  // every burn address is watched under every token, new tokens included
  for (const d of ctx.state.deposits.filter((d) => d.chainId === chainId)) {
    for (const tokenId of tokens) {
      if (d.watches.some((w) => w.tokenId === tokenId)) continue;
      const from = d.watches[0].watch.from;
      d.watches.push({
        tokenId,
        watch: { key: numberToHex(core.transferTag(tokenId, d.address), { size: 4 }), from, scannedTo: from },
      });
    }
  }

  // tags: notes, deposits, and deposits paid to others
  const notes = ctx.state.notes.filter((n) => n.chainId === chainId);
  const deposits = ctx.state.deposits.filter((d) => d.chainId === chainId);
  const sent = ctx.state.sent.filter((s) => s.chainId === chainId);
  const transfers = [...deposits, ...sent];
  const watches: Watch[] = [
    ...notes.flatMap((n) => (n.watch ? [n.watch] : [])),
    ...transfers.flatMap((d) => d.watches.map((w) => w.watch)),
  ];
  const live = waiting(ctx, chainId, now) ? status.commitments : status.commitmentsFinal;
  const hits = await scan(watches, 4, (p) => c.indexer.page('tags', p), status.commitmentsFinal, live);
  applyHits(notes, transfers, hits);
  dropReorged([...notes, ...transfers], status.commitmentsFinal);

  const fieldsAt = commitmentFields(c.indexer);
  // a note is counted once its commitment is the note it expects: a 4-byte tag matches someone else's now and then.
  // Read as soon as it is seen, so that it shows; read again once it is final (`place` clears it)
  for (const n of notes) {
    for (const f of n.found.filter((f) => !f.confirmed)) {
      const fields = await fieldsAt(f.index);
      if (!fields) continue;
      const ours =
        fields[0] === ((NOTE_TAG << 32n) | BigInt(n.tokenId)) &&
        fields[1] === BigInt(n.noteHash) &&
        fields[2] === 0n &&
        fields[3] === 0n;
      if (ours) f.confirmed = true;
      else n.found.splice(n.found.indexOf(f), 1);
    }
    // a note's hash is unique (its payer chose a fresh salt): once confirmed where no reorg moves it, stop watching for it
    if (n.found.some((f) => f.confirmed && !f.tentative)) n.watch = null;
  }
  await readTransfers(fieldsAt, transfers);
  // each one's block time, read with the page of commitments just read, so it tells the indexer nothing more
  const timeAt = commitmentTimes(c.indexer);
  for (const f of [...notes.flatMap((r) => r.found), ...transfers.flatMap((r) => r.found)])
    f.atMs ??= (await timeAt(f.index)) ?? undefined;

  // nullifiers of everything final and unspent
  const nullifierFrom = nullifiersBefore(c.indexer);
  // a zero-value change is never spent: it carries its payment's receipt
  const owned = [
    ...notes
      .filter((n) => n.value > 0n)
      .flatMap((n) =>
        n.found.map((f) => ({
          f,
          code: n.keyIndex === undefined ? undefined : { chainId, tokenId: n.tokenId, index: n.keyIndex },
        })),
      ),
    ...deposits.flatMap((d) => d.found.map((f) => ({ f, code: undefined }))),
  ].filter(({ f }) => !f.tentative && !f.spent);
  for (const { f, code } of owned) {
    const key = owner(ctx, code);
    if (f.nullifier || !key) continue; // without its owner: looked for once the seed is held
    const nullifier = core.nullifier(chainId, BigInt(f.index), key.nullifyingKey);
    const from = await nullifierFrom(f.index);
    f.nullifier = { key: nullifier.slice(0, 18) as Hex, from, scannedTo: from };
  }
  const nullifierWatches = owned.flatMap(({ f }) => (f.nullifier ? [f.nullifier] : []));
  const spent = await scan(
    nullifierWatches,
    8,
    (p) => c.indexer.page('nullifiers', p),
    status.nullifiersFinal,
    live === status.commitments ? status.nullifiers : status.nullifiersFinal,
  );
  applySpends(
    [...notes, ...deposits].flatMap((r): Position[] => r.found),
    spent,
  );
  for (const r of [...notes, ...transfers]) for (const f of r.found) delete f.unchecked;

  // last, as an ASP that does not answer holds back only its decisions
  const asp = await readDecisions(c.asp, deposits);
  // only a hint for the app: it holds back nothing
  if (asp) await estimateDecisions(c, status.finalBlock, asp.delaySecs, deposits).catch(() => {});
}

/** Records nullifier hits on the positions they spend: a final one spends it, one past the final count marks it
 * `nullifiedAt`, until the final nullifiers pass that place without it (a reorg dropped that JoinSplit, which shows up
 * again where it went). Every device sees an input gone once its JoinSplit is in a block, as the one that sent it does. */
export function applySpends(positions: Position[], hits: Hit[]): void {
  const byNullifier = new Map(positions.filter((f) => f.nullifier).map((f) => [f.nullifier!.key, f]));
  for (const hit of hits) {
    const f = byNullifier.get(hit.key);
    if (!f) continue;
    if (hit.tentative) f.nullifiedAt = hit.position;
    else f.spent = true;
  }
  for (const f of positions) {
    // a spent position needs no more watching
    if (f.spent) {
      delete f.nullifier;
      delete f.nullifiedAt;
    } else if (f.nullifier && f.nullifiedAt !== undefined && f.nullifiedAt < f.nullifier.scannedTo) {
      delete f.nullifiedAt;
    }
  }
}

/** How many nullifiers sit in blocks before the one where the page of commitments holding an index begins, from its
 * page of marks, each page once per reader: no spend of the commitment at that index comes before them. */
export function nullifiersBefore(indexer: Indexer): (index: number) => Promise<number> {
  const pages = new Map<number, Promise<Uint8Array>>();
  return async (index) => {
    const commitmentPage = Math.floor(index / PAGE);
    const p = Math.floor(commitmentPage / PAGE);
    let page = pages.get(p);
    if (!page) pages.set(p, (page = indexer.page('marks', p)));
    const bytes = await page;
    const at = (commitmentPage % PAGE) * 16 + 8;
    return at + 8 <= bytes.length ? Number(new DataView(bytes.buffer, bytes.byteOffset).getBigUint64(at, false)) : 0;
  };
}

/** The four fields of the commitment at an index, read from its page of commitments, each page once per reader: `null`
 * until the page is served that far. */
export function commitmentFields(indexer: Indexer): (index: number) => Promise<bigint[] | null> {
  const pages = new Map<number, Promise<Uint8Array>>();
  return async (index) => {
    const chunk = Math.floor(index / PAGE);
    let page = pages.get(chunk);
    if (!page) pages.set(chunk, (page = indexer.commitments(chunk).then((p) => p.entries)));
    const entries = await page;
    const at = (index % PAGE) * 128;
    if (entries.length < at + 128) return null; // not served yet
    return [0, 1, 2, 3].map((f) => BigInt(bytesToHex(entries.subarray(at + 32 * f, at + 32 * (f + 1)))));
  };
}

/** The block time (ms) of the commitment at an index, from its page of times, each page once per reader: `null` until
 * the page is served that far, or when it cannot be read. */
export function commitmentTimes(indexer: Indexer): (index: number) => Promise<number | null> {
  const pages = new Map<number, Promise<Uint8Array | null>>();
  return async (index) => {
    const p = Math.floor(index / PAGE);
    let page = pages.get(p);
    if (!page) pages.set(p, (page = indexer.page('times', p).catch(() => null)));
    const bytes = await page;
    const at = (index % PAGE) * 8;
    if (!bytes || bytes.length < at + 8) return null;
    return Number(new DataView(bytes.buffer, bytes.byteOffset).getBigUint64(at, false)) * 1000;
  };
}

/** Burn addresses and what was found paid to them: a wallet's deposits, or a point of sale's sales. */
type Watched = Pick<DepositRecord, 'address' | 'watches' | 'found'>;

/** The transaction that committed `index`: the ledger's log of it, in the block the indexer names. Null while the
 * indexer does not serve that block yet; its hash null while the chain's RPC does not show the log. */
export async function commitmentTx(
  chain: Chain,
  indexer: Indexer,
  index: number,
): Promise<{ hash: Hex | null; block: bigint } | null> {
  const blocks = await indexer.page('blocks', Math.floor(index / PAGE));
  const at = (index % PAGE) * 8;
  if (blocks.length < at + 8) return null;
  const block = BigInt(bytesToHex(blocks.subarray(at, at + 8)));
  const [log] = await chain.client.getLogs({
    address: await chain.ledger(),
    event: committedEvent,
    args: { index: BigInt(index) },
    fromBlock: block,
    toBlock: block,
  });
  return { hash: log?.transactionHash ?? null, block };
}

/** Each deposit's sender and amount, read as soon as it is seen, so that it shows; read again once it is final (`place`
 * clears them), since a reorg may still move what sits at a position until then. A tag collision is dropped. */
export async function readTransfers(
  fieldsAt: (index: number) => Promise<bigint[] | null>,
  deposits: Watched[],
): Promise<void> {
  for (const d of deposits) {
    for (const f of d.found.filter((f) => f.amount === null)) {
      const fields = await fieldsAt(f.index);
      if (!fields) continue;
      if (fields[0] !== ((TRANSFER_TAG << 32n) | BigInt(f.tokenId)) || fields[2] !== BigInt(d.address)) {
        d.found.splice(d.found.indexOf(f), 1);
        continue;
      }
      f.sender = numberToHex(fields[1], { size: 20 });
      f.amount = fields[3]!;
    }
  }
}

/** The ASP's decisions on deposits it has not decided yet: it decides only final ones. Returns the ASP's status, if it
 * was read. */
export async function readDecisions(asp: Asp, deposits: Watched[]): Promise<AspStatus | null> {
  const undecided = deposits.flatMap((d) => d.found).filter((f) => !f.spent && f.asp === null);
  if (undecided.length === 0) return null;
  const status = await asp.status();
  const bitmaps = new Map<number, Uint8Array>();
  for (const f of undecided.filter((f) => f.index < status.decided)) {
    const chunk = Math.floor(f.index / PAGE);
    if (!bitmaps.has(chunk)) bitmaps.set(chunk, await asp.bitmap(chunk));
    const j = f.index % PAGE;
    f.asp = (bitmaps.get(chunk)![j >> 3] >> (j & 7)) & 1 ? 'approved' : 'rejected';
  }
  return status;
}

/** When the ASP should decide each deposit it has not: once its block is final and `delaySecs` old. Taken from block
 * numbers, the latest block and the final one, so that no server is asked about a block of this wallet's. */
async function estimateDecisions(
  c: ChainCtx,
  finalBlock: number | null,
  delaySecs: number,
  deposits: Watched[],
): Promise<void> {
  const undecided = deposits.flatMap((d) => d.found).filter((f) => !f.spent && f.asp === null);
  if (undecided.length === 0 || finalBlock === null) return;
  const [latest, final] = await Promise.all([
    c.chain.client.getBlock(),
    c.chain.client.getBlock({ blockNumber: BigInt(finalBlock) }),
  ]);
  const at = (b: typeof latest) => ({ number: Number(b.number), timestamp: Number(b.timestamp) });
  const pages = new Map<number, Uint8Array>();
  for (const f of undecided) {
    const p = Math.floor(f.index / PAGE);
    if (!pages.has(p)) pages.set(p, await c.indexer.page('blocks', p));
    const page = pages.get(p)!;
    const o = (f.index % PAGE) * 8;
    if (page.length < o + 8) continue; // not served yet
    const block = Number(new DataView(page.buffer, page.byteOffset).getBigUint64(o, false));
    f.decidedByMs = decisionEstimate(block, at(latest), at(final), delaySecs) ?? f.decidedByMs;
  }
}

/** When a deposit in `block` should be decided (ms), with blocks taken to come evenly from the final block to the
 * latest, and to become final as late after their time as the final one has: null where no block came in between. */
export function decisionEstimate(
  block: number,
  latest: { number: number; timestamp: number },
  final: { number: number; timestamp: number },
  delaySecs: number,
): number | null {
  const blocks = latest.number - final.number;
  if (blocks <= 0) return null;
  const lag = latest.timestamp - final.timestamp;
  const time = latest.timestamp - ((latest.number - block) * lag) / blocks;
  return (time + Math.max(delaySecs, lag)) * 1000;
}

/** Records tag hits on the notes and deposits they belong to, through one map from key to owners: a restore can
 * bring thousands of hits for thousands of notes. */
export function applyHits(
  notes: NoteRecord[],
  deposits: Pick<DepositRecord, 'watches' | 'found'>[],
  hits: Hit[],
): void {
  type Owner = { note: NoteRecord } | { deposit: Pick<DepositRecord, 'found'>; tokenId: number };
  const owners = new Map<string, Owner[]>();
  const add = (key: string, o: Owner) => {
    const list = owners.get(key);
    if (list) list.push(o);
    else owners.set(key, [o]);
  };
  for (const n of notes) if (n.watch) add(n.watch.key, { note: n });
  for (const d of deposits) for (const w of d.watches) add(w.watch.key, { deposit: d, tokenId: w.tokenId });
  for (const hit of hits) {
    for (const o of owners.get(hit.key) ?? []) {
      const at = { index: hit.position, tentative: hit.tentative, spent: false };
      if ('note' in o) place(o.note.found, { ...at, confirmed: false });
      else place(o.deposit.found, { ...at, tokenId: o.tokenId, sender: null, amount: null, asp: null });
    }
  }
}

/** Records a found position once, `unchecked` until the sync that found it has looked for its spend. A later final
 * sighting replaces a tentative one, with whatever was read of it (a reorg may have moved what sat there, and to another
 * block), but not that this wallet spent it, nor whether that was looked for. */
function place<T extends { index: number; tentative: boolean; spent: boolean; atMs?: number; unchecked?: true }>(
  found: T[],
  hit: T,
): void {
  const same = found.find((f) => f.index === hit.index);
  if (!same) found.push({ ...hit, unchecked: true });
  else if (same.tentative && !hit.tentative) {
    Object.assign(same, hit, { spent: same.spent });
    delete same.atMs;
  }
}

/** Drops each position seen before it was final that the final count has passed without finding it there: a reorg took
 * it away (it shows up again where it went). The final scan covers every tentative position's index, as its watch is
 * kept until the position is final. */
export function dropReorged(records: { found: { index: number; tentative: boolean }[] }[], finalCount: number): void {
  for (const r of records) r.found = r.found.filter((f) => !f.tentative || f.index >= finalCount);
}

/** Everything new since the last sync, then saved. A chain or storage that fails holds back only itself: the rest go
 * on, and its error is returned. */
export async function syncAll(ctx: Ctx): Promise<unknown[]> {
  const errors: unknown[] = [];
  const kept = <T>(p: Promise<T>): Promise<T | null> => p.catch((e: unknown) => (errors.push(e), null));
  const listed = await Promise.all(
    ctx.chains.map((c) =>
      kept(
        c.chain.tokens().then((ts) => {
          chainState(ctx, c.config.chainId).tokens = ts;
          return [c.config.chainId, ts.map((t) => t.tokenId)] as const;
        }),
      ),
    ),
  );
  const tokens = new Map(listed.filter((l) => l !== null));
  // storage announces a record once, and a refresh drops one of a chain or token it is not given: only with them all
  if (tokens.size === ctx.chains.length) await kept(syncStorage(ctx, tokens));
  // side by side: each changes only its own chain's records. Every one settles before the next sync can start
  await Promise.all(
    ctx.chains
      .filter((c) => tokens.has(c.config.chainId))
      .map((c) => kept(syncChain(ctx, c, tokens.get(c.config.chainId)!))),
  );
  await ctx.save();
  return errors;
}
