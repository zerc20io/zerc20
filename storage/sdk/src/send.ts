// Planning payments, deposits, notes to self, burn blocks and points of sale from a synced state, and submitting them.
// A point of sale writes its own lane with its key alone (`writePosBlocks`).
//
// Write the note here first, then create the on-chain note with the same opening: a note that exists
// only on chain cannot be found. Receivers match notes one-to-one to on-chain leaves (by
// `commitment_index`) and treat the unmatched as pending.

import type { Action } from './candid.js';
import { type CanisterClient, StorageError } from './canister.js';
import { equal, seal, sealTo } from './crypto.js';
import {
  type BurnBlock,
  type NoteOpening,
  type OwnReceipt,
  type Receipt,
  type ReceiveCode,
  burnBlockPlaintext,
  channelKey,
  channelPlaintext,
  channelSeed,
  depositPlaintext,
  notePlaintext,
  outgoingId,
  outgoingKey,
  ownKey,
  ownReceiptPlaintext,
  posLanePlaintext,
  sealKey,
  slotId,
  targetPlaintext,
} from './formats.js';
import { type ChainLane, type NewRecord, type SyncState, checkState, refresh, sequenceEnd } from './sync.js';
import type { Recipient, ViewKey } from './viewKey.js';

/** The record at `slotIndex` of the lane of `laneKey` on `chainId`. */
function put(laneKey: Uint8Array, chainId: bigint, slotIndex: number, plaintext: Uint8Array): Action {
  const id = slotId(laneKey, chainId, slotIndex);
  return { Put: { kind: { Lane: null }, id, data: seal(sealKey(laneKey), id, plaintext) } };
}

/** The next free slot of a lane `state` has read, which must be on a watched chain. */
function nextSlotIndex(state: SyncState, chains: ChainLane[] | undefined, chainId: bigint): number {
  if (!state.chains.includes(chainId)) throw new Error(`watch chain ${chainId} and refresh first`);
  return chains?.find((c) => c.chainId === chainId)?.nextSlotIndex ?? 0;
}

function plaintextOf(plain: Uint8Array | null): Uint8Array {
  if (!plain) throw new Error('out of range: value ≥ 2^248 or salt ≥ Fr');
  return plain;
}

/** A record for `recipient` on `chainId`, through the channel to it, which is opened first if there is none yet. */
function toAddress(
  view: ViewKey,
  state: SyncState,
  recipient: Recipient,
  chainId: bigint,
  plaintext: Uint8Array,
): Action[] {
  checkState(view, state);
  const actions: Action[] = [];
  const { inbox } = recipient;
  const channel = state.outgoing.lanes.find((c) => c.inbox && equal(c.inbox, inbox));
  let key = channel?.key;
  if (!key) {
    // first contact: announce `payer ‖ seed` to the receiver, and record the channel for the payer
    const c = channelSeed(view.seed, view.address, inbox);
    const enc_announcement = sealTo(recipient.notifyKey, 'announce', inbox, channelPlaintext(view.address, c));
    if (!enc_announcement) throw new Error('low-order notify key');
    const outgoing_id = outgoingId(view.seed, state.outgoing.next);
    const target = { address: recipient.address, notifyKey: recipient.notifyKey };
    const enc_outgoing = seal(outgoingKey(view.seed), outgoing_id, targetPlaintext(target));
    actions.push({ OpenChannel: { inbox, enc_announcement, outgoing_id, enc_outgoing } });
    key = channelKey(c, inbox, view.address);
  }
  actions.push(put(key, chainId, nextSlotIndex(state, channel?.chains, chainId), plaintext));
  return actions;
}

/** A note with `opening` (what the on-chain note commits to) for `recipient`, as `lookupRecipient` found it. The
 * on-chain note must be owned by `recipient.publicKey`. */
export function planSend(view: ViewKey, state: SyncState, recipient: Recipient, opening: NoteOpening): Action[] {
  return toAddress(view, state, recipient, opening.chainId, plaintextOf(notePlaintext(opening)));
}

/** Tells `recipient` of a deposit of `value` of `tokenId` on `chainId` into its burn address of `burnSalt`, under
 * `recipient.publicKey`, which the payer then pays by a plain transfer. */
export function planDeposit(
  view: ViewKey,
  state: SyncState,
  recipient: Recipient,
  deposit: { chainId: bigint; tokenId: number; value: Uint8Array; burnSalt: Uint8Array; burnAddress: Uint8Array },
): Action[] {
  const plaintext = plaintextOf(
    depositPlaintext(deposit.tokenId, deposit.value, deposit.burnSalt, deposit.burnAddress),
  );
  return toAddress(view, state, recipient, deposit.chainId, plaintext);
}

/** A note with `opening` paying `code`; the on-chain note must be owned by `code.publicKey`. Every payer of the code
 * writes to its one lane, naming itself: the first payment records the code for the payer's history and looks for
 * the lane's end, later ones take it from `state`. Another payer writing first makes the submit `Occupied`, which
 * `commit` plans again. */
export async function planPayCode(
  client: CanisterClient,
  view: ViewKey,
  state: SyncState,
  code: ReceiveCode,
  opening: NoteOpening,
): Promise<Action[]> {
  if (opening.chainId !== code.chainId || opening.tokenId !== code.tokenId)
    throw new Error("the note is not for the code's chain and token");
  const plaintext = plaintextOf(notePlaintext(opening, { payer: view.address }));
  checkState(view, state);
  const { chainId, key } = code;
  const lane = state.outgoing.lanes.find((c) => equal(c.key, key));
  if (lane) return [put(key, chainId, nextSlotIndex(state, lane.chains, chainId), plaintext)];
  nextSlotIndex(state, undefined, chainId); // a watched chain
  const id = outgoingId(view.seed, state.outgoing.next);
  const record = seal(outgoingKey(view.seed), id, targetPlaintext(code));
  const end = await sequenceEnd(client, (i) => slotId(key, chainId, i));
  return [{ Put: { kind: { Outgoing: null }, id, data: record } }, put(key, chainId, end, plaintext)];
}

/** A note to self in the own lane, which only the owner reads: the output of a merge, or the change of a payment.
 * Put a payment's change in the payment's batch, so both are written or neither:
 * `[...planSend(..), ...planSelf(..)]`. `receipt` says what the payment or merge was, for the owner's other devices; a
 * zero-value change is unspendable, and worth writing only to carry it. */
export function planSelf(view: ViewKey, state: SyncState, opening: NoteOpening, receipt: Receipt): Action[] {
  checkState(view, state);
  const plaintext = plaintextOf(notePlaintext(opening, { receipt }));
  return [put(ownKey(view.seed), opening.chainId, nextSlotIndex(state, state.own, opening.chainId), plaintext)];
}

/** What the owner did that leaves no note to self (a rage exit, a deposit address registered), in the own lane. */
export function planReceipt(view: ViewKey, state: SyncState, receipt: OwnReceipt): Action[] {
  checkState(view, state);
  return [
    put(
      ownKey(view.seed),
      receipt.chainId,
      nextSlotIndex(state, state.own, receipt.chainId),
      ownReceiptPlaintext(receipt),
    ),
  ];
}

/** The record of `block` in the own lane, to submit before handing out any of its burn addresses, so that every
 * device of the owner watches them. Record blocks ahead of need, not as an address is handed out: the time of the
 * write would otherwise mark the first payment to it. */
export function planBurnBlock(view: ViewKey, state: SyncState, block: BurnBlock): Action[] {
  checkState(view, state);
  return [
    put(ownKey(view.seed), block.chainId, nextSlotIndex(state, state.own, block.chainId), burnBlockPlaintext(block)),
  ];
}

/** The number the owner's next point of sale takes: one past the highest the own lane records. */
export const nextPosLane = (state: SyncState): number =>
  1 + Math.max(-1, ...state.incoming.map((c) => (c.via.type === 'pos' ? c.via.n : -1)));

/** The record of point of sale `n` in the own lane, so that every device of the owner reads its lane (`posKey`). Plan
 * it with `n = nextPosLane(state)` inside `commit`'s plan: after `Occupied`, another device took that number. */
export function planPosLane(view: ViewKey, state: SyncState, chainId: bigint, n: number): Action[] {
  checkState(view, state);
  return [put(ownKey(view.seed), chainId, nextSlotIndex(state, state.own, chainId), posLanePlaintext(n))];
}

/** The most burn blocks one `writePosBlocks` takes: the canister's actions per batch. */
export const MAX_POS_BLOCKS = 16;

/** Writes `blocks`, all of one chain, to the lane of `laneKey`, as the point of sale that alone holds the key, in one
 * batch at the lane's first empty slots from `from` on; returns the slot after the last. A batch is written whole or
 * not at all, and from the first empty slot, so the lane's filled slots stay a run from 0 that readers read to its end:
 * a batch that finds a slot taken found the first, and tries again past it. The same salts written twice are found
 * once. */
export async function writePosBlocks(
  client: CanisterClient,
  laneKey: Uint8Array,
  blocks: BurnBlock[],
  from = 0,
): Promise<number> {
  const chainId = blocks[0]?.chainId;
  if (chainId === undefined || blocks.length > MAX_POS_BLOCKS || blocks.some((b) => b.chainId !== chainId))
    throw new Error(`1 to ${MAX_POS_BLOCKS} burn blocks, all of one chain`);
  const plaintexts = blocks.map(burnBlockPlaintext);
  for (;;) {
    const at = await sequenceEnd(client, (i) => slotId(laneKey, chainId, i), from);
    try {
      await submit(
        client,
        plaintexts.map((p, i) => put(laneKey, chainId, at + i, p)),
      );
      return at + blocks.length;
    } catch (e) {
      if (!(e instanceof StorageError && e.occupied)) throw e;
      from = at + 1;
    }
  }
}

/** Submits the actions `plan` builds from `state`, then refreshes; continue from the returned state,
 * or the next plan reuses a slot that is taken. After `Occupied` (another device wrote there first)
 * it refreshes and plans once more. Calls that fail without an answer are retried with the same
 * actions, which is safe: writes are write-once and batches atomic. */
export async function commit<T extends Action[]>(
  client: CanisterClient,
  view: ViewKey,
  state: SyncState,
  plan: (state: SyncState) => T | Promise<T>,
): Promise<{ planned: T; state: SyncState; added: NewRecord[] }> {
  let planned = await plan(state);
  // a record is announced by one refresh only: keep what the one between the attempts announced too
  let added: NewRecord[] = [];
  try {
    await submit(client, planned);
  } catch (e) {
    if (!(e instanceof StorageError && e.occupied)) throw e;
    ({ state, added } = await refresh(client, view, state));
    planned = await plan(state);
    await submit(client, planned);
  }
  const last = await refresh(client, view, state);
  return { planned, state: last.state, added: [...added, ...last.added] };
}

async function submit(client: CanisterClient, actions: Action[]): Promise<void> {
  for (let attempt = 1; ; attempt++) {
    try {
      return await client.submit(actions);
    } catch (e) {
      if (e instanceof StorageError || attempt === 3) throw e;
    }
  }
}
