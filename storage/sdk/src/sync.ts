// Incremental history. Everything is append-only or write-once, so a state remembers how far each
// list has been read and every refresh reads only past that. New records are found through the
// canister's log of lane slot ids: a refresh matches the next id of each of its lanes against the
// log's new entries, so its cost does not grow with the number of channels or receive codes.

import type { ActorSubclass } from '@icp-sdk/core/agent';
import type { Kind, Service, Slot } from './candid.js';
import type { CanisterClient } from './canister.js';
import { concat, equal, hex, kdf, open, openFrom, seal, unhex, utf8 } from './crypto.js';
import {
  type LaneKind,
  type LaneRecord,
  type Via,
  addressInbox,
  channelKey,
  channelSeed,
  codeKey,
  outgoingId,
  outgoingKey,
  ownKey,
  posKey,
  readChannel,
  readLaneRecord,
  readTarget,
  sealKey,
  slotId,
} from './formats.js';
import { type ViewKey, notifyKey, notifySecret } from './viewKey.js';
import { MAX_LOG_READ, MAX_READ } from './wire.js';

/** Slots read per sequence and round trip once a sequence has news, at first. */
const BATCH = 16;

/** One lane on one chain. */
export interface ChainLane {
  chainId: bigint;
  /** Where the next record goes: the first empty slot index (slots that do not open count too). */
  nextSlotIndex: number;
  /** What it held, in slot order. An app that keeps records of its own may empty this. */
  records: LaneRecord[];
}

/** A lane other than the own lane: one payer → receiver channel, a receive code's lane, which every payer of the code
 * writes to, or the lane of one of the owner's points of sale. */
export interface StoredLane {
  /** Outgoing: the receiver, or `null` for a code (which never names its receiver). Incoming: the payer as claimed
   * by whoever opened the channel, or `null` for a code, whose notes each claim their own, and for a point of sale;
   * it is NOT verified. */
  peer: Uint8Array | null;
  via: Via;
  /** The channel seed and its inbox; `null` for a code and a point of sale, which have neither. */
  seed: Uint8Array | null;
  inbox: Uint8Array | null;
  /** The lane key. */
  key: Uint8Array;
  /** One entry per watched chain. */
  chains: ChainLane[];
}

/** Everything one view key has seen so far. Plain data: keep it with `exportState`, and treat it as read-only. */
export interface SyncState {
  address: Uint8Array;
  /** The chains whose lanes are read. Add one and the next refresh reads it from slot 0. */
  chains: bigint[];
  addressInboxRead: number;
  /** Channels to the address, the address's own receive codes (one for each burn index in its burn blocks), and the
   * lanes of its points of sale (one for each the own lane records). */
  incoming: StoredLane[];
  outgoing: { next: number; lanes: StoredLane[] };
  /** The own lane (notes to self, burn blocks and points of sale), one entry per watched chain. */
  own: ChainLane[];
  /** How far the canister's lane log has been read; `null` until the first full read. */
  log: number | null;
}

/** A record a refresh found. */
export interface NewRecord {
  direction: 'incoming' | 'outgoing' | 'own';
  /** `null` in the own lane. */
  lane: StoredLane | null;
  /** Who is on the other side, as claimed and unverified: an incoming channel's payer, an outgoing one's receiver,
   * a note's payer in one of the owner's codes. `null` in the own lane and a point of sale's, and for a payment to a
   * code. */
  peer: Uint8Array | null;
  record: LaneRecord;
}

/** Where records come from: a channel, a receive code, a point of sale, or the own lane. */
interface Source {
  direction: NewRecord['direction'];
  kind: LaneKind;
  lane: StoredLane | null;
  chains: ChainLane[];
  key: Uint8Array;
  /** Whom a record of it is with, or `undefined` to skip it. */
  peerOf: (r: LaneRecord) => Uint8Array | null | undefined;
}

export const emptyState = (view: ViewKey, chains: bigint[]): SyncState => ({
  address: view.address,
  chains,
  addressInboxRead: 0,
  incoming: [],
  outgoing: { next: 0, lanes: [] },
  own: [],
  log: null,
});

export function checkState(view: ViewKey, state: SyncState): void {
  if (!equal(state.address, view.address)) throw new Error('the state belongs to another view key');
}

const payerOf = (r: LaneRecord): Uint8Array | null => (r.kind === 'note' ? (r.payer ?? null) : null);

/** Reads what is new since `state` and returns the extended state, plus the records it found. `state` itself is
 * left untouched, so a failed refresh loses nothing. A first sync is a refresh of `emptyState`.
 *
 * Queries only spot news: whatever is kept is read again as update calls, so a single lying replica
 * can neither plant entries nor make a cursor skip one. With nothing new it costs queries only: one
 * for outgoing records, one for the address inbox, and one for the lane log.
 *
 * A replica can still leave log entries out, which only delays those records: `full` reads every
 * lane instead (one query per 256 of them: every channel, point of sale and the own lane on every
 * watched chain, every code on its own), as the first refresh of a state does. Do that now and then, say hourly. */
export async function refresh(
  client: CanisterClient,
  view: ViewKey,
  state: SyncState,
  opts: { full?: boolean } = {},
): Promise<{ state: SyncState; added: NewRecord[] }> {
  checkState(view, state);
  const next = structuredClone(state);
  // read before anything else: writes made while this refresh runs are found by the next one
  const fromLog = opts.full || next.log === null ? null : next.log;
  const log =
    fromLog === null ? { end: Number(await client.actor.log_length()), ids: [] } : await readLog(client, fromLog);
  const news = new Set(log.ids.map((id) => hex(id)));
  const { address, seed } = view;
  const added: NewRecord[] = [];

  /** The sequences of `sources` with news: a lane found in this refresh, or a chain just watched, may hold records
   * from before the log position. */
  const due = (sources: Source[]) =>
    sources.flatMap((source) => {
      const via = source.lane?.via;
      const chainIds =
        via?.type === 'code'
          ? next.chains.filter((c) => c === ('code' in via ? via.code.chainId : via.chainId))
          : next.chains;
      return chainIds.flatMap((chainId) => {
        let chain = source.chains.find((c) => c.chainId === chainId);
        const fresh = !chain;
        if (!chain) source.chains.push((chain = { chainId, nextSlotIndex: 0, records: [] }));
        const idAt = (i: number) => slotId(source.key, chainId, i);
        const isDue = fromLog === null || fresh || news.has(hex(idAt(chain.nextSlotIndex)));
        return isDue ? [{ source, chain, next: chain.nextSlotIndex, idAt }] : [];
      });
    });
  /** Takes what `sequences` held, every filled slot counting (so that a code's payer writes past the other payers'
   * notes), and returns the records it took. */
  const take = (sequences: ReturnType<typeof due>, found: Filled[][]) =>
    sequences.flatMap(({ source, chain }, s) =>
      found[s].flatMap(({ id, slot }) => {
        const slotIndex = chain.nextSlotIndex++;
        const plain = open(sealKey(source.key), id, slot.data);
        const record = plain && readLaneRecord(source.kind, chain.chainId, slotIndex, slot.at_ns, plain);
        const peer = record && source.peerOf(record);
        if (!record || peer === undefined) return [];
        chain.records.push(record);
        added.push({ direction: source.direction, lane: source.lane, peer, record });
        return [record];
      }),
    );

  // The own lane and outgoing records past the cursors, perhaps written by another device. The own lane comes
  // first, so that the codes of a new burn block, and a new point of sale's lane, are read in this refresh.
  const own: Source = {
    direction: 'own',
    kind: 'own',
    lane: null,
    chains: next.own,
    key: ownKey(seed),
    peerOf: () => null,
  };
  const ownSequences = due([own]);
  const [ownFound, records] = await Promise.all([
    readSequences(client, { Lane: null }, ownSequences),
    readSequences(client, { Outgoing: null }, [{ next: next.outgoing.next, idAt: (i) => outgoingId(seed, i) }]),
  ]);
  // two devices may record the same index, or the same point of sale: one lane each
  const lanesHeld = new Set(next.incoming.filter((c) => c.via.type !== 'address').map((c) => hex(c.key)));
  const hold = (via: Via, key: Uint8Array) => {
    if (lanesHeld.has(hex(key))) return;
    lanesHeld.add(hex(key));
    next.incoming.push({ peer: null, via, seed: null, inbox: null, key, chains: [] });
  };
  for (const r of take(ownSequences, ownFound)) {
    if (r.kind === 'pos-lane') hold({ type: 'pos', n: r.n }, posKey(seed, r.n));
    if (r.kind !== 'burn-block') continue;
    r.salts.forEach((_, i) => {
      const index = r.first + i;
      hold({ type: 'code', chainId: r.chainId, tokenId: r.tokenId, index }, codeKey(seed, r.chainId, r.tokenId, index));
    });
  }
  for (const { id, slot } of records[0]) {
    next.outgoing.next++;
    const target = readTarget(open(outgoingKey(seed), id, slot.data) ?? new Uint8Array());
    if (!target) continue;
    if (!('address' in target)) {
      next.outgoing.lanes.push({
        peer: null,
        via: { type: 'code', code: target },
        seed: null,
        inbox: null,
        key: target.key,
        chains: [],
      });
      continue;
    }
    const inbox = addressInbox(target.address, target.notifyKey);
    const c = channelSeed(seed, address, inbox);
    const channel = {
      peer: target.address,
      via: { type: 'address' } as const,
      seed: c,
      inbox,
      key: channelKey(c, inbox, address),
      chains: [],
    };
    next.outgoing.lanes.push(channel);
  }

  // New announcements in the address inbox, once per seed. Deduplicating by payer instead would let a forged entry
  // naming a real payer hide the real channel.
  const inbox = addressInbox(address, notifyKey(view));
  const infos = await readInbox(client, inbox, next.addressInboxRead);
  next.addressInboxRead += infos.length;
  for (const info of infos) {
    const announced = readChannel(openFrom(notifySecret(view), 'announce', inbox, info) ?? new Uint8Array());
    if (!announced || next.incoming.some((channel) => channel.seed && equal(channel.seed, announced.seed))) continue;
    const { payer, seed: c } = announced;
    next.incoming.push({
      peer: payer,
      via: { type: 'address' },
      seed: c,
      inbox,
      key: channelKey(c, inbox, payer),
      chains: [],
    });
  }

  // New records in every channel and point of sale on every watched chain, and in every code on its own. Of a code's
  // lane, the owner takes every payer's notes, and a payer only its own.
  const sources: Source[] = [
    ...next.incoming.map((lane): Source => ({
      direction: 'incoming',
      kind: lane.via.type === 'address' ? 'channel' : lane.via.type,
      lane,
      chains: lane.chains,
      key: lane.key,
      peerOf: (r) => (lane.via.type === 'code' ? payerOf(r) : lane.peer),
    })),
    ...next.outgoing.lanes.map((lane): Source => ({
      direction: 'outgoing',
      kind: lane.via.type === 'code' ? 'code' : 'channel',
      lane,
      chains: lane.chains,
      key: lane.key,
      peerOf: (r) => (lane.via.type !== 'code' ? lane.peer : equal(payerOf(r)!, address) ? null : undefined),
    })),
  ];
  const sequences = due(sources);
  take(sequences, await readSequences(client, { Lane: null }, sequences));
  next.log = log.end;
  return { state: next, added };
}

/** The lane log from `start` to its end. */
async function readLog(client: CanisterClient, start: number): Promise<{ end: number; ids: Uint8Array[] }> {
  const ids: Uint8Array[] = [];
  for (;;) {
    const page = await client.actor.get_log(BigInt(start + ids.length), MAX_LOG_READ);
    ids.push(...page);
    if (page.length < MAX_LOG_READ) return { end: start + ids.length, ids };
  }
}

/** Announcements from `start` on. */
async function readInbox(client: CanisterClient, inbox: Uint8Array, start: number): Promise<Uint8Array[]> {
  const infos: Uint8Array[] = [];
  for (;;) {
    const at = start + infos.length;
    const peek = await client.actor.get_announcements(inbox, at, MAX_READ);
    if (peek.length === 0) return infos;
    const page = await client.replicated.get_announcements(inbox, at, MAX_READ);
    infos.push(...page);
    if (page.length < MAX_READ) return infos;
  }
}

interface Sequence {
  /** First slot index not read yet. */
  next: number;
  idAt: (index: number) => Uint8Array;
}

type Filled = { id: Uint8Array; slot: Slot };

/** The filled slots of each sequence from its `next` index up to the first empty one. The first round
 * checks one slot per sequence; sequences with news are then read `BATCH` slots at a time, twice as many each round
 * up to `MAX_READ`, so that a lane of hundreds of records, read on a new device, takes a few round trips. A wider read
 * costs little: the replicated read, the slow one, takes only the slots the single-replica one found filled. */
export async function readSequences(client: CanisterClient, kind: Kind, sequences: Sequence[]): Promise<Filled[][]> {
  const found: Filled[][] = sequences.map(() => []);
  let pending = sequences.map((_, s) => s);
  for (let width = 1; pending.length > 0; width = Math.min(width === 1 ? BATCH : width * 2, MAX_READ)) {
    const ids = pending.map((s) => {
      const { next, idAt } = sequences[s];
      return Array.from({ length: width }, (_, i) => idAt(next + found[s].length + i));
    });
    const peek = await getSlots(client.actor, kind, ids.flat());
    const news = ids.map((row, p) => row.slice(0, leading(peek.slice(p * width, (p + 1) * width))));
    const confirmed = await getSlots(client.replicated, kind, news.flat());
    let at = 0;
    pending = pending.filter((s, p) => {
      const slots = confirmed.slice(at, (at += news[p].length));
      const n = leading(slots);
      found[s].push(...slots.slice(0, n).map((slot, i) => ({ id: news[p][i], slot: slot! })));
      return n === width;
    });
  }
  return found;
}

/** `get_slots` in reads of at most `MAX_READ` ids. */
async function getSlots(actor: ActorSubclass<Service>, kind: Kind, ids: Uint8Array[]): Promise<(Slot | null)[]> {
  const reads = [];
  for (let i = 0; i < ids.length; i += MAX_READ) reads.push(actor.get_slots(kind, ids.slice(i, i + MAX_READ)));
  return (await Promise.all(reads)).flat().map((slot) => slot[0] ?? null);
}

/** The first empty slot of a lane's sequence from slot `from` on: where a code's first payment goes, or a point of
 * sale's next block. */
export async function sequenceEnd(
  client: CanisterClient,
  idAt: (index: number) => Uint8Array,
  from = 0,
): Promise<number> {
  return from + (await readSequences(client, { Lane: null }, [{ next: from, idAt }]))[0].length;
}

const leading = (slots: (Slot | null)[]): number => {
  const empty = slots.indexOf(null);
  return empty < 0 ? slots.length : empty;
};

const STATE_TAG = utf8('zerc20/storage/sync-state/v1');

/** `state`, encrypted under a key only `view` derives, for the app to store anywhere. */
export function exportState(view: ViewKey, state: SyncState): Uint8Array {
  checkState(view, state);
  const json = JSON.stringify(state, (_, v: unknown) =>
    typeof v === 'bigint' ? { $n: v.toString() } : v instanceof Uint8Array ? { $b: hex(v) } : v,
  );
  return seal(kdf(view.seed, 'sync-state'), concat(STATE_TAG, view.address), utf8(json));
}

/** The state `exportState` encrypted, or `null` if `bytes` is not one for `view` (start over from
 * `emptyState` then). */
export function importState(view: ViewKey, bytes: Uint8Array): SyncState | null {
  const plain = open(kdf(view.seed, 'sync-state'), concat(STATE_TAG, view.address), bytes);
  if (!plain) return null;
  return JSON.parse(new TextDecoder().decode(plain), (_, v: unknown) => {
    if (typeof v === 'object' && v !== null && '$n' in v) return BigInt(v.$n as string);
    if (typeof v === 'object' && v !== null && '$b' in v) return unhex(v.$b as string);
    return v;
  }) as SyncState;
}
