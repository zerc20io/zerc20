// End-to-end flows against the real canister and real vetKD keys (for audits) in PocketIC, through
// the SDK as an app would use it. Each test walks through one user-facing story; rejected requests are covered by
// the canister's unit tests instead, but for what only a real call has: the ingress the canister refuses before any
// method runs, and the caller an audit comes from.
//
// Build the wasm first: cargo build --release --target wasm32-unknown-unknown -p zerc20_storage

import type { PocketIc } from '@dfinity/pic';
import { TransportSecretKey } from '@dfinity/vetkeys';
import { HttpAgent } from '@icp-sdk/core/agent';
import { IDL } from '@icp-sdk/core/candid';
import { Ed25519KeyIdentity } from '@icp-sdk/core/identity';
import type { Principal } from '@icp-sdk/core/principal';
import { afterAll, beforeAll, beforeEach, expect, inject, test, vi } from 'vitest';
import { CanisterClient, unwrap } from '../../src/canister.js';
import { concat, hex, randomBytes, readU64, u64be } from '../../src/crypto.js';
import { type LaneRecord, type NoteOpening, type Receipt, codeKey, passkeySeedId, posKey } from '../../src/formats.js';
import { fetchPasskeySeed, storePasskeySeed } from '../../src/passkey.js';
import {
  commit,
  nextPosLane,
  planBurnBlock,
  planDeposit,
  planPayCode,
  planPosLane,
  planSelf,
  planSend,
  writePosBlocks,
} from '../../src/send.js';
import {
  type NewRecord,
  type StoredLane,
  type SyncState,
  emptyState,
  exportState,
  importState,
  refresh,
} from '../../src/sync.js';
import {
  type ViewKey,
  lookupRecipient,
  notifyKey,
  openEscrow,
  register,
  registeredViewKey,
  viewKey,
} from '../../src/viewKey.js';
import { createPic } from '../pocket-ic.js';
import { wallet } from '../wallet.js';

const WASM = new URL('../../../target/wasm32-unknown-unknown/release/zerc20_storage.wasm', import.meta.url).pathname;
const InitArgs = IDL.Record({ auditor: IDL.Principal, vetkd_key_name: IDL.Text });
/** The chains the receivers watch. */
const CHAINS = [1n, 10n];
const TOKEN = 7;
const [alice, bob, mallory] = [wallet(1), wallet(2), wallet(3)];
/** The auditor: a user principal here, standing in for the Orbit station that calls the canister on mainnet. */
const auditor = Ed25519KeyIdentity.generate();

let pic: PocketIc;
let host: string;
let agent: HttpAgent;
let canisterId: Principal;
let client: CanisterClient;

beforeAll(async () => {
  pic = await createPic(inject('picUrl'));
  // Live, so the clock follows wall time and signed expiries check against it.
  host = `http://127.0.0.1:${await pic.makeLive()}`;
  agent = await HttpAgent.create({ host, shouldFetchRootKey: true });
});

afterAll(() => pic?.tearDown());

/** A freshly installed canister for every test. */
beforeEach(async () => {
  const [subnet] = await pic.getApplicationSubnets();
  canisterId = await pic.createCanister({ targetSubnetId: subnet!.id });
  const arg = IDL.encode([InitArgs], [{ auditor: auditor.getPrincipal(), vetkd_key_name: 'test_key_1' }]);
  await pic.installCode({ canisterId, wasm: WASM, arg });
  client = new CanisterClient(agent, canisterId);
});

type Wallet = ReturnType<typeof wallet>;

/** A made-up zERC20 public key of a root seed: a zero top byte keeps it below Fr. */
const publicKeyOf = (rootSeed: Uint8Array) => concat(new Uint8Array(1), rootSeed.subarray(1));

/** `w`'s view key, registered as a wallet does when it opens. */
const key = (w: Wallet): Promise<ViewKey> =>
  registeredViewKey(client, w.rootSeed, w.sign, w.address, publicKeyOf(w.rootSeed));

const sync = async (view: ViewKey, state = emptyState(view, CHAINS)) => (await refresh(client, view, state)).state;

const big = (value: bigint) => concat(new Uint8Array(24), u64be(value));
const valueOf = (r: LaneRecord) =>
  readU64(r.kind === 'note' ? r.opening.value : r.kind === 'deposit' ? r.value : new Uint8Array(32), 24);

/** The opening of an on-chain note, with a fresh salt below `Fr`. */
const opening = (chainId: bigint, value: bigint): NoteOpening => ({
  chainId,
  tokenId: TOKEN,
  value: big(value),
  noteSalt: concat(new Uint8Array(1), randomBytes(31)), // a zero top byte keeps it below Fr
});

/** What a note to self is the change or the output of, with no fee. */
const receipt = (kind: Receipt['kind'], amount: bigint, counterparty: Uint8Array): Receipt => ({
  kind,
  amount: big(amount),
  fee: big(0n),
  counterparty,
});

/** A burn block on chain 1 of two burn indices from `first`, with made-up salts. */
const block = (first: number) => ({ chainId: 1n, tokenId: TOKEN, first, salts: [randomBytes(32), randomBytes(32)] });

/** Looks `to` up and pays it from a freshly synced state, as a new device would. */
async function pay(from: ViewKey, to: Uint8Array, chainId: bigint, value: bigint) {
  const recipient = await lookupRecipient(client, to);
  if (!recipient) throw new Error('not registered');
  const state = await sync(from, emptyState(from, [chainId]));
  await commit(client, from, state, (s) => planSend(from, s, recipient, opening(chainId, value)));
}

/** Each channel as [peer, via, [chainId, value][]], records in order. */
const summary = (lanes: StoredLane[]) =>
  lanes.map((c) => [c.peer, c.via, c.chains.flatMap((chain) => chain.records.map((r) => [chain.chainId, valueOf(r)]))]);

/** New records as [direction, kind, value]. */
const values = (added: NewRecord[]) => added.map((a) => [a.direction, a.record.kind, valueOf(a.record)]);

const received = async (view: ViewKey) => summary((await sync(view)).incoming);
const sent = async (view: ViewKey) => summary((await sync(view)).outgoing.lanes);

test('both sides see address payments', async () => {
  const [aliceKey, bobKey] = [await key(alice), await key(bob)];

  // Payers find Bob's public key in his registration, signed by his wallet. Mallory never opened a wallet, so
  // there is none for her.
  expect((await lookupRecipient(client, bob.address))?.publicKey).toEqual(publicKeyOf(bob.rootSeed));
  expect(await lookupRecipient(client, mallory.address)).toBeNull();

  // Alice pays Bob on two chains, plus once on a chain he does not watch.
  await pay(aliceKey, bob.address, 1n, 100n);
  await pay(aliceKey, bob.address, 1n, 200n);
  await pay(aliceKey, bob.address, 10n, 7n);
  await pay(aliceKey, bob.address, 99n, 1n);

  // Bob finds the notes on the chains he watches, and Alice recovers the same history from her view
  // key alone. Chain 99 shows up once watched.
  const notes = [
    [1n, 100n],
    [1n, 200n],
    [10n, 7n],
  ];
  expect(await received(bobKey)).toEqual([[alice.address, { type: 'address' }, notes]]);
  expect(await sent(aliceKey)).toEqual([[bob.address, { type: 'address' }, notes]]);
  const on99 = await sync(bobKey, emptyState(bobKey, [99n]));
  expect(summary(on99.incoming)[0]![2]).toEqual([[99n, 1n]]);

  // Each chain has its own slot sequence; a note keeps its storage time.
  const [chain1, chain10] = (await sync(bobKey)).incoming[0]!.chains.map((c) => c.records);
  expect([chain1![0]!.slotIndex, chain1![1]!.slotIndex, chain10![0]!.slotIndex]).toEqual([0, 1, 0]);
  expect(0n < chain1![0]!.atNs && chain1![0]!.atNs <= chain1![1]!.atNs).toBe(true);

  // A new device with Bob's root seed gets his view key back with no signature. Another root seed cannot take
  // his registration over without registering anew.
  const sign = vi.spyOn(bob, 'sign');
  expect((await key(bob)).seed).toEqual(bobKey.seed);
  expect(sign.mock.calls.length).toBe(0);
  await expect(
    registeredViewKey(client, alice.rootSeed, bob.sign, bob.address, publicKeyOf(alice.rootSeed)),
  ).rejects.toThrow('another root seed');
});

test('a payer tells a deposit in its channel', async () => {
  const [aliceKey, bobKey] = [await key(alice), await key(bob)];
  const toBob = (await lookupRecipient(client, bob.address))!;
  const deposit = {
    chainId: 1n,
    tokenId: TOKEN,
    value: big(30n),
    burnSalt: concat(new Uint8Array(1), randomBytes(31)),
    burnAddress: randomBytes(20),
  };
  await commit(client, aliceKey, await sync(aliceKey), (s) => planDeposit(aliceKey, s, toBob, deposit));
  const [found] = (await refresh(client, bobKey, emptyState(bobKey, CHAINS))).added;
  expect(found).toMatchObject({
    direction: 'incoming',
    peer: alice.address,
    record: { kind: 'deposit', burnSalt: deposit.burnSalt, burnAddress: deposit.burnAddress },
  });
});

test('a forged payer cannot hide the real one', async () => {
  const [aliceKey, bobKey] = [await key(alice), await key(bob)];

  // Payers are not verified, so Mallory can open a channel to Bob in Alice's name.
  const asAlice = viewKey(mallory.rootSeed, alice.address, client.canisterId);
  await pay(asAlice, bob.address, 1n, 1_000_000n);
  await pay(aliceKey, bob.address, 1n, 100n);

  // Bob sees two channels claiming to be Alice: the forgery does not replace the real one.
  const fromAlice = (value: bigint) => [alice.address, { type: 'address' }, [[1n, value]]];
  expect(await received(bobKey)).toEqual([fromAlice(1_000_000n), fromAlice(100n)]);
});

test('every payer of a code writes to its lane', async () => {
  const [aliceKey, bobKey, malloryKey] = [await key(alice), await key(bob), await key(mallory)];

  // Bob's wallet records burn blocks ahead of need; every index is also a code he can hand out with no further write.
  await commit(client, bobKey, await sync(bobKey), (s) => planBurnBlock(bobKey, s, block(4)));
  const code = {
    chainId: 1n,
    tokenId: TOKEN,
    burnAddress: randomBytes(20),
    publicKey: randomBytes(32),
    key: codeKey(bobKey.seed, 1n, TOKEN, 5),
  };

  // Alice and Mallory pay it, any amount. Alice pays twice, the second time from a state that missed
  // Mallory's payment: her slot is taken, so `commit` refreshes and writes past it.
  const payCode = (from: ViewKey, value: bigint) => (s: SyncState) =>
    planPayCode(client, from, s, code, opening(1n, value));
  const alices = await commit(client, aliceKey, await sync(aliceKey), payCode(aliceKey, 50n));
  await commit(client, malloryKey, await sync(malloryKey), payCode(malloryKey, 7n));
  await commit(client, aliceKey, alices.state, payCode(aliceKey, 60n));

  // Bob finds every payment in the code's lane, each naming its (unverified) payer. Each payer's history holds
  // its own payments only, under the code it paid; none names Bob.
  const at = (index: number) => ({ type: 'code', chainId: 1n, tokenId: TOKEN, index });
  expect(await received(bobKey)).toEqual([
    [null, at(4), []],
    [
      null,
      at(5),
      [
        [1n, 50n],
        [1n, 7n],
        [1n, 60n],
      ],
    ],
  ]);
  const added = (await refresh(client, bobKey, emptyState(bobKey, CHAINS))).added.filter(
    (a) => a.direction === 'incoming',
  );
  expect(added.map((a) => a.peer)).toEqual([alice.address, mallory.address, alice.address]);
  const paid = { type: 'code', code };
  expect(await sent(aliceKey)).toEqual([
    [
      null,
      paid,
      [
        [1n, 50n],
        [1n, 60n],
      ],
    ],
  ]);
  expect(await sent(malloryKey)).toEqual([[null, paid, [[1n, 7n]]]]);
});

test('merge outputs and change stay with their owner', async () => {
  const [aliceKey, bobKey] = [await key(alice), await key(bob)];
  await pay(bobKey, alice.address, 1n, 100n);
  await pay(bobKey, alice.address, 1n, 200n);

  // Alice merges her two notes (on chain, a transact spending both), recording the output first.
  const merge = (s: SyncState) => planSelf(aliceKey, s, opening(1n, 300n), receipt('merged', 300n, new Uint8Array(20)));
  const merged = await commit(client, aliceKey, await sync(aliceKey), merge);
  expect(values(merged.added)).toEqual([['own', 'note', 300n]]);

  // She pays Bob 50 from it, with the change in the same batch.
  const toBob = (await lookupRecipient(client, bob.address))!;
  const payWithChange = (s: SyncState) => [
    ...planSend(aliceKey, s, toBob, opening(1n, 50n)),
    ...planSelf(aliceKey, s, opening(1n, 250n), receipt('sent', 50n, bob.address)),
  ];
  const paid = await commit(client, aliceKey, merged.state, payWithChange);
  expect(values(paid.added)).toEqual([
    ['own', 'note', 250n],
    ['outgoing', 'note', 50n],
  ]);

  // A fresh device finds both notes to self from the view key alone. Bob sees only his payment.
  const own = (await sync(aliceKey)).own[0]!.records;
  expect(own.map((r) => [valueOf(r), r.kind === 'note' && r.receipt?.kind])).toEqual([
    [300n, 'merged'],
    [250n, 'sent'],
  ]);
  expect(await received(bobKey)).toEqual([[alice.address, { type: 'address' }, [[1n, 50n]]]]);
});

test('burn blocks reach every device', async () => {
  const aliceKey = await key(alice);
  const record = (s: SyncState, chainId: bigint, first: number) =>
    planBurnBlock(aliceKey, s, { chainId, tokenId: TOKEN, first, salts: [randomBytes(32)] });

  // Two devices record blocks from states that do not know of each other's writes: the second one's
  // slot is taken, so `commit` refreshes and records it in the next one.
  const stale = await sync(aliceKey);
  const first = await commit(client, aliceKey, stale, (s) => record(s, 1n, 8));
  await commit(client, aliceKey, stale, (s) => record(s, 1n, 9));
  await commit(client, aliceKey, first.state, (s) => record(s, 10n, 8));

  // A fresh device finds every block, per chain, in the order they were recorded; so does a device
  // that only follows the log.
  const blocks = (s: SyncState) =>
    s.own.map((c) => [c.chainId, c.records.map((r) => r.kind === 'burn-block' && r.first)]);
  expect(blocks(await sync(aliceKey))).toEqual([
    [1n, [8, 9]],
    [10n, [8]],
  ]);
  const follower = await sync(aliceKey, first.state);
  expect(blocks(follower)).toEqual([
    [1n, [8, 9]],
    [10n, [8]],
  ]);
  expect(() => record(stale, 99n, 1)).toThrow('watch chain 99');
});

test('a point of sale records its addresses where every device of its owner finds them', async () => {
  const aliceKey = await key(alice);

  // Two devices each make a point of sale from states that do not know of each other's: the second one's slot is
  // taken, so `commit` refreshes and it takes the next number.
  const stale = await sync(aliceKey);
  const make = async () => {
    let n = -1;
    await commit(client, aliceKey, stale, (s) => planPosLane(aliceKey, s, 1n, (n = nextPosLane(s))));
    return n;
  };
  expect([await make(), await make()]).toEqual([0, 1]);
  const before = await sync(aliceKey);

  // Point of sale 1 writes with its key alone; three blocks in one batch from a stale cursor land past the first.
  const till = posKey(aliceKey.seed, 1);
  const pos = (first: number) => ({ chainId: 10n, tokenId: TOKEN, first, salts: [randomBytes(32), randomBytes(32)] });
  expect(await writePosBlocks(client, till, [pos(0)])).toBe(1);
  expect(await writePosBlocks(client, till, [pos(2), pos(4), pos(6)], 0)).toBe(4);

  // A fresh device finds both points of sale and the blocks in the second one's lane; so does a device that only
  // follows the log, to which they are news from point of sale 1.
  const lanes = (s: SyncState) =>
    s.incoming.map((c) => [
      c.via,
      c.chains.map((chain) => [chain.chainId, chain.records.map((r) => r.kind === 'burn-block' && r.first)]),
    ]);
  const expected = [
    [
      { type: 'pos', n: 0 },
      [
        [1n, []],
        [10n, []],
      ],
    ],
    [
      { type: 'pos', n: 1 },
      [
        [1n, []],
        [10n, [0, 2, 4, 6]],
      ],
    ],
  ];
  expect(lanes(await sync(aliceKey))).toEqual(expected);
  const followed = await refresh(client, aliceKey, before);
  expect(lanes(followed.state)).toEqual(expected);
  expect(followed.added.map((a) => [a.direction, a.lane?.via, a.peer, a.record.kind])).toEqual(
    Array(4).fill(['incoming', { type: 'pos', n: 1 }, null, 'burn-block']),
  );
});

test('audits come only from the auditor and are publicly logged', async () => {
  const bobKey = await key(bob);
  const asAuditor = new CanisterClient(
    await HttpAgent.create({ host, identity: auditor, shouldFetchRootKey: true }),
    canisterId,
  );

  // Bob escrowed his view key when he registered; only the auditor can have it opened, and gets the
  // same key Bob has.
  const transport = TransportSecretKey.random();
  const args = { target: bob.address, notify_key: notifyKey(bobKey), transport_public_key: transport.publicKeyBytes() };
  expect(await client.actor.validate_audit_escrow_key(args)).toEqual({ Ok: expect.stringContaining(hex(bob.address)) });
  expect(await client.actor.audit_escrow_key(args)).toEqual({ Err: { Rejected: 'not the auditor' } });
  const encrypted = unwrap(await asAuditor.actor.audit_escrow_key(args));
  const registration = (await client.registration(bob.address))!;
  const audited = openEscrow(encrypted, transport, await client.escrowPublicKey(), registration);
  expect(audited?.seed).toEqual(bobKey.seed);

  // Anyone can read the log: one record, naming the auditor.
  const log = await client.actor.get_audits(0n, 10);
  expect(log.map((r) => [r.auditor.toText(), r.target])).toEqual([[auditor.getPrincipal().toText(), bob.address]]);
});

test('ingress no method could take is refused before it runs', async () => {
  // a query called as an update where a stale answer matters goes through, but not one that answers as a query only
  await expect(client.replicated.registration(alice.address, [])).resolves.toEqual([]);
  await expect(client.replicated.get_log(0n, 1)).rejects.toThrow();
  // a batch far larger than any valid one never reaches submit, which would answer with Rejected
  const huge = { Put: { kind: { Lane: null }, id: new Uint8Array(32), data: new Uint8Array(1 << 20) } };
  await expect(client.actor.submit([huge], 0n)).rejects.toThrow();
});

test('registering anew moves new payments to the new key', async () => {
  const [aliceKey, oldKey] = [await key(alice), await key(bob)];
  const fromAlice = (value: bigint) => [[alice.address, { type: 'address' }, [[1n, value]]]];

  // Bob registers another root seed between two payments. Alice looks him up before each payment, so the second
  // goes to a fresh channel in the new registration's inbox, which only the new key can read.
  await pay(aliceKey, bob.address, 1n, 100n);
  const newRoot = randomBytes(32);
  const newKey = viewKey(newRoot, bob.address, client.canisterId);
  await register(client, bob.sign, newKey, publicKeyOf(newRoot));
  await pay(aliceKey, bob.address, 1n, 200n);
  expect(await received(oldKey)).toEqual(fromAlice(100n));
  expect(await received(newKey)).toEqual(fromAlice(200n));
  await expect(key(bob)).rejects.toThrow('another root seed');

  // Registrations and notes live in stable memory, so an upgrade keeps them.
  await pic.upgradeCanister({ canisterId, wasm: WASM, arg: IDL.encode([IDL.Opt(InitArgs)], [[]]) });
  expect((await client.registration(bob.address))?.notify_key).toEqual(notifyKey(newKey));
  expect(await received(newKey)).toEqual(fromAlice(200n));
});

/** Counts calls per actor and method from now on. */
function countCalls(): () => Record<string, number> {
  const counts: Record<string, number> = {};
  for (const side of ['actor', 'replicated'] as const) {
    const actor = client[side] as unknown as Record<string, (...args: unknown[]) => unknown>;
    for (const method of Object.keys(actor).filter((m) => typeof actor[m] === 'function')) {
      const original = actor[method]!;
      actor[method] = (...args) => {
        counts[`${side}.${method}`] = (counts[`${side}.${method}`] ?? 0) + 1;
        return original(...args);
      };
    }
  }
  return () => counts;
}

test("a restored account's seed reaches every device of its passkey", async () => {
  const [prf, seed] = [randomBytes(32), randomBytes(32)];
  const slot = async (i: number) =>
    (await client.actor.get_slots({ Outgoing: null }, [passkeySeedId(prf, canisterId, i)]))[0];
  expect(await fetchPasskeySeed(client, prf)).toBeNull();

  // Someone who saw the slot's id asked for writes it first: the seed goes to the next one.
  const submit = client.submit.bind(client);
  vi.spyOn(client, 'submit').mockImplementationOnce(async (actions) => {
    const put = actions[0]!;
    if (!('Put' in put)) throw new Error('a seed is a Put');
    await submit([{ Put: { ...put.Put, data: randomBytes(256) } }]);
    return submit(actions);
  });
  await storePasskeySeed(client, prf, seed);
  expect(await slot(1)).not.toEqual([]);

  // The passkey's other device finds it, and keeping it again writes nothing.
  const other = new CanisterClient(agent, canisterId);
  expect(await fetchPasskeySeed(other, prf)).toEqual(seed);
  await storePasskeySeed(other, prf, seed);
  expect(await slot(2)).toEqual([]);
  expect(await fetchPasskeySeed(other, randomBytes(32))).toBeNull();
});

test('polling reads only what is new', async () => {
  const [aliceKey, bobKey] = [await key(alice), await key(bob)];

  // Bob has two codes, from a burn block, and a point of sale; Alice pays him once.
  const coded = await commit(client, bobKey, emptyState(bobKey, CHAINS), (s) => planBurnBlock(bobKey, s, block(0)));
  const { state: bobs } = await commit(client, bobKey, coded.state, (s) => planPosLane(bobKey, s, 1n, nextPosLane(s)));
  const toBob = (await lookupRecipient(client, bob.address))!;
  const pay = (s: SyncState, value: bigint) => planSend(aliceKey, s, toBob, opening(1n, value));
  const { state: alices } = await commit(client, aliceKey, emptyState(aliceKey, CHAINS), (s) => pay(s, 100n));
  const first = await refresh(client, bobKey, bobs);
  expect(values(first.added)).toEqual([['incoming', 'note', 100n]]);

  // With nothing new, a refresh makes queries only: outgoing records, the address inbox and the note
  // log. It reads no lane, however many channels, codes and points of sale it has; a full refresh reads them all.
  const calls = countCalls();
  const quiet = await refresh(client, bobKey, first.state);
  expect(quiet.added).toEqual([]);
  expect(calls()).toEqual({ 'actor.get_slots': 1, 'actor.get_announcements': 1, 'actor.get_log': 1 });
  const full = countCalls();
  expect((await refresh(client, bobKey, first.state, { full: true })).added).toEqual([]);
  expect(full()['actor.get_slots']).toBe(3);

  // A new payment is the only addition on both sides, also after the state went through storage.
  const second = await commit(client, aliceKey, alices, (s) => pay(s, 200n));
  expect(values(second.added)).toEqual([['outgoing', 'note', 200n]]);
  const stored = importState(bobKey, exportState(bobKey, quiet.state))!;
  expect(values((await refresh(client, bobKey, stored)).added)).toEqual([['incoming', 'note', 200n]]);
});
