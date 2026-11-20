import type { NewRecord, StoredLane, SyncState } from '@zerc20/storage-sdk';
import { hexToBytes, numberToHex } from 'viem';
import { expect, test, vi } from 'vitest';
import type { Token } from '../src/chain.js';
import { type Ctx, chainState } from '../src/context.js';
import { initCore } from '../src/core.js';
import { type OperationRecord, emptyWalletState } from '../src/state.js';
import { CODES_AHEAD, keyAll, takeRefresh } from '../src/sync.js';
import { Wallet } from '../src/wallet.js';

const seed = new Uint8Array(32).fill(7);
const address = `0x${'11'.repeat(20)}` as const;
const down = () => Promise.reject(new Error('down'));
const zeth = { chainId: 1n, tokenId: 1 } as Token;
/** A wallet on one chain whose storage is down: each sync fails, then ends as any does. Its tokens take a few ms, so a
 * call made while it runs queues behind it. */
function ctx(): Ctx {
  const c = {
    seed,
    owners: new Map(),
    refundSigners: new Map(),
    view: { address: new Uint8Array(20), seed: new Uint8Array(32) },
    chains: [
      {
        config: { chainId: 1n },
        chain: { tokens: () => new Promise((r) => setTimeout(() => r([]), 5)), known: [] },
        indexer: { status: async () => ({ commitments: 0, commitmentsFinal: 0, nullifiers: 0, nullifiersFinal: 0 }) },
      },
    ],
    state: emptyWalletState(address),
    storage: { actor: { log_length: down } },
    save: async () => {},
    lastFullRefreshMs: 0,
  } as unknown as Ctx;
  keyAll(c, [zeth]); // as opening does
  return c;
}
const open = (c: Ctx, unlock: () => Promise<Uint8Array>) =>
  new (Wallet as unknown as new (ctx: Ctx, unlock: () => Promise<Uint8Array>) => Wallet)(c, unlock);
/** A sync, through its end: it settles before the burn addresses are topped up, and lets the seed go after. */
const sync = async (w: Wallet) => {
  await w.sync().catch(() => {});
  await new Promise((r) => setTimeout(r, 20));
};
const token = {} as Token;

test('opened with a function for its seed, the wallet lets the seed go at the end of a sync, and asks for it again to pay', async () => {
  await initCore();
  const c = ctx();
  const unlock = vi.fn(async () => seed);
  const wallet = open(c, unlock);
  await sync(wallet);
  expect(c.seed).toBeNull();
  // asked before anything else: the recipient's lookup then fails, storage being down
  await expect(wallet.send({ to: `0x${'22'.repeat(20)}`, token, amount: 1n, maxFee: 0n })).rejects.toThrow();
  expect(unlock).toHaveBeenCalledTimes(1);
  expect(c.seed).toBe(seed);
  await sync(wallet);
  expect(c.seed).toBeNull();
}, 120_000);

test('the seed stays while a payment is in flight, and for a call that waits behind the sync', async () => {
  await initCore();
  const c = ctx();
  const unlock = vi.fn(async () => seed);
  const wallet = open(c, unlock);
  const data = { to: { kind: 'public' as const, address }, maxFee: 0n, step: null, paid: 0n };
  // on a chain the network lacks: advancing it fails every sync, and it stays pending
  const op: OperationRecord = {
    id: 's',
    kind: 'send',
    chainId: 9n,
    tokenId: 1,
    amount: 1n,
    createdMs: 0,
    status: 'pending',
    data,
  };
  c.state.ops.push(op);
  await sync(wallet);
  expect(c.seed).toBe(seed);
  op.status = 'failed';
  const syncing = sync(wallet);
  // refused once it runs: the network has no merge prover
  const merging = wallet.consolidate({ token, maxFee: 0n }).catch(() => {});
  await syncing;
  expect(c.seed).toBe(seed);
  await merging;
  await sync(wallet);
  expect(c.seed).toBeNull();
  expect(unlock).not.toHaveBeenCalled();
}, 120_000);

test("the seed a function gives must be the wallet's own", async () => {
  await initCore();
  const c = ctx();
  const wallet = open(c, async () => new Uint8Array(32).fill(8));
  await sync(wallet);
  await expect(wallet.consolidate({ token, maxFee: 0n })).rejects.toMatchObject({ code: 'invalid' });
  expect(c.seed).toBeNull();
}, 120_000);

test('a note paid to a code whose key was not derived waits for the seed, then is watched', async () => {
  await initCore();
  const c = ctx();
  const wallet = open(c, async () => seed);
  await sync(wallet);
  // another device's code, which this one never derived
  const lane: StoredLane = {
    peer: null,
    via: { type: 'code', chainId: 1n, tokenId: 1, index: 5 },
    seed: null,
    inbox: null,
    key: new Uint8Array(32),
    chains: [],
  };
  const state: SyncState = {
    address: hexToBytes(address),
    chains: [1n],
    addressInboxRead: 0,
    incoming: [lane],
    outgoing: { next: 0, lanes: [] },
    own: [],
    log: 0,
  };
  const bytes = (n: bigint) => hexToBytes(numberToHex(n, { size: 32 }));
  const added: NewRecord[] = [
    {
      direction: 'incoming',
      lane,
      peer: null,
      record: {
        kind: 'note',
        slotIndex: 0,
        atNs: 0n,
        opening: { chainId: 1n, tokenId: 1, value: bytes(5n), noteSalt: bytes(3n) },
      },
    },
  ];
  takeRefresh(c, { state, added }, new Map([[1n, [1]]]));
  expect(c.state.notes).toMatchObject([{ keyIndex: 5, unkeyed: true, watch: null }]);
  await wallet.consolidate({ token, maxFee: 0n }).catch(() => {}); // asks for the seed first
  expect(c.state.notes[0]).not.toHaveProperty('unkeyed');
  expect(c.state.notes[0]!.watch).not.toBeNull();
}, 120_000);

test('a receive code asks for the seed only past those whose owners were derived ahead', async () => {
  await initCore();
  const c = ctx();
  const unlock = vi.fn(async () => seed);
  const wallet = open(c, unlock);
  await sync(wallet);
  expect(c.seed).toBeNull();
  // refused once it writes the burn address, storage being down: the seed was not asked for
  await expect(wallet.receiveCode(zeth)).rejects.toThrow();
  expect(unlock).not.toHaveBeenCalled();
  chainState(c, 1n).burnNext[1] = CODES_AHEAD;
  await expect(wallet.receiveCode(zeth)).rejects.toThrow();
  expect(unlock).toHaveBeenCalledTimes(1);
}, 120_000);

test('a deposit address asks for the seed only past the refund signers derived ahead', async () => {
  await initCore();
  const c = ctx();
  const unlock = vi.fn(async () => seed);
  const wallet = open(c, unlock);
  await sync(wallet);
  expect(c.seed).toBeNull();
  // refused once it writes the burn address, storage being down: the seed was not asked for
  await expect(wallet.depositAddress(zeth)).rejects.toThrow();
  expect(unlock).not.toHaveBeenCalled();
  chainState(c, 1n).burnNext[1] = CODES_AHEAD;
  await expect(wallet.depositAddress(zeth)).rejects.toThrow();
  expect(unlock).toHaveBeenCalledTimes(1);
}, 120_000);
