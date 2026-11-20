import type { NewRecord, StoredLane, SyncState } from '@zerc20/storage-sdk';
import { existsSync } from 'node:fs';
import { type Hex, hexToBytes, numberToHex } from 'viem';
import { expect, test, vi } from 'vitest';
import { type Ctx, chainState, spendKey } from '../src/context.js';
import {
  type Burn,
  type BurnCall,
  Search,
  burnAddress,
  burnAddressFor,
  core,
  initCore,
  runBurnsOn,
} from '../src/core.js';
import { emptyWalletState } from '../src/state.js';
import { nextBurn, takeDeposit, takeRefresh, unusedBurn } from '../src/sync.js';

const FR = 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001n;

test("a burn address a payer found from the published key is the owner's deposit, and only that", async () => {
  await initCore();
  const ctx = {
    seed: new Uint8Array(32).fill(7),
    owners: new Map(),
    state: emptyWalletState(`0x${'11'.repeat(20)}`),
  } as unknown as Ctx;
  // what a payer finds from the registered public key alone
  const burn = await burnAddressFor(1n, spendKey(ctx).publicKey);
  expect(BigInt(burn.salt) < FR).toBe(true);
  const told = (salt: Hex) => ({
    kind: 'deposit' as const,
    slotIndex: 0,
    atNs: 0n,
    chainId: 1n,
    tokenId: 1,
    value: new Uint8Array(32),
    burnSalt: hexToBytes(salt),
    burnAddress: hexToBytes(burn.address),
  });
  const [tokens, payer] = [new Map([[1n, [1, 2]]]), new Uint8Array(20).fill(2)];
  takeDeposit(ctx, told(numberToHex(BigInt(burn.salt) + 1n, { size: 32 })), payer, tokens); // another salt has no proof of work
  expect(ctx.state.deposits).toEqual([]);
  takeDeposit(ctx, told(burn.salt), payer, tokens);
  takeDeposit(ctx, told(burn.salt), payer, tokens); // told twice, taken once
  expect(ctx.state.deposits).toMatchObject([
    { chainId: 1n, tokenId: 1, burnIndex: -1, salt: burn.salt, address: burn.address, payer: `0x${'02'.repeat(20)}` },
  ]);
}, 120_000);

test("a point of sale's addresses, from its lane, are the owner's payments, with no burn index of the owner's", async () => {
  await initCore();
  const address: Hex = `0x${'11'.repeat(20)}`;
  const ctx = {
    seed: new Uint8Array(32).fill(7),
    owners: new Map(),
    state: emptyWalletState(address),
  } as unknown as Ctx;
  const laneKey = new Uint8Array(32).fill(9);
  const sold = await burnAddress(laneKey, 1n, 1, 0, spendKey(ctx).publicKey);
  const own = await burnAddress(new Uint8Array(32).fill(8), 1n, 1, 0, spendKey(ctx).publicKey);
  const block = (salt: Hex) => ({
    kind: 'burn-block' as const,
    slotIndex: 0,
    atNs: 0n,
    chainId: 1n,
    tokenId: 1,
    first: 0,
    salts: [hexToBytes(salt)],
  });
  const lane: StoredLane = {
    peer: null,
    via: { type: 'pos', n: 0 },
    seed: null,
    inbox: null,
    key: laneKey,
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
  const added: NewRecord[] = [
    { direction: 'incoming', lane, peer: null, record: block(sold.salt) },
    { direction: 'own', lane: null, peer: null, record: { kind: 'pos-lane', slotIndex: 1, atNs: 0n, n: 0 } },
    { direction: 'own', lane: null, peer: null, record: block(own.salt) },
  ];
  takeRefresh(ctx, { state, added }, new Map([[1n, [1]]]));
  expect(ctx.state.deposits).toMatchObject([
    { address: sold.address, burnIndex: -1, managed: true },
    { address: own.address, burnIndex: 0 },
  ]);
  expect(ctx.state.deposits[1]!.managed).toBeUndefined();
  // neither is handed out, and only the owner's own counts among the burn indices it hands out
  expect(unusedBurn(ctx, 1n, 1)).toBeUndefined();
  expect(nextBurn(ctx, 1n, 1)).toBe(1);
}, 120_000);

test('the burn address another device recorded ahead is never handed out here, and leaves the one recorded here', async () => {
  await initCore();
  const address: Hex = `0x${'11'.repeat(20)}`;
  const ctx = {
    seed: new Uint8Array(32).fill(7),
    owners: new Map(),
    state: emptyWalletState(address),
  } as unknown as Ctx;
  const key = new Uint8Array(32).fill(8);
  const [here, there] = await Promise.all([0, 1].map((i) => burnAddress(key, 1n, 1, i, spendKey(ctx).publicKey)));
  ctx.state.deposits.push({
    chainId: 1n,
    tokenId: 1,
    burnIndex: 0,
    salt: here.salt,
    address: here.address,
    createdMs: 0,
    depositAddress: null,
    watches: [],
    found: [],
  });
  const state: SyncState = {
    address: hexToBytes(address),
    chains: [1n],
    addressInboxRead: 0,
    incoming: [],
    outgoing: { next: 0, lanes: [] },
    own: [],
    log: 0,
  };
  const block = { kind: 'burn-block' as const, slotIndex: 1, atNs: 0n, chainId: 1n, tokenId: 1, first: 1 };
  const added: NewRecord[] = [
    { direction: 'own', lane: null, peer: null, record: { ...block, salts: [hexToBytes(there.salt)] } },
  ];
  takeRefresh(ctx, { state, added }, new Map([[1n, [1]]]));
  // the one recorded here is still the next handed out: nothing more is recorded ahead
  expect(unusedBurn(ctx, 1n, 1)?.address).toBe(here.address);
  // once it is, the next is past the other device's
  chainState(ctx, 1n).burnNext[1] = 1;
  expect(unusedBurn(ctx, 1n, 1)).toBeUndefined();
  expect(nextBurn(ctx, 1n, 1)).toBe(2);
}, 120_000);

test('a search takes the first block that holds an address, in whatever order the blocks finish', () => {
  const burn = (block: number): Burn => ({ salt: numberToHex(block, { size: 32 }), address: `0x${'00'.repeat(20)}` });
  const holding = new Set([5, 9, 12]);
  for (let trial = 0; trial < 50; trial++) {
    const settled: unknown[] = [];
    const search = { burnKey: new Uint8Array(32), chainId: 1n, tokenId: 1, index: 0, publicKey: '0x01' as const };
    const s = new Search(search, (r) => settled.push(r));
    const taken = Array.from({ length: 16 }, () => s.take()!);
    // a worker died with one: it is handed out again first
    s.drop(taken[3]!);
    expect(s.take()).toBe(taken[3]);
    taken.sort(() => Math.random() - 0.5);
    for (const block of taken) s.finish(block, holding.has(block) ? burn(block) : null);
    expect(settled).toEqual([{ burn: burn(5) }]);
  }
});

test('a runner set while blocks run on this thread takes every block from then on', async () => {
  await initCore();
  const { publicKey } = core.spendKey(new Uint8Array(32).fill(7)) as { publicKey: Hex };
  const stop = new AbortController();
  // its address is in block 285: this thread is still on it, waiting between two blocks, when the runner comes
  const search = burnAddress(new Uint8Array(32).fill(5), 1n, 1, 0, publicKey, { signal: stop.signal }).catch(
    () => null,
  );
  await new Promise((r) => setTimeout(r, 150));
  const from: number[] = [];
  runBurnsOn({
    slots: 1,
    run: (c) =>
      new Promise((answer) => {
        from.push((c as { from: number }).from);
        setTimeout(() => answer(null), 0);
      }),
  });
  try {
    await vi.waitFor(() => expect(from.length).toBeGreaterThanOrEqual(10));
    // none ran here meanwhile: the runner's blocks follow one another
    expect(from.slice(0, 10).map((f) => f - from[0]!)).toEqual(Array.from({ length: 10 }, (_, i) => i * 512));
  } finally {
    stop.abort();
    runBurnsOn(null);
  }
  expect(await search).toBeNull();
});

test('blocks go first to the searches waited for, to each owner in turn, and one in four to those made ahead', async () => {
  await initCore();
  const key = (owner: number) => new Uint8Array(32).fill(owner);
  const asked: { owner: number; answer: (b: Burn | null) => void }[] = [];
  const runner = {
    slots: 0,
    run: (c: BurnCall) =>
      new Promise<Burn | null>((answer) => asked.push({ owner: 'burnKey' in c ? c.burnKey[0]! : 0, answer })),
  };
  runBurnsOn(runner);
  try {
    // owner 1 makes three ahead; owner 2 waits for three, owner 3 for one
    const all = [
      ...[0, 1, 2].map((i) => burnAddress(key(1), 1n, 1, i, '0x01', { urgent: false })),
      ...[0, 1, 2].map((i) => burnAddress(key(2), 1n, 1, i, '0x01')),
      burnAddress(key(3), 1n, 1, 0, '0x01'),
    ];
    await new Promise((r) => setTimeout(r, 0));
    runner.slots = 1;
    runBurnsOn(runner);
    const order: number[] = [];
    for (let i = 0; i < 8; i++) {
      await vi.waitFor(() => expect(asked).toHaveLength(i + 1));
      order.push(asked[i]!.owner);
      asked[i]!.answer(null);
    }
    expect(order.filter((o) => o === 1)).toHaveLength(2);
    const waited = order.filter((o) => o !== 1);
    expect(waited.every((o, i) => i === 0 || o !== waited[i - 1])).toBe(true);
    // answered with an address from here on, every search ends on one
    const hit: Burn = { salt: '0x01', address: `0x${'00'.repeat(20)}` };
    runner.run = async () => hit;
    expect(await Promise.all(all)).toEqual(Array(7).fill(hit));
  } finally {
    runBurnsOn(null);
  }
});

test('a runner taken away hands its blocks back, and what it answers after is dropped', async () => {
  await initCore();
  const late: ((b: Burn | null) => void)[] = [];
  runBurnsOn({ slots: 2, run: () => new Promise((answer) => late.push(answer)) });
  // wallet_keys::tests::burn_addresses_are_stable
  const { publicKey } = core.spendKey(new Uint8Array(32).fill(7)) as { publicKey: Hex };
  const found = burnAddress(new Uint8Array(32).fill(9), 1n, 1, 0, publicKey);
  await vi.waitFor(() => expect(late).toHaveLength(2));
  runBurnsOn(null);
  for (const answer of late) answer({ salt: '0x01', address: `0x${'00'.repeat(20)}` });
  expect(await found).toEqual({
    salt: '0x2e317f73c5bf700ed29866a5911b2580f080f3448ed825e84950d3ae4605fdb8',
    address: '0x33b43727f947d4f7e6c3a99b7127a28ebf42661e',
  });
}, 120_000);

// the pool runs from the built package, where burnWorker.js is; from source, blocks run on this thread
test.skipIf(!existsSync(new URL('../dist/core.js', import.meta.url)))(
  'the worker pool finds the pinned burn address',
  async () => {
    const { burnAddress, core } = await import('../dist/core.js');
    // wallet_keys::tests::burn_addresses_are_stable
    const { publicKey } = core.spendKey(new Uint8Array(32).fill(7)) as { publicKey: Hex };
    expect(await burnAddress(new Uint8Array(32).fill(9), 1n, 1, 0, publicKey)).toEqual({
      salt: '0x2e317f73c5bf700ed29866a5911b2580f080f3448ed825e84950d3ae4605fdb8',
      address: '0x33b43727f947d4f7e6c3a99b7127a28ebf42661e',
    });
  },
  60_000,
);
