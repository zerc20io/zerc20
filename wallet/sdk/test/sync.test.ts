import { type NewRecord, emptyState } from '@zerc20/storage-sdk';
import { bytesToHex, concat, getAddress, hexToBytes, numberToHex } from 'viem';
import { expect, test } from 'vitest';
import { type Ctx, owner } from '../src/context.js';
import { core, initCore } from '../src/core.js';
import { type NoteRecord, type Position, emptyWalletState, unspent } from '../src/state.js';
import { applySpends, decisionEstimate, keyAll, syncAll, takeRefresh } from '../src/sync.js';
import { type CoinInfo, Wallet, waitsOn } from '../src/wallet.js';

const view = { address: new Uint8Array(20), seed: new Uint8Array(32) };
const down = () => Promise.reject(new Error('down'));
const chain = (chainId: bigint, tokens: () => Promise<{ tokenId: number }[]>) => {
  // as a Chain does: `known` is what `tokens()` last read
  const c = { known: [] as { tokenId: number }[], tokens: async () => (c.known = await tokens()) };
  return {
    config: { chainId },
    chain: c,
    indexer: { status: async () => ({ commitments: 0, commitmentsFinal: 0, nullifiers: 0, nullifiersFinal: 0 }) },
  };
};
const ctx = (chains: ReturnType<typeof chain>[]) =>
  ({
    view,
    chains,
    state: emptyWalletState(`0x${'11'.repeat(20)}`),
    storage: { actor: { log_length: down } },
    save: async () => {},
    lastFullRefreshMs: 0,
  }) as unknown as Ctx;
const synced = (c: Ctx) => c.state.chains.filter((s) => s.samples.length > 0).map((s) => s.chainId);

test('a chain whose tokens cannot be read holds back storage and itself, not another chain', async () => {
  const c = ctx([chain(1n, down), chain(2n, async () => [{ tokenId: 1 }])]);
  const before = c.state.storage;
  expect(await syncAll(c)).toEqual([new Error('down')]);
  expect(synced(c)).toEqual([2n]);
  expect(c.state.storage).toBe(before); // not refreshed without every chain's tokens
});

test('storage that fails holds back no chain', async () => {
  const c = ctx([chain(1n, async () => []), chain(2n, async () => [])]);
  expect(await syncAll(c)).toEqual([new Error('down')]);
  expect(synced(c)).toEqual([1n, 2n]);
});

test('an operation whose next step keeps failing stays pending, saying why and since when', async () => {
  const c = ctx([chain(1n, async () => [])]);
  // on a chain the network lacks: advancing it throws an error that is not the wallet's own, as a wasm trap does
  const data = { to: { kind: 'self' as const }, maxFee: 0n, step: null, paid: 0n };
  c.state.ops.push({
    id: 'm',
    kind: 'consolidate',
    chainId: 9n,
    tokenId: 1,
    amount: 0n,
    createdMs: 0,
    status: 'pending',
    data,
  });
  const wallet = new (Wallet as unknown as new (ctx: Ctx) => Wallet)(c);
  const [op] = wallet.operations();
  await wallet.sync().catch(() => {}); // storage is down too
  expect(op!.status).toBe('pending');
  expect(op!.retrying).toMatchObject({ message: 'Error: chain 9 is not in this network', code: undefined });
  const since = op!.retrying!.since.getTime();
  await new Promise((r) => setTimeout(r, 5));
  await wallet.sync().catch(() => {});
  expect(op!.retrying!.since.getTime()).toBe(since);
});

test('activity is what storage and the chain hold; operations add only a failure and what no change shows yet', async () => {
  const c = ctx([chain(1n, async () => [{ chainId: 1n, tokenId: 1 }] as { tokenId: number }[])]);
  const a = (n: number) => `0x${n.toString(16).repeat(40)}` as const;
  const at = (index: number, atMs: number) => ({ index, tentative: false, spent: false, confirmed: true, atMs });
  const note = { chainId: 1n, tokenId: 1, peer: null, atNs: null, noteHash: '0x01', watch: null } as const;
  const s = c.state;
  s.notes.push(
    { ...note, value: 5n, salt: '0x0a', source: 'received', peer: a(1), found: [at(10, 1000)] },
    // a payment's zero-value change, which says what the payment was
    {
      ...note,
      value: 0n,
      salt: '0x0b',
      source: 'self',
      receipt: { kind: 'sent', amount: 7n, fee: 1n, counterparty: a(2) },
      found: [at(11, 2000)],
    },
    {
      ...note,
      value: 9n,
      salt: '0x0c',
      source: 'self',
      receipt: { kind: 'merged', amount: 9n, fee: 2n, counterparty: a(0) },
      found: [at(12, 3000)],
    },
  );
  const transfer = (index: number, amount: bigint) => ({
    ...at(index, 4000),
    tokenId: 1,
    sender: a(3),
    amount,
    asp: 'approved' as const,
  });
  const watches = [] as { tokenId: number; watch: { key: `0x${string}`; from: number; scannedTo: number } }[];
  s.deposits.push(
    {
      chainId: 1n,
      tokenId: 1,
      burnIndex: 0,
      salt: '0x01',
      address: a(4),
      createdMs: 0,
      depositAddress: null,
      watches,
      found: [transfer(13, 4n)],
    },
    // one a point of sale handed out
    {
      chainId: 1n,
      tokenId: 1,
      burnIndex: -1,
      salt: '0x02',
      address: a(5),
      createdMs: 0,
      depositAddress: null,
      managed: true,
      watches,
      found: [transfer(15, 6n)],
    },
    // a deposit address handed out here, which nothing has reached yet
    {
      chainId: 1n,
      tokenId: 1,
      burnIndex: 1,
      salt: '0x03',
      address: a(10),
      createdMs: 100,
      depositAddress: a(11),
      watches,
      found: [],
    },
  );
  s.sent.push({ chainId: 1n, tokenId: 1, address: a(5), to: a(6), createdMs: 0, watches, found: [transfer(14, 3n)] });
  // another device's deposit address for the burn address, whose receipt does not tell its fee, and its rage exit of
  // the deposit
  s.receipts.push(
    { kind: 'deposit-address', chainId: 1n, tokenId: 1, burnAddress: a(4), depositAddress: a(3), atMs: 0 },
    {
      kind: 'deposit-address',
      chainId: 1n,
      tokenId: 1,
      burnAddress: a(10),
      depositAddress: a(11),
      args: { fee: 2n, feeRecipient: a(12), refundSigner: a(13), referrer: a(0), referralBps: 0 },
      atMs: 200,
    },
    {
      kind: 'returned',
      chainId: 1n,
      tokenId: 1,
      burnAddress: a(4),
      index: 13,
      recipient: a(7),
      amount: 4n,
      txHash: '0xee',
      atMs: 5000,
    },
  );
  const spend = (id: string, kind: 'send' | 'withdraw', status: 'done' | 'failed', changes: `0x${string}`[]) => ({
    id,
    kind,
    chainId: 1n,
    tokenId: 1,
    amount: 7n,
    createdMs: 6000,
    status,
    data: { to: { kind: 'public' as const, address: a(8) }, maxFee: 1n, step: null, paid: 1n, changes },
  });
  s.ops.push(spend('shown-by-its-change', 'send', 'done', ['0x0b']), spend('failed-here', 'withdraw', 'failed', []), {
    id: 'deposit-not-found-yet',
    kind: 'deposit',
    chainId: 1n,
    tokenId: 1,
    amount: 2n,
    createdMs: 500,
    status: 'done',
    data: { burnAddress: a(9), to: a(6), txHash: '0xdd' },
  });
  const wallet = new (Wallet as unknown as new (ctx: Ctx) => Wallet)(c);
  await wallet.sync().catch(() => {}); // reads the tokens; the fakes fail the rest
  expect(wallet.activity().map((x) => [x.id, x.kind, x.amount, x.fee, x.at?.getTime()])).toEqual([
    ['failed-here', 'withdrawn', 7n, 1n, 6000],
    ['returned:1:13', 'returned', 4n, null, 5000],
    ['deposited:1:13', 'deposited', 4n, null, 4000],
    ['sale:1:15', 'sale', 6n, null, 4000],
    ['sent:1:14', 'sent', 3n, null, 4000],
    ['merged:1:12', 'merged', 9n, 2n, 3000],
    ['sent:1:11', 'sent', 7n, 1n, 2000],
    ['received:1:10', 'received', 5n, null, 1000],
    ['deposit-not-found-yet', 'sent', 2n, null, 500],
  ]);
  const byId = new Map(wallet.activity().map((x) => [x.id, x]));
  expect(byId.get('deposited:1:13')).toMatchObject({ via: { depositAddress: a(3) }, burnAddress: a(4) });
  // the fee is known where the receipt tells it
  expect(wallet.depositAddresses().map((x) => [x.address, x.fee, x.at.getTime()])).toEqual([
    [getAddress(a(11)), 2n, 200],
    [getAddress(a(3)), null, 0],
  ]);
  expect(byId.get('sale:1:15')).toMatchObject({ counterparty: a(3), burnAddress: a(5) });
  expect(byId.get('received:1:10')!.burnAddress).toBeNull();
  expect(byId.get('returned:1:13')).toMatchObject({ counterparty: a(7), txHash: '0xee', coin: '1:13' });
  expect(byId.get('sent:1:14')).toMatchObject({ counterparty: a(6) });
  expect(byId.get('failed-here')!.status).toBe('failed');
  // the zero-value change is no coin
  expect(wallet.coins().map((x) => x.id)).not.toContain('1:11');
});

test('what storage told of shows in activity only once its transaction is on chain: a payer writes there first, and may never send it', async () => {
  const c = ctx([chain(1n, async () => [{ chainId: 1n, tokenId: 1 }] as { tokenId: number }[])]);
  const a = (n: number) => `0x${n.toString(16).repeat(40)}` as const;
  const note = { chainId: 1n, tokenId: 1, peer: null, atNs: 1_000_000_000n, noteHash: '0x01', watch: null } as const;
  const s = c.state;
  s.notes.push(
    { ...note, value: 5n, salt: '0x0a', source: 'received', peer: a(1), found: [] },
    // another device's payment and merge, by their changes
    {
      ...note,
      value: 0n,
      salt: '0x0b',
      source: 'self',
      receipt: { kind: 'sent', amount: 7n, fee: 1n, counterparty: a(2) },
      found: [],
    },
    {
      ...note,
      value: 9n,
      salt: '0x0c',
      source: 'self',
      receipt: { kind: 'merged', amount: 9n, fee: 2n, counterparty: a(0) },
      found: [],
    },
  );
  const watched = { chainId: 1n, tokenId: 1, createdMs: 1000, watches: [], found: [] };
  // a payer's deposit into a burn address of this wallet's, and another device's deposit that pays someone
  s.deposits.push({ ...watched, burnIndex: -1, salt: '0x01', address: a(4), depositAddress: null, payer: a(3) });
  s.sent.push({ ...watched, address: a(5), to: a(6) });
  const wallet = new (Wallet as unknown as new (ctx: Ctx) => Wallet)(c);
  await wallet.sync().catch(() => {}); // reads the tokens; the fakes fail the rest
  expect(wallet.activity()).toEqual([]);
});

test("a deposit address's receipt in storage tells every device what it was registered with, and a later one tells it where the first did not", () => {
  const c = ctx([]);
  const a = (n: number) => hexToBytes(`0x${n.toString(16).repeat(40)}`);
  const word = (n: bigint) => hexToBytes(numberToHex(n, { size: 32 }));
  const receipt = (burn: number, fee: bigint | null, atNs: bigint, deposit = burn + 1): NewRecord => ({
    direction: 'own',
    lane: null,
    peer: null,
    record: {
      kind: 'deposit-address',
      slotIndex: 0,
      atNs,
      chainId: 1n,
      tokenId: 1,
      burnAddress: a(burn),
      depositAddress: a(deposit),
      ...(fee !== null && {
        args: { fee: word(fee), feeRecipient: a(7), refundSigner: a(8), referrer: a(9), referralBps: 30 },
      }),
    },
  });
  const state = emptyState(c.view, [1n]);
  const take = (...added: NewRecord[]) => takeRefresh(c, { state, added }, new Map([[1n, [1]]]));
  // registered here, not yet written
  const here = { chainId: 1n, tokenId: 1, burnAddress: bytesToHex(a(2)), depositAddress: bytesToHex(a(3)) } as const;
  const args = {
    feeRecipient: bytesToHex(a(7)),
    refundSigner: bytesToHex(a(8)),
    referrer: bytesToHex(a(9)),
    referralBps: 30,
  };
  c.state.receipts.push({ ...here, kind: 'deposit-address', args: { ...args, fee: 2n }, atMs: 0, unwritten: true });
  take(receipt(2, 2n, 1_000_000n), receipt(4, 3n, 2_000_000n), receipt(6, null, 3_000_000n));
  expect(c.state.receipts[1]).toMatchObject({ args: { ...args, fee: 3n } });
  const fees = () => c.state.receipts.map((r) => r.kind === 'deposit-address' && [r.args?.fee, r.atMs, r.unwritten]);
  expect(fees()).toEqual([
    [2n, 1, undefined],
    [3n, 2, undefined],
    [undefined, 3, undefined],
  ]);
  // written anew elsewhere, with what it was registered with
  take(receipt(6, 4n, 4_000_000n));
  expect(fees()[2]).toEqual([4n, 4, undefined]);
  // another deposit address for the first burn address, registered elsewhere with arguments of its own
  take(receipt(2, 5n, 5_000_000n, 12));
  expect(fees()).toEqual([
    [2n, 1, undefined],
    [3n, 2, undefined],
    [4n, 4, undefined],
    [5n, 5, undefined],
  ]);
});

test("a deposit's decision is due once its block is final and the ASP's delay old, whichever is later", () => {
  // 2 s blocks, final 64 blocks (128 s) behind: the delay is later
  const base = { latest: { number: 1064, timestamp: 10_128 }, final: { number: 1000, timestamp: 10_000 } };
  expect(decisionEstimate(1054, base.latest, base.final, 600)).toBe((10_108 + 600) * 1000);
  // 12 s blocks, final 64 blocks (768 s) behind: finality is later
  const l1 = { latest: { number: 1064, timestamp: 10_768 }, final: { number: 1000, timestamp: 10_000 } };
  expect(decisionEstimate(1064, l1.latest, l1.final, 600)).toBe((10_768 + 768) * 1000);
  expect(
    decisionEstimate(1000, { number: 1000, timestamp: 10_000 }, { number: 1000, timestamp: 10_000 }, 600),
  ).toBeNull();
});

test("a note counts once read on chain, or before that as the note of this device's operation under way", async () => {
  const c = ctx([chain(1n, async () => [{ chainId: 1n, tokenId: 1 }] as { tokenId: number }[])]);
  const note = { chainId: 1n, tokenId: 1, peer: null, atNs: null, noteHash: '0x01', watch: null } as const;
  const at = (index: number, more: object = {}) => ({
    index,
    tentative: false,
    spent: false,
    confirmed: true,
    ...more,
  });
  const change = (value: bigint, salt: `0x${string}`) => ({
    ...note,
    value,
    salt,
    source: 'self' as const,
    receipt: { kind: 'sent' as const, amount: 1n, fee: 1n, counterparty: '0x00' as const },
    found: [],
  });
  c.state.notes.push(
    change(2n, '0x0a'), // this device's payment under way: incoming
    change(3n, '0x0b'), // this device's payment that failed: never comes
    change(5n, '0x0c'), // another device's payment: counted once on chain
    { ...note, value: 7n, salt: '0x0d', source: 'received', found: [] }, // announced only: may never land
    { ...note, value: 11n, salt: '0x0e', source: 'received', found: [at(20, { tentative: true })] }, // in a block
    { ...note, value: 13n, salt: '0x0f', source: 'received', found: [at(21, { nullifiedAt: 4 })] }, // spent in a block
  );
  const spend = (id: string, status: 'pending' | 'failed', changes: `0x${string}`[]) => ({
    id,
    kind: 'send' as const,
    chainId: 1n,
    tokenId: 1,
    amount: 1n,
    createdMs: Date.now(),
    status,
    data: { to: { kind: 'public' as const, address: '0x00' as const }, maxFee: 1n, step: null, paid: 0n, changes },
  });
  c.state.ops.push(spend('under-way', 'pending', ['0x0a']), spend('failed', 'failed', ['0x0b']));
  const wallet = new (Wallet as unknown as new (ctx: Ctx) => Wallet)(c);
  await wallet.sync().catch(() => {}); // reads the tokens; the fakes fail the rest
  const [b] = wallet.balances();
  expect(b!.pending).toEqual([
    { amount: 2n, reason: 'incoming' },
    { amount: 11n, reason: 'awaiting-root' },
  ]);
  expect(wallet.coins().map((x) => x.id)).toEqual(['1:20']);
});

test('a note a sync finds counts once that sync has looked for its spend: not where it fails first, never where it was spent', async () => {
  await initCore();
  const fake = chain(1n, async () => [{ chainId: 1n, tokenId: 1 }] as { tokenId: number }[]);
  const c = { ...ctx([fake]), seed: new Uint8Array(32).fill(7), owners: new Map() } as Ctx;
  // paid to a receive code, which keyAll watches for here as storage would
  const code = { chainId: 1n, tokenId: 1, index: 3 };
  const note = (salt: `0x${string}`): NoteRecord => ({
    chainId: 1n,
    tokenId: 1,
    value: 5n,
    salt,
    source: 'received',
    peer: null,
    atNs: null,
    keyIndex: code.index,
    unkeyed: true,
    noteHash: '0x',
    watch: null,
    found: [],
  });
  // one spent long ago, as a new device finds it, and one not
  const [spent, kept] = [note('0x01'), note('0x02')];
  c.state.notes.push(spent, kept);
  keyAll(c, []);
  const tags = concat([spent.watch!.key, kept.watch!.key]);
  const fields = (n: NoteRecord) => [(0x789f26ebn << 32n) | 1n, BigInt(n.noteHash), 0n, 0n];
  let marks = (): Promise<Uint8Array> => down();
  Object.assign(fake.indexer, {
    status: async () => ({ commitments: 2, commitmentsFinal: 2, nullifiers: 1, nullifiersFinal: 1 }),
    commitments: async () => ({
      entries: hexToBytes(concat([...fields(spent), ...fields(kept)].map((v) => numberToHex(v, { size: 32 })))),
    }),
    page: async (list: string) =>
      list === 'tags'
        ? hexToBytes(tags)
        : list === 'marks'
          ? marks()
          : list === 'nullifiers'
            ? hexToBytes(core.nullifier(1n, 0n, owner(c, code)!.nullifyingKey).slice(0, 18) as `0x${string}`)
            : down(),
  });
  const wallet = new (Wallet as unknown as new (ctx: Ctx) => Wallet)(c);
  // the indexer fails as the sync turns to the nullifiers: both found, and neither counts
  await wallet.sync().catch(() => {});
  expect([...spent.found, ...kept.found]).toMatchObject([
    { index: 0, confirmed: true, unchecked: true },
    { index: 1, confirmed: true, unchecked: true },
  ]);
  expect(wallet.coins()).toEqual([]);
  marks = async () => new Uint8Array();
  await wallet.sync().catch(() => {});
  expect(spent.found).toMatchObject([{ index: 0, spent: true }]);
  expect(wallet.coins().map((x) => x.id)).toEqual(['1:1']);
});

test('a note is one coin: where a reorg moved it before its first place is final, at its final place, or else its latest', async () => {
  const c = ctx([chain(1n, async () => [{ chainId: 1n, tokenId: 1 }] as { tokenId: number }[])]);
  const at = (index: number, tentative: boolean) => ({ index, tentative, spent: false, confirmed: true });
  const note = { chainId: 1n, tokenId: 1, value: 5n, source: 'received', peer: null, atNs: null } as const;
  c.state.notes.push(
    { ...note, salt: '0x0a', noteHash: '0x0a', watch: null, found: [at(20, true), at(23, true)] },
    { ...note, salt: '0x0b', noteHash: '0x0b', watch: null, found: [at(21, true), at(22, false)] },
  );
  const wallet = new (Wallet as unknown as new (ctx: Ctx) => Wallet)(c);
  await wallet.sync().catch(() => {}); // reads the tokens; the fakes fail the rest
  expect(wallet.coins().map((x) => x.id)).toEqual(['1:23', '1:22']);
});

test('an input spent by a JoinSplit in a block is gone at once, and back if a reorg drops that JoinSplit', () => {
  const watch = { key: '0xaa' as const, from: 0, scannedTo: 10 };
  const f: Position = { index: 3, tentative: false, spent: false, nullifier: watch };
  applySpends([f], [{ key: '0xaa', position: 12, tentative: true }]);
  expect(unspent(f)).toBe(false);
  // the final nullifiers passed 12 without it
  watch.scannedTo = 14;
  applySpends([f], []);
  expect(unspent(f)).toBe(true);
  // in a block again, then final
  applySpends([f], [{ key: '0xaa', position: 15, tentative: true }]);
  watch.scannedTo = 16;
  applySpends([f], [{ key: '0xaa', position: 15, tentative: false }]);
  expect(f).toEqual({ index: 3, tentative: false, spent: true });
});

test("a note paid to a receive code waits for the code's key: watched once the seed derives it, not before", async () => {
  await initCore();
  const note: NoteRecord = {
    chainId: 1n,
    tokenId: 1,
    value: 5n,
    salt: '0x01',
    source: 'received',
    peer: null,
    atNs: null,
    keyIndex: 3,
    unkeyed: true,
    noteHash: '0x',
    watch: null,
    found: [],
  };
  const c = { ...ctx([]), seed: null, owners: new Map() } as Ctx;
  c.state.notes.push(note);
  keyAll(c, []);
  expect(note).toMatchObject({ unkeyed: true, noteHash: '0x', watch: null });
  c.seed = new Uint8Array(32).fill(7);
  keyAll(c, []);
  expect(note.unkeyed).toBeUndefined();
  expect(note.watch).not.toBeNull();
});

test('a payment waits on the soonest coins on their way that make up what it needs', () => {
  const min = 60_000;
  const coin = (amount: bigint, readyIn: number | null) =>
    ({ amount, readyBy: readyIn === null ? null : new Date(readyIn * min) }) as CoinInfo;
  const note = coin(3n, 5);
  const deposit = coin(5n, 9);
  expect(waitsOn([deposit, note], 2n)).toBe(note);
  expect(waitsOn([deposit, note], 6n)).toBe(deposit);
  // more than all of them: no wait ends it
  expect(waitsOn([deposit, note], 9n)).toBeNull();
  // one with no estimate comes last, and gives none where it is needed
  const unknown = coin(4n, null);
  expect(waitsOn([unknown, note], 2n)).toBe(note);
  expect(waitsOn([unknown, note], 6n)).toBeNull();
});
