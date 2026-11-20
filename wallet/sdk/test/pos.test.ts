// A point of sale against fake servers: two chains whose token has one address, as CREATE3 deploys it, a deposit
// relayer that may lie, and sales asked for side by side. Storage and the burn address search are stood in for: the
// lane's writes are the storage SDK's own, and the search is pinned in wallet/core.

import {
  type Address,
  type Hex,
  concat,
  encodeAbiParameters,
  encodeEventTopics,
  getAddress,
  hexToBytes,
  numberToHex,
  parseAbiItem,
  http,
  parseAbiParameters,
  toHex,
  zeroAddress,
} from 'viem';
import { afterEach, beforeAll, beforeEach, expect, test, vi } from 'vitest';
import { Chain } from '../src/chain.js';
import { core, initCore } from '../src/core.js';
import { type ChainConfig, NITRO_ROOT_SHA256, type Network, PointOfSale, type PosToken } from '../src/index.js';

const addr = (n: number) => numberToHex(n, { size: 20 });
const word = (x: bigint) => numberToHex(x, { size: 32 });
const TOKEN: Address = '0x3b727B8A1671eD1E1631A007E683DbC5B6e48bbd';
const [MERCHANT, CUSTOMER, PREDICTED, FEE_RECIPIENT, STRANGER] = [
  addr(0x11),
  addr(0x22),
  addr(0x33),
  addr(0x44),
  addr(0x55),
];
const [KEY, OTHER_KEY] = [word(0x5150n), word(0x5151n)];
const TRANSFER_TAG = 0xddf252adn;

const storage = vi.hoisted(() => ({
  /** Each write's blocks, with the slot the write began looking from. */
  writes: [] as { laneKey: Hex; chainId: bigint; first: number; salts: number; from: number }[][],
  failNext: false,
  lookups: 0,
  /** The fetch each connection was made with. */
  fetches: [] as unknown[],
}));
/** Each address searched for, and whether something waited for it; how many are found, and how long one made ahead
 * takes. */
const searches = vi.hoisted(() => [] as { k: number; urgent: boolean }[]);
const search = vi.hoisted(() => ({ found: 0, aheadMs: 5 }));
vi.mock('@zerc20/storage-sdk', async (load) => ({
  ...(await load<typeof import('@zerc20/storage-sdk')>()),
  CanisterClient: { connect: async (_: string, __: string, fetch: unknown) => (storage.fetches.push(fetch), {}) },
  lookupRecipient: async (_: unknown, address: Uint8Array) => {
    storage.lookups++;
    return toHex(address) === MERCHANT ? { address, publicKey: new Uint8Array(32).fill(1) } : null;
  },
  writePosBlocks: async (
    _: unknown,
    laneKey: Uint8Array,
    blocks: { chainId: bigint; first: number; salts: Uint8Array[] }[],
    from: number,
  ) => {
    await Promise.resolve();
    if (storage.failNext) {
      storage.failNext = false;
      throw new Error('storage is down');
    }
    storage.writes.push(
      blocks.map((b) => ({ laneKey: toHex(laneKey), chainId: b.chainId, first: b.first, salts: b.salts.length, from })),
    );
    return from + blocks.length;
  },
}));
// the k-th address of a lane on a chain, made up: at once if something waits for it, a little later if made ahead
vi.mock('../src/core.js', async (load) => ({
  ...(await load<typeof import('../src/core.js')>()),
  burnAddress: async (
    laneKey: Uint8Array,
    chainId: bigint,
    _: number,
    k: number,
    __: Hex,
    o: { urgent?: boolean; signal?: AbortSignal },
  ) => {
    searches.push({ k, urgent: o.urgent ?? true });
    if (o.urgent === false) await new Promise((r) => setTimeout(r, search.aheadMs));
    // as a search stops once its point of sale closes
    o.signal?.throwIfAborted();
    search.found++;
    return {
      salt: word(BigInt(k)),
      address: addr(Number(chainId % 1000n) * 100_000 + (laneKey[31]! % 2) * 10_000 + k),
    };
  },
}));

/** One chain's servers and RPC, all on one port. */
interface Fake {
  /** Transfers to burn addresses, by commitment index; all final. */
  payments: { to: Address; sender: Address; amount: bigint; approved: boolean }[];
  relayerGives: Address;
  predicts: Address;
  code: Hex;
  asked: string[];
}
const fakes = new Map<string, Fake>();
const fake = (): Fake => ({ payments: [], relayerGives: PREDICTED, predicts: PREDICTED, code: '0x', asked: [] });

const chain = (chainId: bigint, port: number): ChainConfig => {
  const at = (path: string) => `http://127.0.0.1:${port}/${path}`;
  return {
    chainId,
    rpcUrls: [at('rpc')],
    verifier: addr(1),
    depositAddressFactory: addr(2),
    indexer: at('indexer'),
    asp: at('asp'),
    attester: at('attester'),
    attesterTrust:
      chainId === 31337n ? { development: true } : { pcr0: 'ab'.repeat(48), rootSha256: NITRO_ROOT_SHA256 },
    transactRelayer: at('relayer'),
    depositRelayer: at('deposits'),
  };
};
const circuit = { wasm: 'file:///j.wasm', zkey: 'file:///j.zkey', wasmSha256: '', zkeySha256: '' };
const [A, B] = [chain(31337n, 7001), chain(84532n, 7002)];
const network: Network = {
  name: 'test',
  storage: { host: 'http://127.0.0.1:7000', canisterId: 'aaaaa-aa' },
  circuits: { joinsplit: circuit, rageexit: circuit },
  chains: [A, B],
};
const on = (c: ChainConfig): PosToken => ({ chainId: c.chainId, tokenId: 1, address: TOKEN });

const committed = parseAbiItem('event Committed(uint64 indexed index, uint256[4] fields)');
const txOf = (index: number) => word(0xbeef00n + BigInt(index));
const json = (v: unknown) => new Response(JSON.stringify(v));
const bytes = (h: Hex) => new Response(new Uint8Array(hexToBytes(h)));

async function serve(input: string | URL | Request, init?: RequestInit): Promise<Response> {
  const url = new URL(typeof input === 'string' ? input : input instanceof URL ? input.href : input.url);
  const f = fakes.get(url.port)!;
  f.asked.push(url.pathname);
  const n = f.payments.length;
  switch (url.pathname) {
    case '/indexer/status':
      return json({
        commitments: n,
        commitments_final: n,
        nullifiers: 0,
        nullifiers_final: 0,
        latest_root: null,
        mismatch: null,
        indexer: { final_block: null },
      });
    case '/indexer/tags/0':
      return bytes(concat(f.payments.map((p) => numberToHex(core.transferTag(1, p.to), { size: 4 }))));
    case '/indexer/commitments/0': {
      const fields = f.payments.map((p) =>
        concat([word((TRANSFER_TAG << 32n) | 1n), word(BigInt(p.sender)), word(BigInt(p.to)), word(p.amount)]),
      );
      return bytes(concat([word(0n), ...fields]));
    }
    case '/indexer/blocks/0':
      return bytes(concat(['0x', ...f.payments.map((_, i) => numberToHex(i + 1, { size: 8 }))]));
    case '/asp/status':
      return json({ decided: n, latest_root: null, delay_secs: 0 });
    case '/asp/bitmap/0': {
      const bits = new Uint8Array(512);
      f.payments.forEach((p, i) => p.approved && (bits[i >> 3]! |= 1 << (i & 7)));
      return new Response(bits);
    }
    case '/deposits/register':
      return json({ depositAddress: f.relayerGives, feeRecipient: FEE_RECIPIENT, fee: toHex(100n) });
    case '/rpc': {
      const { id, method, params } = JSON.parse(init!.body as string) as {
        id: number;
        method: string;
        params: [{ topics: Hex[] }];
      };
      if (method === 'eth_getLogs') {
        const index = Number(BigInt(params[0].topics[1]!));
        const topics = encodeEventTopics({ abi: [committed], eventName: 'Committed', args: { index: BigInt(index) } });
        const log = {
          address: f.predicts,
          topics,
          data: encodeAbiParameters([{ type: 'uint256[4]' }], [[0n, 0n, 0n, 0n]]),
        };
        const at = {
          blockHash: word(1n),
          blockNumber: toHex(index + 1),
          logIndex: '0x0',
          transactionIndex: '0x0',
          removed: false,
        };
        return json({ jsonrpc: '2.0', id, result: [{ ...log, ...at, transactionHash: txOf(index) }] });
      }
      const result =
        method === 'eth_call'
          ? encodeAbiParameters([{ type: 'address' }], [f.predicts])
          : method === 'eth_getCode'
            ? f.code
            : null;
      return json({ jsonrpc: '2.0', id, result });
    }
  }
  return new Response('not found', { status: 404 });
}

beforeAll(async () => {
  await initCore();
  vi.stubGlobal('fetch', serve);
});

beforeEach(() => {
  storage.writes.length = 0;
  searches.length = 0;
  Object.assign(search, { found: 0, aheadMs: 5 });
  storage.lookups = 0;
  fakes.set('7001', fake());
  fakes.set('7002', fake());
});

/** Every point of sale a test opens, closed after it so that none makes addresses into the next. */
const opened: PointOfSale[] = [];
const open = async (o: Parameters<typeof PointOfSale.open>[0]) => {
  const pos = await PointOfSale.open(o);
  opened.push(pos);
  return pos;
};
afterEach(async () => {
  await Promise.all(opened.splice(0).map((pos) => pos.close().catch(() => undefined)));
});

const memory = () => {
  const box = { saved: null as Uint8Array | null };
  return { box, persist: { load: async () => box.saved, save: async (b: Uint8Array) => void (box.saved = b) } };
};
/** A point of sale connected to the merchant, refilling only when a test lets it. */
const connected = async (persist = memory().persist, refillWithinMs = 3_600_000) => {
  const pos = await open({ network, persist, refillWithinMs });
  await pos.connect(MERCHANT, KEY);
  return pos;
};

test("it connects to a registered merchant's key, once per key", async () => {
  const pos = await open({ network, persist: memory().persist });
  expect(pos.connected).toBe(false);
  await expect(pos.next({ via: 'burn', token: on(A) })).rejects.toMatchObject({ code: 'invalid' });
  await expect(pos.connect(STRANGER, KEY)).rejects.toMatchObject({ code: 'invalid' });
  await expect(pos.connect(MERCHANT, '0x1234')).rejects.toMatchObject({ code: 'invalid' });
  await pos.connect(MERCHANT, KEY);
  await pos.connect(MERCHANT, KEY);
  expect([pos.connected, storage.lookups]).toEqual([true, 2]);
});

test('sales at once have the blocks they need made side by side, recorded in one write before any is handed out', async () => {
  const pos = await connected();
  const sales = await Promise.all([1, 2, 3, 4, 5, 6, 7].map(() => pos.next({ via: 'burn', token: on(A) })));
  expect(new Set(sales.map((s) => s.id)).size).toBe(7);
  expect(storage.writes).toEqual([
    [
      { laneKey: KEY, chainId: A.chainId, first: 0, salts: 6, from: 0 },
      { laneKey: KEY, chainId: A.chainId, first: 6, salts: 6, from: 0 },
    ],
  ]);
  expect(sales.map((s) => s.tokenId)).toEqual(Array(7).fill(1));
});

test('a sale that finds none ready waits only for the write: as many as its token sold lately are made ahead', async () => {
  const pos = await connected();
  pos.prepare(on(A));
  // one block recorded for the first sales, and one made ahead of them
  await vi.waitFor(() => expect([pos.ready(on(A)), searches.length]).toEqual([6, 12]));
  for (let i = 0; i < 6; i++) await pos.next({ via: 'burn', token: on(A) });
  // six sales lately: twice that made ahead
  await vi.waitFor(() => expect(search.found).toBe(18));
  await pos.next({ via: 'burn', token: on(A) });
  expect(storage.writes.map((w) => w.map((b) => b.first))).toEqual([[0], [6, 12]]);
  // the empty pool's first block alone was made for a sale
  expect(searches.filter((s) => s.urgent).map((s) => s.k)).toEqual([0, 1, 2, 3, 4, 5]);
});

test('a pool with none ready has its next block made first, not after the one made ahead', async () => {
  // what is made ahead never ends here
  search.aheadMs = 60_000;
  const pos = await connected();
  pos.prepare(on(A));
  await vi.waitFor(() => expect(pos.ready(on(A))).toBe(6));
  for (let i = 0; i < 7; i++) await pos.next({ via: 'burn', token: on(A) });
  expect(storage.writes.map((w) => w.map((b) => b.first))).toEqual([[0], [12]]);
  expect(searches.filter((s) => s.urgent).map((s) => s.k)).toEqual([0, 1, 2, 3, 4, 5, 12, 13, 14, 15, 16, 17]);
});

test('blocks made ahead and for sales that wait never share a counter', async () => {
  const pos = await connected();
  pos.prepare(on(A));
  const sales = await Promise.all(Array.from({ length: 13 }, () => pos.next({ via: 'burn', token: on(A) })));
  expect(new Set(sales.map((s) => s.id)).size).toBe(13);
  const firsts = storage.writes.flat().map((b) => b.first);
  expect(new Set(firsts).size).toBe(firsts.length);
  expect(new Set(searches.map((s) => s.k)).size).toBe(searches.length);
});

test('a low pool refills on its own, after a while', async () => {
  const pos = await connected(memory().persist, 0);
  expect(pos.ready(on(A))).toBe(0);
  pos.prepare(on(A));
  await vi.waitFor(() => expect(pos.ready(on(A))).toBe(6));
  expect(storage.writes).toHaveLength(1);
  await pos.next({ via: 'burn', token: on(A) });
  expect(storage.writes).toHaveLength(1);
  await vi.waitFor(() => expect(storage.writes.map((w) => w.map((b) => b.first))).toEqual([[0], [6]]));
});

test('a refill that fails changes nothing, and the next sale tries again', async () => {
  const pos = await connected();
  storage.failNext = true;
  await expect(pos.next({ via: 'burn', token: on(A) })).rejects.toThrow('storage is down');
  const sale = await pos.next({ via: 'burn', token: on(A) });
  expect(storage.writes.flat().map((b) => b.first)).toEqual([0]);
  expect(pos.sales()).toEqual([sale]);
});

test('closed, it saves nothing more, and a sale under way fails', async () => {
  const { box, persist } = memory();
  const pos = await connected(persist);
  const sale = await pos.next({ via: 'burn', token: on(A) });
  await pos.close();
  const saved = box.saved;
  await expect(pos.next({ via: 'burn', token: on(A) })).rejects.toMatchObject({ code: 'unavailable' });
  expect(box.saved).toBe(saved);
  expect((await open({ network, persist })).sales()).toEqual([sale]);
});

test('a state saved before addresses were made ahead opens and sells on', async () => {
  const { box, persist } = memory();
  const pos = await connected(persist);
  await pos.next({ via: 'burn', token: on(A) });
  await pos.close();
  const old = JSON.parse(new TextDecoder().decode(box.saved!)) as { connection: { pools: Record<string, object> } };
  for (const pool of Object.values(old.connection.pools)) delete (pool as { made?: unknown }).made;
  box.saved = new TextEncoder().encode(JSON.stringify(old));
  const again = await open({ network, persist });
  for (let i = 0; i < 6; i++) await again.next({ via: 'burn', token: on(A) });
  expect(new Set(again.sales().map((s) => s.id)).size).toBe(7);
});

test('the same key keeps its addresses, another starts over in its lane, and the saved state opens again', async () => {
  const { box, persist } = memory();
  const pos = await connected(persist);
  const first = await pos.next({ via: 'burn', token: on(A) });
  await pos.connect(MERCHANT, KEY);
  await pos.next({ via: 'burn', token: on(A) });
  expect(storage.writes).toHaveLength(1);

  const again = await open({ network, persist: { load: async () => box.saved, save: async () => {} } });
  expect([again.connected, again.sales().length, again.sales()[0]!.chainId]).toEqual([true, 2, A.chainId]);
  const third = await again.next({ via: 'burn', token: on(A) });
  expect(storage.writes).toHaveLength(1);

  await again.connect(MERCHANT, OTHER_KEY);
  const other = await again.next({ via: 'burn', token: on(A) });
  expect(storage.writes.at(-1)).toEqual([{ laneKey: OTHER_KEY, chainId: A.chainId, first: 0, salts: 6, from: 0 }]);
  expect(new Set([first.id, third.id, other.id]).size).toBe(3);
});

test('a token with one address on two chains: the sale is on the chain asked for, and is followed there alone', async () => {
  const pos = await connected();
  const sale = await pos.next({ via: 'burn', token: on(B), amount: 500n });
  expect([sale.chainId, storage.writes[0]![0]!.chainId]).toEqual([B.chainId, B.chainId]);

  const [a, b] = [fakes.get('7001')!, fakes.get('7002')!];
  b.payments.push({ to: sale.burnAddress, sender: CUSTOMER, amount: 500n, approved: true });
  a.asked.length = 0;
  const { sales, errors } = await pos.refresh([sale.id]);
  expect(errors).toEqual([]);
  expect(sales[0]!.payments).toEqual([{ amount: 500n, sender: CUSTOMER, state: 'approved', txHash: txOf(0) }]);
  expect(sales[0]!.received).toBe(500n);
  expect(a.asked).toEqual([]);
  // a final payment's transaction is read once
  b.asked.length = 0;
  await pos.refresh([sale.id]);
  expect(b.asked.filter((p) => p === '/indexer/blocks/0')).toEqual([]);
});

test('it reaches the chains and the servers only as it is told to, as a wallet does', async () => {
  // the platform's fetch is not to be called: an app routing through Tor would leak there
  const direct: string[] = [];
  vi.stubGlobal('fetch', (input: string | URL | Request) => {
    direct.push(String(input));
    return Promise.reject(new Error('reached directly'));
  });
  const told: string[] = [];
  const fetch = (input: string | URL | Request, init?: RequestInit) => (told.push(String(input)), serve(input, init));
  try {
    const transport = (c: ChainConfig) => http(c.rpcUrls[0], { fetchFn: fetch });
    const pos = await open({ network, persist: memory().persist, refillWithinMs: 3_600_000, transport, fetch });
    await pos.connect(MERCHANT, KEY);
    const sale = await pos.next({ via: 'burn', token: on(A), amount: 500n });
    fakes.get('7001')!.payments.push({ to: sale.burnAddress, sender: CUSTOMER, amount: 500n, approved: true });
    const { sales, errors } = await pos.refresh([sale.id]);
    expect(errors).toEqual([]);
    expect(sales[0]!.payments[0]!.txHash).toBe(txOf(0)); // read through the transport
    expect(await PointOfSale.registered(network, MERCHANT, { fetch })).toBe(true);
    expect(direct).toEqual([]);
    expect(new Set(told.map((u) => new URL(u).pathname.split('/')[1]))).toEqual(new Set(['indexer', 'asp', 'rpc']));
    // storage, connected for the lane and for `registered`, asks through it too
    for (const f of storage.fetches.slice(-2) as (typeof globalThis.fetch)[]) await f('http://127.0.0.1:7001/storage');
    expect(told.filter((u) => u.endsWith('/storage'))).toHaveLength(2);
    expect(direct).toEqual([]);
  } finally {
    vi.stubGlobal('fetch', serve);
  }
});

test("a deposit address is the factory's, refunds to whom the sale names, and is one per sale", async () => {
  const pos = await connected();
  const a = fakes.get('7001')!;
  a.relayerGives = addr(0x66);
  await expect(pos.next({ via: 'deposit', token: on(A) })).rejects.toMatchObject({ code: 'indexer-mismatch' });
  // the address it was for is spent all the same
  expect(pos.sales()).toHaveLength(1);

  a.relayerGives = PREDICTED;
  const merchant = await pos.next({ via: 'deposit', token: on(A) });
  expect([merchant.depositAddress, merchant.depositFee, merchant.refundTo]).toEqual([PREDICTED, 100n, MERCHANT]);
  const sale = await pos.next({ via: 'burn', token: on(A) });
  expect(sale.depositAddress).toBeNull();
  expect((await pos.registerDeposit(sale.id, { refundTo: CUSTOMER })).refundTo).toBe(CUSTOMER);
  expect((await pos.registerDeposit(sale.id, { refundTo: CUSTOMER })).depositAddress).toBe(PREDICTED);
  await expect(pos.registerDeposit(sale.id, { refundTo: MERCHANT })).rejects.toMatchObject({ code: 'invalid' });
  await expect(pos.registerDeposit(merchant.id, { refundTo: addr(0) })).rejects.toMatchObject({ code: 'invalid' });

  // the relayer writes it in lower case; it comes back checksummed, as the factory's is
  const mixed = getAddress(`0x${'ab'.repeat(20)}`);
  [a.predicts, a.relayerGives] = [mixed, mixed.toLowerCase() as Address];
  expect((await pos.next({ via: 'deposit', token: on(A) })).depositAddress).toBe(mixed);
});

test("a deposit address's refund is read from its code, and only for the factory's address", async () => {
  const a = fakes.get('7001')!;
  const burn = addr(0x77);
  const code = (refundAddress: Address, refundSigner: Address) =>
    concat([
      '0x363d3d373d3d3d363d73',
      addr(0x88),
      '0x5af43d82803e903d91602b57fd5bf3',
      encodeAbiParameters(parseAbiParameters('address, address, address, address, address, uint256, address, uint16'), [
        TOKEN,
        burn,
        refundAddress,
        refundSigner,
        FEE_RECIPIENT,
        100n,
        addr(0x55),
        30,
      ]),
    ]);
  const c = new Chain(A);
  a.code = code(CUSTOMER, zeroAddress);
  expect(await c.depositAddressRefund(PREDICTED, TOKEN, burn)).toEqual({ address: CUSTOMER });
  expect(await c.depositAddressRefund(addr(0x99), TOKEN, burn)).toBeNull();
  a.code = code(zeroAddress, addr(0x66));
  expect(await c.depositAddressRefund(PREDICTED, TOKEN, burn)).toEqual({ signer: addr(0x66) });
  // the factory takes one of the two, never both or neither
  a.code = code(CUSTOMER, addr(0x66));
  expect(await c.depositAddressRefund(PREDICTED, TOKEN, burn)).toBeNull();
  a.code = code(zeroAddress, zeroAddress);
  expect(await c.depositAddressRefund(PREDICTED, TOKEN, burn)).toBeNull();
  a.code = '0x';
  expect(await c.depositAddressRefund(PREDICTED, TOKEN, burn)).toBeNull();
});
