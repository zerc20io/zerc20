// A point of sale with no key: it makes burn addresses for a merchant's wallet in the lane the wallet gave it
// (`Wallet.posKey`), records them there ahead of need, hands out one per sale, and follows what reaches each from what
// every wallet downloads. Stolen, it gives away which addresses are the merchant's, and nothing else: the merchant's
// wallet alone spends what they receive, merges it and withdraws it.

import { BURN_BLOCK, CanisterClient, MAX_POS_BLOCKS, lookupRecipient, writePosBlocks } from '@zerc20/storage-sdk';
import {
  type Address,
  type Hex,
  bytesToHex,
  getAddress,
  hexToBytes,
  isAddress,
  isHex,
  numberToHex,
  zeroAddress,
} from 'viem';
import { Chain, type Reach, type Token, fetchOf } from './chain.js';
import { type Burn, burnAddress, core, initCore } from './core.js';
import { WalletError, fail } from './errors.js';
import { type ChainConfig, type Network, checkNetwork } from './network.js';
import { scan } from './scan.js';
import { Asp, Indexer, type IndexerStatus } from './servers.js';
import { registerDeposit } from './services.js';
import type { DepositRecord } from './state.js';
import { applyHits, commitmentFields, commitmentTx, dropReorged, readDecisions, readTransfers } from './sync.js';

/** The longest a refill waits once a token's addresses run low: a write at a random time after the sale that drew
 * them down, not right after it, so that the write's time does not mark that sale. */
const REFILL_WITHIN_MS = 10 * 60_000;
/** How long what a pass over the chains read may go unsaved: lost, it is read from the chains again. */
const PASS_SAVED_WITHIN_MS = 60_000;

/** What a point of sale needs of a token: where it is, and its id for the burn addresses' derivation and tags. */
export type PosToken = Pick<Token, 'chainId' | 'tokenId' | 'address'>;

export interface Sale {
  /** Its burn address, which no other sale has. */
  id: Address;
  chainId: bigint;
  tokenId: number;
  token: Address;
  /** Paid in the token by a transfer here. */
  burnAddress: Address;
  /** Paid in the underlying asset here, which the deposit relayer then wraps into the burn address: once one is
   * registered (`registerDeposit`). */
  depositAddress: Address | null;
  /** What the deposit relayer takes out of each payment to `depositAddress`: ask for `amount` plus it. */
  depositFee: bigint | null;
  /** Where `depositAddress` sends back what it cannot wrap, and what a rage exit returns: the payer's, or the
   * merchant's. On chain for anyone to read once the address is first flushed. */
  refundTo: Address | null;
  /** What was asked, if anything: the point of sale's alone, never sent anywhere. */
  amount: bigint | null;
  createdMs: number;
}

export interface Payment {
  amount: bigint;
  /** Who paid the burn address: the payer, or for a payment through `depositAddress` the deposit address itself. */
  sender: Address;
  /** `confirming` until final (a reorg may still drop it), then `screening` until the ASP decides. `rejected` goes back
   * to its sender by the merchant's rage exit, or to `refundTo` from a deposit address. */
  state: 'confirming' | 'screening' | 'approved' | 'rejected';
  /** The transaction that paid the burn address, once the chain shows it: the payer's, or for a payment through
   * `depositAddress` the deposit relayer's. */
  txHash: Hex | null;
}

export interface SaleStatus {
  sale: Sale;
  payments: Payment[];
  /** What is final: every payment but the confirming ones. */
  received: bigint;
}

type Watched = Pick<DepositRecord, 'address' | 'watches' | 'found'>;

/** A token's addresses: made and recorded ahead of its sales. */
interface Pool {
  /** The next counter to derive. */
  next: number;
  /** Addresses made and not recorded yet, a block of counters `first..` each. */
  made: { first: number; burns: Burn[] }[];
  /** Addresses recorded in the lane that no sale has had. */
  ready: Address[];
}

interface Connection {
  merchant: Address;
  /** The zERC20 public key the merchant registered in storage, which its burn addresses are under. */
  publicKey: Hex;
  laneKey: Hex;
  /** Per chain, the lane's first slot not known to be taken. */
  slots: Record<string, number>;
  /** Per `chainId:tokenId`. */
  pools: Record<string, Pool>;
}

interface Saved {
  connection: Connection | null;
  sales: Sale[];
  /** What reached each sale's address, as a wallet's deposits keep it, by sale id. */
  seen: Record<Address, Watched>;
  /** Each payment's transaction, by `chainId:index`. */
  txs: Record<string, Hex>;
}

/** JSON with bigints, which `JSON` itself has no form for. */
const encode = (v: unknown) =>
  new TextEncoder().encode(JSON.stringify(v, (_, x: unknown) => (typeof x === 'bigint' ? { $n: `${x}` } : x)));
const decode = (b: Uint8Array): Saved =>
  JSON.parse(new TextDecoder().decode(b), (_, x: { $n?: string }) =>
    x && typeof x === 'object' && typeof x.$n === 'string' ? BigInt(x.$n) : x,
  ) as Saved;

const same = (a: string, b: string) => a.toLowerCase() === b.toLowerCase();
const pairOf = (token: Pick<PosToken, 'chainId' | 'tokenId'>) => `${token.chainId}:${token.tokenId}`;
const madeOf = (pool: Pool) => pool.made.length * BURN_BLOCK;

/** A chain's indexer as one pass reads it: its status, read once for every point of sale of the process that asks while
 * it is read, and the tag pages they read after it, each once. The points of sale of a server run their passes side by
 * side, so the indexer serves each page once a pass, not once a merchant; and a page read after the status is never
 * older than it, which the scan needs. */
interface Pass {
  status: IndexerStatus;
  tags: Map<number, Promise<Uint8Array>>;
}
const passes = new Map<string, Promise<Pass>>();

function passOf(indexer: Indexer): Promise<Pass> {
  let pass = passes.get(indexer.url);
  if (!pass) {
    const read = indexer.status().then((status) => ({ status, tags: new Map() }));
    const done = () => void (passes.get(indexer.url) === read && passes.delete(indexer.url));
    read.then(done, done);
    passes.set(indexer.url, (pass = read));
  }
  return pass;
}

export class PointOfSale {
  readonly #network: Network;
  /** How it reaches the chains and the servers, as a wallet does (`Reach`). */
  readonly #reach: Reach;
  readonly #fetch: typeof fetch;
  readonly #state: Saved;
  readonly #persist: { save(bytes: Uint8Array): Promise<void> };
  readonly #refillWithinMs: number;
  readonly #chains = new Map<bigint, Chain>();
  /** Sales by lowercase id. */
  readonly #byId = new Map<string, Sale>();
  /** The block each token is making ahead: one at a time, beside those made for a sale that waits. */
  readonly #making = new Map<string, Promise<void>>();
  /** The write each token has under way: one at a time. */
  readonly #recording = new Map<string, Promise<void>>();
  /** The write each token waits to do, at a random time. */
  readonly #timers = new Map<string, ReturnType<typeof setTimeout>>();
  /** How many sales of each token wait for an address. */
  readonly #waiting = new Map<string, number>();
  /** The searches of the lane connected now: another lane, or closing, stops them. */
  #searches = new AbortController();
  #storage: Promise<CanisterClient> | undefined;
  #queue: Promise<unknown> = Promise.resolve();
  #saving: Promise<unknown> = Promise.resolve();
  #passSave: ReturnType<typeof setTimeout> | undefined;
  #closed = false;

  private constructor(
    network: Network,
    reach: Reach,
    state: Saved,
    persist: { save(bytes: Uint8Array): Promise<void> },
    refillWithinMs: number,
  ) {
    this.#network = network;
    this.#reach = reach;
    this.#fetch = fetchOf(reach);
    this.#state = state;
    this.#persist = persist;
    this.#refillWithinMs = refillWithinMs;
    for (const s of state.sales) this.#byId.set(s.id.toLowerCase(), s);
  }

  /** Opens the point of sale's saved state. It keeps which addresses it handed out: lose that, and it may hand one out
   * twice. One state, one point of sale: two open on it would hand out the same addresses, so `close` the one before
   * opening it again. `transport` and `fetch` reach the chains and the servers, as `Wallet.open` takes them. */
  static async open(
    opts: {
      network: Network;
      persist: { load(): Promise<Uint8Array | null | undefined>; save(bytes: Uint8Array): Promise<void> };
      refillWithinMs?: number;
    } & Reach,
  ): Promise<PointOfSale> {
    checkNetwork(opts.network);
    await initCore();
    const saved = await opts.persist.load();
    const state: Saved = saved?.length ? decode(saved) : { connection: null, sales: [], seen: {}, txs: {} };
    // a state saved before addresses were made ahead
    for (const pool of Object.values(state.connection?.pools ?? {})) pool.made ??= [];
    const reach = { transport: opts.transport, fetch: opts.fetch };
    return new PointOfSale(opts.network, reach, state, opts.persist, opts.refillWithinMs ?? REFILL_WITHIN_MS);
  }

  /** Whether `merchant` registered for private payments in storage, as `connect` needs: a server may ask before it keeps
   * anything for an account, since storage admits registrations at a bounded rate and accounts cost nothing. */
  static async registered(network: Network, merchant: Address, reach: Reach = {}): Promise<boolean> {
    const client = await CanisterClient.connect(network.storage.host, network.storage.canisterId, fetchOf(reach));
    return (await lookupRecipient(client, hexToBytes(merchant))) !== null;
  }

  get connected(): boolean {
    return this.#state.connection !== null;
  }

  /** Takes the key `merchant`'s wallet made for it (`Wallet.posKey`), and the public key `merchant` registered in
   * storage, which every address it makes is under: whoever hands it a key cannot point sales at a key of its own. The
   * same key again changes nothing. Another one starts over in that lane; the sales made so far are still followed. */
  connect(merchant: Address, laneKey: Hex): Promise<void> {
    return this.#exclusive(async () => {
      if (!isAddress(merchant, { strict: false })) fail('invalid', `${String(merchant)} is not an address`);
      if (!isHex(laneKey) || laneKey.length !== 66) fail('invalid', 'the key is 32 bytes in hex');
      const c = this.#state.connection;
      if (c && same(c.merchant, merchant) && same(c.laneKey, laneKey)) return;
      const recipient = await lookupRecipient(await this.#client(), hexToBytes(merchant));
      if (!recipient) fail('invalid', `${merchant} has not registered for private payments: open its wallet once`);
      this.#stop();
      this.#state.connection = {
        merchant: getAddress(merchant),
        publicKey: bytesToHex(recipient!.publicKey),
        laneKey: laneKey.toLowerCase() as Hex,
        slots: {},
        pools: {},
      };
      await this.#save();
    });
  }

  /** Stops making and recording, then saves the state as it is: nothing is saved after, so the state may be opened
   * again. A sale under way then fails rather than hand out an address it could not save. */
  async close(): Promise<void> {
    this.#stop();
    const last = this.#save();
    this.#closed = true;
    await last;
  }

  /** Readies addresses of `token` ahead of its sales: an app calls it for each token it takes, as it starts and after
   * sales. Nothing happens while enough are ready, or a refill is under way or due. */
  prepare(token: PosToken): void {
    chainOf(this.#network, token.chainId);
    this.#supply(token);
  }

  /** How many addresses of `token` are recorded and wait for a sale. */
  ready(token: PosToken): number {
    return this.#state.connection?.pools[pairOf(token)]?.ready.length ?? 0;
  }

  /** A new sale of `token`, at an address no sale has had: one recorded ahead, or, when none is left, one recorded
   * now. With `via: 'deposit'` it also registers a deposit address in front of it (`registerDeposit`). */
  async next(opts: { via: 'burn' | 'deposit'; token: PosToken; amount?: bigint; refundTo?: Address }): Promise<Sale> {
    const { token } = opts;
    const c = chainOf(this.#network, token.chainId);
    this.#connection();
    const pair = pairOf(token);
    // counted from the start, so that the sales that come at once have their addresses made at once
    this.#waiting.set(pair, (this.#waiting.get(pair) ?? 0) + 1);
    let burnAddress: Address | undefined;
    let from: number;
    try {
      ({ commitmentsFinal: from } = await new Indexer(c.indexer, this.#fetch).status());
      while (!(burnAddress = this.#pool(token).ready.shift())) await this.#record(token);
    } finally {
      const left = this.#waiting.get(pair)! - 1;
      if (left) this.#waiting.set(pair, left);
      else this.#waiting.delete(pair);
    }
    // saved as taken before the deposit relayer is asked: a sale that fails half-way never hands it out again
    const sale: Sale = {
      id: burnAddress,
      chainId: token.chainId,
      tokenId: token.tokenId,
      token: token.address,
      burnAddress,
      depositAddress: null,
      depositFee: null,
      refundTo: null,
      amount: opts.amount ?? null,
      createdMs: Date.now(),
    };
    const watch = { key: tag(token.tokenId, burnAddress), from, scannedTo: from };
    this.#state.sales.push(sale);
    this.#byId.set(burnAddress.toLowerCase(), sale);
    this.#state.seen[burnAddress] = { address: burnAddress, watches: [{ tokenId: token.tokenId, watch }], found: [] };
    await this.#save();
    this.#supply(token);
    return opts.via === 'deposit' ? this.#exclusive(() => this.#register(sale, opts.refundTo)) : sale;
  }

  /** Registers a deposit address in front of sale `id`, for the underlying asset; the deposit relayer watches it for 7
   * days. What it cannot wrap (too little, another token) and a rage exit go back to `refundTo`, the merchant's
   * account if absent: name the payer's, so that neither the merchant's account is on chain nor a payment the ASP
   * rejects comes back to the merchant. A sale has one: asked again with the same `refundTo`, it is the same. */
  registerDeposit(id: Address, opts: { refundTo?: Address } = {}): Promise<Sale> {
    return this.#exclusive(() => this.#register(this.#sale(id), opts.refundTo));
  }

  async #register(sale: Sale, refundTo: Address | undefined): Promise<Sale> {
    const to = refundTo ?? this.#connection().merchant;
    if (!isAddress(to, { strict: false }) || same(to, zeroAddress))
      return fail('invalid', `${to} is not an address to refund to`);
    if (sale.depositAddress) {
      if (same(sale.refundTo!, to)) return sale;
      return fail('invalid', `sale ${sale.id} already has a deposit address, refunding to ${sale.refundTo}`);
    }
    const { depositAddress, fee } = await registerDeposit(this.#chain(sale.chainId), sale.token, sale.burnAddress, {
      address: to,
    });
    Object.assign(sale, { depositAddress, depositFee: fee, refundTo: to });
    await this.#save();
    return sale;
  }

  sales(): Sale[] {
    return [...this.#state.sales];
  }

  /** Sale `id`. */
  sale(id: Address): Sale {
    return this.#sale(id);
  }

  /** What reached each of sales `ids`: every transfer to its burn address, with where each stands. One pass per chain
   * for them all, reading only what every wallet downloads, so no server learns which addresses it asks about. A chain
   * that fails keeps what was read before, and its error is returned. */
  refresh(ids: Address[]): Promise<{ sales: SaleStatus[]; errors: unknown[] }> {
    return this.#exclusive(async () => {
      const sales = [...new Map(ids.map((id) => [id.toLowerCase(), this.#sale(id)])).values()];
      const errors: unknown[] = [];
      const chains = [...new Set(sales.map((s) => s.chainId))];
      await Promise.all(
        chains.map((chainId) =>
          this.#refreshChain(
            chainId,
            sales.filter((s) => s.chainId === chainId),
          ).catch((e: unknown) => void errors.push(e)),
        ),
      );
      this.#saveSoon();
      return { sales: sales.map((s) => this.#statusOf(s)), errors };
    });
  }

  /** What reached sale `id`, and how much is final. */
  async status(id: Address): Promise<SaleStatus> {
    const { sales, errors } = await this.refresh([id]);
    if (errors.length > 0) throw errors[0];
    return sales[0];
  }

  /** What reached sale `id` as of the last `refresh`, asking no server. */
  lastStatus(id: Address): SaleStatus {
    return this.#statusOf(this.#sale(id));
  }

  async #refreshChain(chainId: bigint, sales: Sale[]): Promise<void> {
    const c = chainOf(this.#network, chainId);
    const indexer = new Indexer(c.indexer, this.#fetch);
    const seen = sales.map((s) => this.#state.seen[s.id]);
    const { status, tags } = await passOf(indexer);
    const page = (p: number) => {
      let read = tags.get(p);
      if (!read) tags.set(p, (read = indexer.page('tags', p)));
      return read;
    };
    const watches = seen.flatMap((r) => r.watches.map((w) => w.watch));
    const hits = await scan(watches, 4, page, status.commitmentsFinal, status.commitments);
    applyHits([], seen, hits);
    dropReorged(seen, status.commitmentsFinal);
    await readTransfers(commitmentFields(indexer), seen);
    await readDecisions(new Asp(c.asp, this.#fetch), seen);
    // a final payment's transaction is kept; until then it is read again, as a reorg may move what sits at a position
    const txs = this.#state.txs;
    await Promise.all(
      seen
        .flatMap((r) => r.found)
        .map(async (f) => {
          const at = `${chainId}:${f.index}`;
          if (!f.tentative && txs[at]) return;
          const tx = await commitmentTx(this.#chain(chainId), indexer, f.index).catch(() => undefined);
          if (tx === undefined) return;
          if (tx?.hash) txs[at] = tx.hash;
          else delete txs[at];
        }),
    );
  }

  #statusOf(sale: Sale): SaleStatus {
    const payments = this.#state.seen[sale.id].found
      .filter((f) => f.amount !== null)
      .map((f): Payment => ({
        amount: f.amount!,
        sender: f.sender as Address,
        state: f.tentative ? 'confirming' : f.asp === null ? 'screening' : f.asp,
        txHash: this.#state.txs[`${sale.chainId}:${f.index}`] ?? null,
      }));
    const received = payments.filter((p) => p.state !== 'confirming').reduce((s, p) => s + p.amount, 0n);
    return { sale, payments, received };
  }

  /** How many addresses of a token to keep made, and recorded, ahead: twice its sales of the last `refillWithinMs`, so
   * that they last through the wait for a refill as sales pick up; in whole blocks, at least one, at most one write. */
  #low(pair: string): number {
    const sales = this.#state.sales;
    const since = Date.now() - this.#refillWithinMs;
    let recent = 0;
    // sales are kept in the order they were made
    for (let i = sales.length - 1; i >= 0 && sales[i].createdMs >= since; i--) if (pairOf(sales[i]) === pair) recent++;
    return BURN_BLOCK * Math.min(MAX_POS_BLOCKS, Math.max(1, Math.ceil((2 * recent) / BURN_BLOCK)));
  }

  /** Keeps `token` supplied. Its addresses are recorded once fewer than `#low` are ready: right away when none is,
   * otherwise at a random time within `refillWithinMs`, so that the time of a write does not mark the sale that drew
   * them down. They are made ahead, which shows nobody anything, until `#low` are made. */
  #supply(token: PosToken): void {
    if (!this.#state.connection || this.#closed) return;
    const pair = pairOf(token);
    const pool = this.#pool(token);
    const low = this.#low(pair);
    if (pool.ready.length < low && !this.#recording.has(pair) && !this.#timers.has(pair)) {
      // a write that fails is tried again by the next sale, which tells why
      if (pool.ready.length === 0) void this.#record(token).catch(() => undefined);
      else this.#later(token);
    }
    if (madeOf(pool) < low) void this.#ahead(token).catch(() => undefined);
  }

  /** The block `token` is making ahead, begun if there is none; the next follows while fewer than `#low` are made. */
  #ahead(token: PosToken): Promise<void> {
    const pair = pairOf(token);
    const running = this.#making.get(pair);
    if (running) return running;
    const run: Promise<void> = this.#make(token, false).finally(() => {
      if (this.#making.get(pair) === run) this.#making.delete(pair);
    });
    this.#making.set(pair, run);
    // one that fails is made again by the next sale, or the next pass's `prepare`
    run.then(
      () => this.#supply(token),
      () => undefined,
    );
    return run;
  }

  /** Makes `token`'s next block of addresses. Its counters are taken as it starts, so that blocks made side by side
   * never share one; a block that fails, or ends after the lane changed, leaves a gap in the counters, which no reader
   * minds. What is made is saved with the next save: lost, it is made again from the same counters, to the same
   * addresses, none of which a sale has had. */
  async #make(token: PosToken, urgent: boolean): Promise<void> {
    const c = this.#connection();
    const pool = this.#pool(token);
    const first = pool.next;
    pool.next += BURN_BLOCK;
    const laneKey = hexToBytes(c.laneKey);
    const signal = this.#searches.signal;
    const burns = await Promise.all(
      Array.from({ length: BURN_BLOCK }, (_, i) =>
        burnAddress(laneKey, token.chainId, token.tokenId, first + i, c.publicKey, { signal, urgent }),
      ),
    );
    if (this.#state.connection !== c) return;
    pool.made.push({ first, burns });
    this.#saveSoon();
  }

  /** Records made addresses of `token` in the lane, in one write, and readies them: as many blocks as the sales that
   * wait and the low mark ask for. One write at a time per token: a sale that finds none ready waits for the one under
   * way. A pool with none ready has the blocks its waiting sales need, one at least, made side by side and ahead of
   * every search made ahead, since the next sale waits for them. A timer that finds none made waits again: writing
   * right after the making would mark the sale that began it. */
  #record(token: PosToken): Promise<void> {
    const pair = pairOf(token);
    const running = this.#recording.get(pair);
    if (running) return running;
    clearTimeout(this.#timers.get(pair));
    this.#timers.delete(pair);
    const run: Promise<void> = (async () => {
      const c = this.#connection();
      const pool = this.#pool(token);
      const waiting = Math.ceil((this.#waiting.get(pair) ?? 0) / BURN_BLOCK);
      if (pool.ready.length === 0) {
        const short = Math.max(waiting, 1) - pool.made.length;
        await Promise.all(Array.from({ length: Math.max(0, short) }, () => this.#make(token, true)));
      } else if (pool.made.length === 0) return this.#later(token);
      if (this.#state.connection !== c) return;
      const short = Math.ceil((this.#low(pair) - pool.ready.length) / BURN_BLOCK);
      const blocks = pool.made.slice(0, Math.min(MAX_POS_BLOCKS, Math.max(waiting, short, 1)));
      if (!blocks.length) return;
      const chain = `${token.chainId}`;
      const slot = await writePosBlocks(
        await this.#client(),
        hexToBytes(c.laneKey),
        blocks.map((b) => ({
          chainId: token.chainId,
          tokenId: token.tokenId,
          first: b.first,
          salts: b.burns.map((burn) => hexToBytes(burn.salt)),
        })),
        c.slots[chain] ?? 0,
      );
      if (this.#state.connection !== c) return;
      c.slots[chain] = Math.max(c.slots[chain] ?? 0, slot);
      // what is made is only ever added to, after these
      pool.made.splice(0, blocks.length);
      pool.ready.push(...blocks.flatMap((b) => b.burns.map((burn) => burn.address)));
      await this.#save();
    })().finally(() => {
      if (this.#recording.get(pair) === run) this.#recording.delete(pair);
    });
    this.#recording.set(pair, run);
    // what was made ahead is recorded now: make the next, and record again if still short
    run.then(
      () => this.#supply(token),
      () => undefined,
    );
    return run;
  }

  /** Records `token`'s addresses at a random time within `refillWithinMs`. */
  #later(token: PosToken): void {
    const pair = pairOf(token);
    const timer = setTimeout(() => {
      this.#timers.delete(pair);
      void this.#record(token).catch(() => undefined);
    }, Math.random() * this.#refillWithinMs);
    (timer as { unref?: () => void }).unref?.(); // a process need not stay up for it
    this.#timers.set(pair, timer);
  }

  /** Stops the searches, timers and writes of the lane connected now. Those under way finish, and drop what they
   * bring, since the lane is no longer the one connected or the point of sale is closed. */
  #stop(): void {
    this.#searches.abort();
    this.#searches = new AbortController();
    for (const t of this.#timers.values()) clearTimeout(t);
    this.#timers.clear();
    this.#making.clear();
    this.#recording.clear();
  }

  #connection(): Connection {
    return this.#state.connection ?? fail('invalid', "not connected: connect the merchant's wallet first");
  }

  #pool(token: PosToken): Pool {
    return (this.#connection().pools[pairOf(token)] ??= { next: 0, made: [], ready: [] });
  }

  #sale(id: Address): Sale {
    return this.#byId.get(id.toLowerCase()) ?? fail('invalid', `no sale ${id}`);
  }

  #chain(chainId: bigint): Chain {
    let c = this.#chains.get(chainId);
    if (!c) this.#chains.set(chainId, (c = new Chain(chainOf(this.#network, chainId), this.#reach)));
    return c;
  }

  /** Storage, connected on first use: a point of sale that only follows its sales needs none. */
  #client(): Promise<CanisterClient> {
    const { host, canisterId } = this.#network.storage;
    return (this.#storage ??= CanisterClient.connect(host, canisterId, this.#fetch).catch((e: unknown) => {
      this.#storage = undefined;
      throw e;
    }));
  }

  /** Runs `f` after everything queued before it. */
  #exclusive<T>(f: () => Promise<T>): Promise<T> {
    const run = this.#queue.then(f);
    this.#queue = run.catch(() => undefined);
    return run;
  }

  /** Saves the state as it is when the save runs, after every save asked for before: an older state never lands last,
   * which would hand out again an address taken since. Closed, it saves nothing and fails. */
  #save(): Promise<void> {
    if (this.#closed) return Promise.reject(new WalletError('unavailable', 'the point of sale is closed'));
    clearTimeout(this.#passSave);
    this.#passSave = undefined;
    const run = this.#saving.then(() => this.#persist.save(encode(this.#state)));
    this.#saving = run.catch(() => undefined);
    return run;
  }

  /** Saves within `PASS_SAVED_WITHIN_MS`, for what can be read or made again: a pass's findings, addresses made. */
  // ponytail: the whole state on every save; split it once a merchant has some 10k sales
  #saveSoon(): void {
    if (this.#passSave || this.#closed) return;
    this.#passSave = setTimeout(() => void this.#save().catch(() => undefined), PASS_SAVED_WITHIN_MS);
    (this.#passSave as { unref?: () => void }).unref?.(); // a process need not stay up for it
  }
}

function chainOf(network: Network, chainId: bigint): ChainConfig {
  return network.chains.find((c) => c.chainId === chainId) ?? fail('invalid', `the network has no chain ${chainId}`);
}

const tag = (tokenId: number, address: Address) => numberToHex(core.transferTag(tokenId, address), { size: 4 });
