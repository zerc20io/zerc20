// The wallet's protocol computations (wallet/core: the Rust the circuits, the attester and the backend share,
// compiled to wasm). `initCore` loads it once; everything else here waits for it.

import { type Address, type Hex, bytesToHex } from 'viem';
import init, * as wasm from '../wasm/zerc20_wallet_core.js';

let ready: Promise<unknown> | undefined;

/** Loads the wasm. A browser (or a bundler) fetches the file next to this module; Node reads it from disk. */
export function initCore(): Promise<void> {
  ready ??= (async () => {
    const url = new URL('../wasm/zerc20_wallet_core_bg.wasm', import.meta.url);
    if (url.protocol !== 'file:') return init({ module_or_path: url });
    // a variable, so that bundlers for the browser leave Node's module alone
    const fs = 'node:fs/promises';
    const { readFile } = (await import(/* @vite-ignore */ fs)) as { readFile: (path: URL) => Promise<Uint8Array> };
    return init({ module_or_path: await readFile(url) });
  })();
  return ready.then(() => undefined);
}

export const core = wasm;

export interface Burn {
  salt: Hex;
  address: Address;
}

/** The `index`-th burn address of `publicKey` on a chain and token, and its salt, from `burnKey`: the wallet's own burn
 * key, or a point of sale's (`wallet_keys::derive_burn_address`). About 2^16 hashes, spread over the device's cores
 * (Web Workers in a browser, worker threads in Node) so that the app stays responsive; `signal` stops the search. One
 * that nobody waits for, made ahead, is `urgent: false`: it gives way to those someone waits for. */
export const burnAddress = (
  burnKey: Uint8Array,
  chainId: bigint,
  tokenId: number,
  index: number,
  publicKey: Hex,
  opts: { signal?: AbortSignal; urgent?: boolean } = {},
): Promise<Burn> => search({ burnKey, chainId, tokenId, index, publicKey }, opts.urgent ?? true, opts.signal);

/** A burn address of someone else's `publicKey` (one they published to be paid), with a random salt that has the proof
 * of work: about 2^16 hashes too, searched the same way. Only who holds the salt finds it: the payer, and the owner once
 * told (`planSend` with `burn`). */
export const burnAddressFor = (chainId: bigint, publicKey: Hex, signal?: AbortSignal): Promise<Burn> =>
  search({ chainId, publicKey }, true, signal);

export type BurnSearch =
  | { burnKey: Uint8Array; chainId: bigint; tokenId: number; index: number; publicKey: Hex }
  | { chainId: bigint; publicKey: Hex };

/** Counters per block: about 20 ms of hashing on a laptop, a few times that on a phone. */
const BLOCK = 512;

/** A block of a search: its salt counters `from..=to`, or as many random salts for someone else's key. */
export interface BurnBlock {
  search: BurnSearch;
  from: number;
  to: number;
}

export type BurnAnswer = { burn: Burn | null } | { error: string };

/** What a block asks of the protocol code: `burnBlock`'s arguments, or `burnBlockFor`'s. */
export type BurnCall =
  | { burnKey: Uint8Array; chainId: bigint; tokenId: number; index: number; publicKey: Hex; from: number; to: number }
  | { chainId: bigint; publicKey: Hex; start: Hex; count: number };

/** A block's call. Its salts count up from a start: one the burn key derives, or for someone else's key a random one
 * below 2^253, so that every salt is a field element. */
export function blockCall({ search: s, from, to }: BurnBlock): BurnCall {
  if ('burnKey' in s) return { ...s, from, to };
  const start = crypto.getRandomValues(new Uint8Array(32));
  start[0] = start[0] & 0x1f;
  return { chainId: s.chainId, publicKey: s.publicKey, start: bytesToHex(start), count: to - from + 1 };
}

/** The address a block holds, if any. */
export function runBlock(b: BurnBlock): Burn | null {
  const c = blockCall(b);
  const burn: unknown =
    'burnKey' in c
      ? core.burnBlock(c.burnKey, c.chainId, c.tokenId, c.index, c.publicKey, c.from, c.to)
      : core.burnBlockFor(c.chainId, c.publicKey, c.start, c.count);
  return (burn as Burn | undefined) ?? null;
}

type Outcome = { burn: Burn } | { error: unknown };

/** A search in progress, in blocks `0, 1, …` of `BLOCK` counters. From a burn key, the address is the first block's
 * hit, so that every device derives the same one; for someone else's key, it is the first found. */
export class Search {
  readonly s: BurnSearch;
  readonly #settle: (r: Outcome) => void;
  /** From a burn key: the address is the first block's hit, not the first found. */
  readonly #derived: boolean;
  #settled = false;
  #next = 0;
  /** Blocks a worker took and died with, handed out again before any other. */
  #dropped: number[] = [];
  /** What the finished blocks from `#checked` on hold: every block below it holds none. */
  #found = new Map<number, Burn | null>();
  #checked = 0;
  /** The lowest block known to hold an address: no block above it is needed. */
  #lowest = Infinity;

  constructor(s: BurnSearch, settle: (r: Outcome) => void) {
    this.s = s;
    this.#settle = settle;
    this.#derived = 'burnKey' in s;
  }

  take(): number | undefined {
    if (this.#settled) return undefined;
    if (this.#dropped.length) return this.#dropped.shift();
    return this.#next < this.#lowest ? this.#next++ : undefined;
  }

  drop(block: number) {
    this.#dropped.unshift(block);
  }

  finish(block: number, burn: Burn | null) {
    if (this.#settled) return;
    if (!this.#derived) {
      if (burn) this.#end({ burn });
      return;
    }
    this.#found.set(block, burn);
    if (burn) this.#lowest = Math.min(this.#lowest, block);
    for (let found; (found = this.#found.get(this.#checked)) !== undefined; this.#checked++) {
      if (found) return this.#end({ burn: found });
      this.#found.delete(this.#checked);
    }
  }

  fail(error: unknown) {
    if (!this.#settled) this.#end({ error });
  }

  #end(r: Outcome) {
    this.#settled = true;
    this.#settle(r);
  }
}

/** A worker running one block at a time. */
interface Thread {
  job: Job | null;
  /** Whether it ever answered: one that dies before it does never ran. */
  answered: boolean;
  send(b: BurnBlock): void;
  stop(): void;
  /** In Node, a thread keeps the process up while it works, and only then. */
  busy(working: boolean): void;
}

type Job = { search: Search; block: number };

/** What this module takes from Node's worker threads, typed here so that the package needs no Node types. */
type NodeWorker = new (url: URL) => {
  on(event: 'message', f: (a: BurnAnswer) => void): void;
  on(event: 'error' | 'exit' | 'messageerror', f: () => void): void;
  postMessage(b: BurnBlock): void;
  ref(): void;
  unref(): void;
  terminate(): Promise<number>;
};

/** Searches in progress by owner (the burn key, or the key paid): those someone waits for, and those made ahead. Each
 * owner in turn gets a block of its oldest search that has one, so that one owner's many searches hold up no other's,
 * and each address it waits for comes as soon as its cores allow. */
// ponytail: fair per owner, so per point of sale; a merchant opening many accounts gets many turns, so cap each
// merchant's sales if that happens
const queues = { urgent: new Map<string, Search[]>(), later: new Map<string, Search[]>() };
/** One block in this many goes to the searches made ahead while some are waited for: a flood of urgent searches slows
 * the making ahead, which keeps everyone else's sales from waiting, but does not stop it. */
const LATER_EVERY = 4;
/** Urgent blocks handed out in a row. */
let urgentRun = 0;
let threads: Thread[] | null = null;
let starting = false;
/** Workers do not run here (a page whose CSP forbids them, a bundler that left burnWorker.js out, tests run from
 * source): blocks run on this thread instead. */
let here = false;
let runningHere = false;
let idle: ReturnType<typeof setTimeout> | undefined;
/** An idle pool stops after this long, freeing a wasm instance per core. */
const IDLE_MS = 30_000;

async function search(s: BurnSearch, urgent: boolean, signal?: AbortSignal): Promise<Burn> {
  await initCore();
  signal?.throwIfAborted();
  const queue = urgent ? queues.urgent : queues.later;
  const owner = 'burnKey' in s ? bytesToHex(s.burnKey) : s.publicKey;
  return new Promise((resolve, reject) => {
    const abort = () => one.fail(signal!.reason);
    const one = new Search(s, (r) => {
      signal?.removeEventListener('abort', abort);
      const mine = queue.get(owner)!;
      mine.splice(mine.indexOf(one), 1);
      if (!mine.length) queue.delete(owner);
      if ('burn' in r) resolve(r.burn);
      else reject(r.error);
    });
    signal?.addEventListener('abort', abort, { once: true });
    const mine = queue.get(owner);
    if (mine) mine.push(one);
    else queue.set(owner, [one]);
    dispatch();
  });
}

function nextJob(): Job | null {
  const order = urgentRun >= LATER_EVERY - 1 ? [queues.later, queues.urgent] : [queues.urgent, queues.later];
  for (const queue of order) {
    const job = takeFrom(queue);
    if (!job) continue;
    urgentRun = queue === queues.urgent ? urgentRun + 1 : 0;
    return job;
  }
  return null;
}

/** A block of the first owner in line that has one, from its oldest search that does; that owner then goes to the back
 * of the line. */
function takeFrom(queue: Map<string, Search[]>): Job | null {
  for (const [owner, mine] of queue) {
    for (const search of mine) {
      const block = search.take();
      if (block === undefined) continue;
      queue.delete(owner);
      queue.set(owner, mine);
      return { search, block };
    }
  }
  return null;
}

const blockOf = ({ search, block }: Job): BurnBlock => ({
  search: search.s,
  from: block * BLOCK,
  to: block * BLOCK + BLOCK - 1,
});

function deliver({ search, block }: Job, a: BurnAnswer) {
  if ('error' in a) search.fail(new Error(a.error));
  else search.finish(block, a.burn);
}

/** Runs blocks somewhere other than this module's wasm: a server's native process, say. */
export interface BurnRunner {
  /** How many blocks it runs at once. */
  slots: number;
  run(call: BurnCall): Promise<Burn | null>;
}

let runner: BurnRunner | null = null;
/** Blocks the runner has and has not answered. */
const onRunner = new Set<Job>();

/** Runs every block from now on on `r`, or with null in this module's wasm again. The blocks the runner had are handed
 * out again, and what it answers for them later is dropped. */
export function runBurnsOn(r: BurnRunner | null): void {
  for (const job of onRunner) job.search.drop(job.block);
  onRunner.clear();
  runner = r;
  dispatch();
}

function feed(r: BurnRunner) {
  while (onRunner.size < r.slots) {
    const job = nextJob();
    if (!job) return;
    onRunner.add(job);
    void r
      .run(blockCall(blockOf(job)))
      .then(
        (burn): BurnAnswer => ({ burn }),
        (e: unknown): BurnAnswer => ({ error: e instanceof Error ? e.message : String(e) }),
      )
      .then((a) => {
        if (!onRunner.delete(job)) return; // handed out again when the runner was taken away
        deliver(job, a);
        dispatch();
      });
  }
}

/** Hands blocks to the runner, or to idle threads, starting the pool if it is not running. */
function dispatch() {
  clearTimeout(idle);
  if (runner) return feed(runner);
  if (here) return void runHere();
  if (!threads) return void start();
  for (const t of threads) {
    if (t.job) continue;
    const job = nextJob();
    if (!job) break;
    t.job = job;
    t.busy(true);
    t.send(blockOf(job));
  }
  if (!queues.urgent.size && !queues.later.size && threads.every((t) => !t.job)) {
    idle = setTimeout(stop, IDLE_MS);
    (idle as { unref?: () => void }).unref?.(); // a process need not stay up for it
  }
}

async function start() {
  if (starting) return;
  starting = true;
  const cores = globalThis.navigator?.hardwareConcurrency ?? 1;
  // Node leaves a core to its event loop: a point of sale's server answers while it searches
  const count = Math.max(1, Math.min(16, typeof Worker !== 'undefined' ? cores : cores - 1));
  threads = await spawn(count).catch(() => []);
  starting = false;
  if (!threads.length) {
    threads = null;
    void runHere();
  }
  dispatch();
}

function stop() {
  const stopped = threads ?? [];
  threads = null;
  for (const t of stopped) t.stop();
}

function answered(t: Thread, a: BurnAnswer) {
  t.answered = true;
  const job = t.job!;
  t.job = null;
  t.busy(false);
  deliver(job, a);
  dispatch();
}

function died(t: Thread) {
  if (!threads?.includes(t)) return; // stopped, or already counted
  threads = threads.filter((other) => other !== t);
  if (t.job) t.job.search.drop(t.job.block);
  if (!t.answered) {
    // it never ran: neither will the others
    for (const other of threads) if (other.job) other.job.search.drop(other.job.block);
    stop();
    void runHere();
    return;
  }
  if (!threads.length) threads = null; // started again on the next dispatch
  dispatch();
}

/** Starts `count` workers; none where there are no workers. */
async function spawn(count: number): Promise<Thread[]> {
  if (typeof Worker !== 'undefined') {
    return Array.from({ length: count }, () => {
      // this exact form is what bundlers (Vite, webpack) look for to emit the worker
      const worker = new Worker(new URL('./burnWorker.js', import.meta.url), { type: 'module' });
      const t: Thread = {
        job: null,
        answered: false,
        send: (b) => worker.postMessage(b),
        stop: () => worker.terminate(),
        busy: () => {},
      };
      worker.onmessage = ({ data }: MessageEvent<BurnAnswer>) => answered(t, data);
      worker.onerror = (e) => {
        e.preventDefault();
        died(t);
      };
      worker.onmessageerror = () => died(t);
      return t;
    });
  }
  // variables, so that bundlers for the browser leave Node's module and a second copy of the worker alone
  const [threadsModule, file] = ['node:worker_threads', './burnWorker.js'];
  const { Worker: ThreadWorker } = (await import(/* @vite-ignore */ threadsModule).catch(() => ({}))) as {
    Worker?: NodeWorker;
  };
  if (!ThreadWorker) return [];
  return Array.from({ length: count }, () => {
    const worker = new ThreadWorker(new URL(file, import.meta.url));
    worker.unref();
    const t: Thread = {
      job: null,
      answered: false,
      send: (b) => worker.postMessage(b),
      stop: () => void worker.terminate(),
      busy: (working) => (working ? worker.ref() : worker.unref()),
    };
    worker.on('message', (a) => answered(t, a));
    // run from source, as tests are, there is no burnWorker.js: the thread exits before it answers
    for (const event of ['error', 'exit', 'messageerror'] as const) worker.on(event, () => died(t));
    return t;
  });
}

/** Runs the blocks on this thread, yielding to the event loop every ~100 ms, and no more often: each yield is a timer,
 * which costs 4 ms in a visible tab and a whole second in a hidden one. A runner set meanwhile takes every block from
 * the next on. */
async function runHere() {
  if (!here) {
    here = true;
    console.warn('zerc20: burn addresses are searched on the main thread, slower: no worker starts here');
  }
  if (runningHere) return;
  runningHere = true;
  let since = Date.now();
  for (let job; !runner && (job = nextJob());) {
    let a: BurnAnswer;
    try {
      a = { burn: runBlock(blockOf(job)) };
    } catch (e) {
      a = { error: e instanceof Error ? e.message : String(e) };
    }
    deliver(job, a);
    if (Date.now() - since >= 100) {
      await new Promise((resolve) => setTimeout(resolve, 0));
      since = Date.now();
    }
  }
  runningHere = false;
}
