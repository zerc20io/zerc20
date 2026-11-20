// The indexer and the ASP, read in whole pages that every wallet downloads alike: a wallet never names a
// leaf, an address or a nullifier to a server. Layouts are in backend/indexer/README.md and backend/asp/README.md.

import { type Hex, bytesToHex } from 'viem';
import { platformFetch } from './chain.js';
import { fail } from './errors.js';

export const PAGE = 4096;
const TIMEOUT_MS = 20_000;

async function fetchBytes(f: typeof fetch, url: string): Promise<Uint8Array> {
  let res: Response;
  try {
    res = await f(url, { signal: AbortSignal.timeout(TIMEOUT_MS) });
  } catch (e) {
    return fail('unavailable', `${url}: ${(e as Error).message}`);
  }
  if (!res.ok) return fail('unavailable', `${url}: HTTP ${res.status}`);
  return new Uint8Array(await res.arrayBuffer());
}

async function fetchJson<T>(f: typeof fetch, url: string): Promise<T> {
  return JSON.parse(new TextDecoder().decode(await fetchBytes(f, url))) as T;
}

/** A tree's size and root, with the roots of its partial chunk and page (null where the size ends on a
 * boundary): what a path against that root needs besides the wallet's own chunk. */
export interface RootEntry {
  size: number;
  root: Hex;
  partialChunk: Hex | null;
  partialPage: Hex | null;
}

const ZERO = `0x${'0'.repeat(64)}`;
const orNull = (h: Hex): Hex | null => (h === ZERO ? null : h);

/** Root entries back to back: size(8) ‖ root ‖ partial chunk ‖ partial page (zero: none) [‖ matches(1)]. */
function rootEntries(bytes: Uint8Array, width: number): (RootEntry & { matches: boolean })[] {
  const out = [];
  for (let at = 0; at + width <= bytes.length; at += width) {
    const e = bytes.subarray(at, at + width);
    out.push({
      size: Number(new DataView(e.buffer, e.byteOffset).getBigUint64(0, false)),
      root: bytesToHex(e.subarray(8, 40)),
      partialChunk: orNull(bytesToHex(e.subarray(40, 72))),
      partialPage: orNull(bytesToHex(e.subarray(72, 104))),
      matches: width === 104 || e[104] === 1,
    });
  }
  return out;
}

export interface IndexerStatus {
  commitments: number;
  commitmentsFinal: number;
  nullifiers: number;
  nullifiersFinal: number;
  /** The latest proved root the indexer derives itself, before any forged one: what a proof uses. */
  latestRoot: RootEntry | null;
  /** The first proved root since the protocol last recovered that the indexer does not derive: a forged one. No root
   * is proved after it until the protocol recovers. */
  mismatch: { size: number; root: Hex } | null;
  /** The newest block whose entries cannot reorg, the one the final counts stand at. */
  finalBlock: number | null;
  /** The last block it has indexed. Read after the counts: they may stand before it. */
  cursor: number;
  /** How long a commitment usually waits for a proved root to cover it, in seconds, as measured on chain: anyone may
   * prove roots, at any pace. Null until measured, and from an indexer that does not measure it. */
  settleSecs: number | null;
}

interface StatusJson {
  commitments: number;
  commitments_final: number;
  nullifiers: number;
  nullifiers_final: number;
  latest_root: {
    index: number;
    root: Hex;
    matches: boolean;
    partial_chunk_root: Hex | null;
    partial_page_root: Hex | null;
  } | null;
  mismatch: { index: number; root: Hex } | null;
  settle_secs?: number | null;
  indexer: { final_block: number | null; cursor: number };
}

export class Indexer {
  constructor(
    readonly url: string,
    readonly fetch: typeof globalThis.fetch = platformFetch,
  ) {}

  async status(): Promise<IndexerStatus> {
    const s = await fetchJson<StatusJson>(this.fetch, `${this.url}/status`);
    const r = s.latest_root;
    return {
      commitments: s.commitments,
      commitmentsFinal: s.commitments_final,
      nullifiers: s.nullifiers,
      nullifiersFinal: s.nullifiers_final,
      latestRoot:
        r && r.matches
          ? { size: r.index, root: r.root, partialChunk: r.partial_chunk_root, partialPage: r.partial_page_root }
          : null,
      mismatch: s.mismatch ? { size: s.mismatch.index, root: s.mismatch.root } : null,
      finalBlock: s.indexer.final_block,
      cursor: s.indexer.cursor,
      settleSecs: s.settle_secs ?? null,
    };
  }

  /** Page `p` of a list of fixed-size entries: 4096 entries, fewer while it fills. */
  page(list: 'tags' | 'nullifiers' | 'blocks' | 'times' | 'chunk-roots' | 'marks', p: number): Promise<Uint8Array> {
    return fetchBytes(this.fetch, `${this.url}/${list}/${p}`);
  }

  /** Page `p` of commitments: the ledger's hash chain before it (32 bytes), then 4 fields of 32 bytes each. */
  async commitments(p: number): Promise<{ hashChainBefore: Hex; entries: Uint8Array }> {
    const body = await fetchBytes(this.fetch, `${this.url}/commitments/${p}`);
    return { hashChainBefore: bytesToHex(body.subarray(0, 32)), entries: body.subarray(32) };
  }

  pageRoots(): Promise<Uint8Array> {
    return fetchBytes(this.fetch, `${this.url}/page-roots`);
  }

  /** Page `p` of proved roots, in the order they were proved. */
  async roots(p: number): Promise<(RootEntry & { matches: boolean })[]> {
    return rootEntries(await fetchBytes(this.fetch, `${this.url}/roots/${p}`), 105);
  }
}

export interface AspStatus {
  decided: number;
  latestRoot: RootEntry | null;
  /** How old a deposit's block must be before it is screened. */
  delaySecs: number;
}

export class Asp {
  constructor(
    readonly url: string,
    readonly fetch: typeof globalThis.fetch = platformFetch,
  ) {}

  async status(): Promise<AspStatus> {
    const s = await fetchJson<{ decided: number; latest_root: StatusJson['latest_root']; delay_secs: number }>(
      this.fetch,
      `${this.url}/status`,
    );
    const r = s.latest_root;
    return {
      decided: s.decided,
      latestRoot: r
        ? { size: r.index, root: r.root, partialChunk: r.partial_chunk_root, partialPage: r.partial_page_root }
        : null,
      delaySecs: s.delay_secs,
    };
  }

  /** 512 bytes: position `c * 4096 + j` is approved if bit `j % 8` of byte `j / 8` is set. */
  bitmap(c: number): Promise<Uint8Array> {
    return fetchBytes(this.fetch, `${this.url}/bitmap/${c}`);
  }

  chunkRoots(p: number): Promise<Uint8Array> {
    return fetchBytes(this.fetch, `${this.url}/chunk-roots/${p}`);
  }

  pageRoots(): Promise<Uint8Array> {
    return fetchBytes(this.fetch, `${this.url}/page-roots`);
  }

  /** The recorded root whose value is `root`, searched from the newest page back. */
  async rootEntry(root: Hex): Promise<RootEntry | null> {
    const latest = (await this.status()).latestRoot;
    if (latest?.root === root) return latest;
    for (let p = 0; ; p++) {
      const entries = rootEntries(await fetchBytes(this.fetch, `${this.url}/roots/${p}`), 104);
      const hit = entries.find((e) => e.root === root);
      if (hit) return hit;
      if (entries.length < PAGE) return null;
    }
  }
}
