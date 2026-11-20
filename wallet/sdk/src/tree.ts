// Membership paths: a commitment in the latest proved root, and a deposit in the ASP's latest root. Built from
// what every wallet downloads, then checked against the roots the chain holds, so no server is trusted with them.

import type { Hex } from 'viem';
import type { Chain } from './chain.js';
import { core } from './core.js';
import { fail } from './errors.js';
import type { Asp, Indexer, RootEntry } from './servers.js';
import { PAGE } from './servers.js';

const PAGE_BITS = 24;

export interface Membership {
  /** The tree size, which is also the `rootIndex` a transact names. */
  size: number;
  root: Hex;
  siblings: Hex[];
}

/** The leaves of commitment `i`'s chunk, from page `i >> 12` of commitments. */
async function chunkOf(indexer: Indexer, i: number): Promise<Uint8Array> {
  const chunk = Math.floor(i / PAGE);
  const { entries } = await indexer.commitments(chunk);
  if (entries.length < (i - chunk * PAGE + 1) * 128)
    return fail('indexer-mismatch', `commitment ${i} is not served yet`);
  return core.leaves(entries);
}

const hex = (b: Uint8Array): string => Array.from(b, (x) => x.toString(16).padStart(2, '0')).join('');

/** A path for leaf `i` (whose chunk's leaves are `leaves`) against the tree `at`, checked to fold to its root. */
async function pathAt(
  i: number,
  leaves: Uint8Array,
  at: RootEntry,
  chunkRoots: (p: number) => Promise<Uint8Array>,
  pageRoots: () => Promise<Uint8Array>,
): Promise<Membership> {
  const [roots, pages] = await Promise.all([chunkRoots(Math.floor(i / 2 ** PAGE_BITS)), pageRoots()]);
  const siblings = core.path(
    BigInt(i),
    BigInt(at.size),
    leaves,
    roots,
    pages,
    at.partialChunk,
    at.partialPage,
  ) as Hex[];
  const leaf = `0x${hex(leaves.subarray((i % PAGE) * 32, (i % PAGE) * 32 + 32))}`;
  if (core.pathRoot(leaf, BigInt(i), siblings) !== at.root) {
    return fail('indexer-mismatch', `the path of ${i} does not fold to root ${at.root}`);
  }
  return { size: at.size, root: at.root, siblings };
}

/** Commitments `is` in the latest proved root, all under that one root, read and checked once: `null` until a proved
 * root covers every one of them. */
export async function commitmentPaths(indexer: Indexer, chain: Chain, is: number[]): Promise<Membership[] | null> {
  const at = (await indexer.status()).latestRoot;
  if (!at || is.some((i) => at.size <= i)) return null;
  const paths: Membership[] = [];
  for (const i of is)
    paths.push(
      await pathAt(
        i,
        await chunkOf(indexer, i),
        at,
        (p) => indexer.page('chunk-roots', p),
        () => indexer.pageRoots(),
      ),
    );
  // the root a server reports is checked against the ledger: a forged one would make the proof fail on chain
  if (!(await chain.provedRoot(at.size, at.root))) return fail('indexer-mismatch', `root ${at.root} is not proved`);
  return paths;
}

/** Commitment `i` in the latest proved root: `null` until a proved root covers it. */
export const commitmentPath = async (indexer: Indexer, chain: Chain, i: number): Promise<Membership | null> =>
  (await commitmentPaths(indexer, chain, [i]))?.[0] ?? null;

/** Deposits `is` in the ASP root the verifier currently publishes, all under that one root: `null` if that root does
 * not approve every one of them. */
export async function aspPaths(asp: Asp, chain: Chain, is: number[]): Promise<Membership[] | null> {
  const root = await chain.latestAspRoot();
  const at = await asp.rootEntry(root);
  if (!at) return fail('indexer-mismatch', `the ASP has no record of root ${root}`);
  const paths: Membership[] = [];
  for (const i of is) {
    if (at.size <= i) return null;
    const c = Math.floor(i / PAGE);
    const leaves = core.aspLeaves(await asp.bitmap(c), BigInt(c * PAGE), Math.min(PAGE, at.size - c * PAGE));
    if (leaves.subarray((i % PAGE) * 32, (i % PAGE) * 32 + 32).every((b) => b === 0)) return null;
    paths.push(
      await pathAt(
        i,
        leaves,
        at,
        (p) => asp.chunkRoots(p),
        () => asp.pageRoots(),
      ),
    );
  }
  return paths;
}

/** Deposit `i` in the ASP root the verifier currently publishes: `null` if that root does not approve it. */
export const aspPath = async (asp: Asp, chain: Chain, i: number): Promise<Membership | null> =>
  (await aspPaths(asp, chain, [i]))?.[0] ?? null;
