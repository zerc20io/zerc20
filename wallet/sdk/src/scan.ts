// Finding a wallet's own entries in the indexer's append-only lists without naming them: download pages, match
// locally. One scanner serves both the 4-byte commitment tags and the 8-byte nullifier prefixes.
//
// Each watched key remembers how far it has been looked for, so a key learned late (a payment announced after
// its commitment landed) is looked for once over the range it missed, and everything else only over new
// entries. Pages below the final count never change, so re-reading them hits the HTTP cache or the CDN.

import { bytesToHex, type Hex } from 'viem';
import { PAGE } from './servers.js';

/** A key to look for: entries at or after `from`, and not yet looked at before `scannedTo`. */
export interface Watch {
  key: Hex;
  from: number;
  /** Everything in `[from, scannedTo)` has been looked at. */
  scannedTo: number;
}

export interface Hit {
  key: Hex;
  position: number;
  /** Past the final count, so a reorg may still move or drop it. */
  tentative: boolean;
}

/** Looks for `watches` (updated in place) in entries up to `final`, and, without recording that, in
 * `[final, live)` too. `page(p)` returns page `p` of `width`-byte entries. */
export async function scan(
  watches: Watch[],
  width: number,
  page: (p: number) => Promise<Uint8Array>,
  final: number,
  live = final,
): Promise<Hit[]> {
  for (const w of watches) w.scannedTo = Math.max(w.scannedTo, w.from);
  const pending = watches.filter((w) => w.scannedTo < live);
  if (pending.length === 0) return [];
  const byKey = new Map<string, Watch[]>();
  for (const w of pending) byKey.set(w.key, [...(byKey.get(w.key) ?? []), w]);
  // a loop, not Math.min(...): spreading 100k+ watches overflows the stack
  let start = live;
  for (const w of pending) start = Math.min(start, w.scannedTo);
  const hits: Hit[] = [];
  for (let p = Math.floor(start / PAGE); p * PAGE < live; p++) {
    const bytes = await page(p);
    const first = p * PAGE;
    const end = Math.min(first + bytes.length / width, live);
    for (let i = Math.max(first, start); i < end; i++) {
      const key = bytesToHex(bytes.subarray((i - first) * width, (i - first + 1) * width));
      for (const w of byKey.get(key) ?? []) {
        if (i >= w.scannedTo) hits.push({ key, position: i, tentative: i >= final });
      }
    }
    // a short page means the indexer has less than `live` (a stale copy): stop, and look again next time
    if (first + bytes.length / width < Math.min(first + PAGE, live)) {
      for (const w of pending) w.scannedTo = Math.max(w.scannedTo, Math.min(final, first + bytes.length / width));
      return hits;
    }
  }
  for (const w of pending) w.scannedTo = Math.max(w.scannedTo, final);
  return hits;
}
