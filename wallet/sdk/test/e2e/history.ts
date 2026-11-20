// What every device of a wallet shows alike: its history, read from storage and the chain.

import { expect } from 'vitest';
import type { Wallet } from '../../src/index.js';

/** A wallet's history as every device of it shows it: what is on chain, with its ids, amounts, fees, parties and times,
 * and the deposit addresses it handed out, with the fee each takes. */
const history = (w: Wallet) =>
  JSON.stringify(
    [
      w
        .activity()
        .filter((a) => a.status === 'done')
        .map((a) => [a.id, a.kind, a.amount, a.fee, a.counterparty, a.via, a.at?.getTime() ?? null]),
      w.depositAddresses().map((d) => [d.address, d.fee]),
    ],
    (_, v: unknown) => (typeof v === 'bigint' ? `${v}` : typeof v === 'string' ? v.toLowerCase() : v),
  );

/** Syncs `w` until `done` holds of it, or fails with `what` after `ms`. */
async function syncUntil(w: Wallet, done: () => boolean, failure: () => void, ms: number): Promise<void> {
  const end = Date.now() + ms;
  for (;;) {
    await w.sync();
    if (done()) return;
    if (Date.now() > end) failure();
    await new Promise((r) => setTimeout(r, 1000));
  }
}

/** Closes `w` once its history is settled (nothing in it shown from this device's operations but a failure, and its
 * receipts written), then syncs another device of its wallet, opened from nothing by `reopen`, until it shows the same
 * history, and closes that too: one wallet is open in one place at a time. */
export async function sameElsewhere(w: Wallet, reopen: () => Promise<Wallet>, ms = 300_000): Promise<void> {
  const settled = () => w.activity().every((a) => a.status === 'failed' || a.id.includes(':'));
  await syncUntil(w, settled, () => expect(w.activity().filter((a) => !a.id.includes(':'))).toEqual([]), ms);
  const seen = history(w);
  await w.close();
  const other = await reopen();
  await syncUntil(
    other,
    () => history(other) === seen,
    () => expect(JSON.parse(history(other))).toEqual(JSON.parse(seen)),
    ms,
  );
  await other.close();
}
