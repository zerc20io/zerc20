import { bytesToHex } from 'viem';
import { expect, test } from 'vitest';
import { type Watch, scan } from '../src/scan.js';
import { PAGE } from '../src/servers.js';

/** A list of 2-byte entries where entry i is i mod 65536, served in pages; counts the reads. */
function list(count: number) {
  const reads: number[] = [];
  const page = async (p: number) => {
    reads.push(p);
    const n = Math.max(0, Math.min(PAGE, count - p * PAGE));
    const out = new Uint8Array(n * 2);
    for (let j = 0; j < n; j++) new DataView(out.buffer).setUint16(j * 2, (p * PAGE + j) % 65536);
    return out;
  };
  return { page, reads };
}

const key = (i: number) => bytesToHex(Uint8Array.of(i >> 8, i & 255));
const watch = (i: number, from = 0): Watch => ({ key: key(i), from, scannedTo: from });

test('each key is looked for once over what it missed', async () => {
  const { page, reads } = list(3 * PAGE);
  const early = watch(10);
  expect(await scan([early], 2, page, 2 * PAGE)).toEqual([{ key: key(10), position: 10, tentative: false }]);
  expect(reads).toEqual([0, 1]);

  // A key learned late is looked for from its own `from`; the early one only over the new page.
  const late = watch(PAGE + 5, PAGE);
  reads.length = 0;
  const hits = await scan([early, late], 2, page, 3 * PAGE);
  expect(hits).toEqual([{ key: key(PAGE + 5), position: PAGE + 5, tentative: false }]);
  expect(reads).toEqual([1, 2]);
  expect([early.scannedTo, late.scannedTo]).toEqual([3 * PAGE, 3 * PAGE]);

  // Nothing new: nothing read.
  reads.length = 0;
  expect(await scan([early, late], 2, page, 3 * PAGE)).toEqual([]);
  expect(reads).toEqual([]);
});

test('entries past the final count are tentative and looked at again', async () => {
  const { page } = list(PAGE);
  const w = watch(100);
  expect(await scan([w], 2, page, 50, 200)).toEqual([{ key: key(100), position: 100, tentative: true }]);
  expect(w.scannedTo).toBe(50);
  expect(await scan([w], 2, page, 150)).toEqual([{ key: key(100), position: 100, tentative: false }]);
});

test('a short page stops the scan where it ends', async () => {
  const { page } = list(PAGE + 10);
  const w = watch(PAGE + 20);
  await scan([w], 2, page, PAGE + 30);
  expect(w.scannedTo).toBe(PAGE + 10);
});
