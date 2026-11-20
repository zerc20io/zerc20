// A wallet holding tens of thousands of notes: nothing quadratic, nothing that overflows, a state that stays small.

import { bytesToHex } from 'viem';
import { expect, test } from 'vitest';
import { type Watch, scan } from '../src/scan.js';
import { PAGE } from '../src/servers.js';
import { type Coin, pick } from '../src/spend.js';
import { type NoteRecord, emptyWalletState, openState, sealState } from '../src/state.js';
import { applyHits } from '../src/sync.js';

const key = (i: number) => bytesToHex(Uint8Array.of(i >>> 24, (i >>> 16) & 255, (i >>> 8) & 255, i & 255));
const timed = <T>(f: () => T): [T, number] => {
  const start = performance.now();
  return [f(), performance.now() - start];
};

test('200k watched keys scan without overflowing', async () => {
  // a page of tags where entry i is key(i)
  const page = async (p: number) => {
    const out = new Uint8Array(PAGE * 4);
    for (let j = 0; j < PAGE; j++) new DataView(out.buffer).setUint32(j * 4, p * PAGE + j);
    return out;
  };
  const watches: Watch[] = Array.from({ length: 200_000 }, (_, i) => ({
    key: key(10_000_000 + i),
    from: 0,
    scannedTo: 0,
  }));
  watches.push({ key: key(5), from: 0, scannedTo: 0 });
  const start = performance.now();
  expect(await scan(watches, 4, page, 2 * PAGE)).toEqual([{ key: key(5), position: 5, tentative: false }]);
  expect(performance.now() - start).toBeLessThan(2000);
});

test('picking among 50k notes is fast and still finds the smallest total', () => {
  const coins: Coin[] = Array.from({ length: 50_000 }, (_, i) => ({
    kind: i % 7 ? 'note' : 'burn',
    index: i,
    value: BigInt(1 + ((i * 7919) % 100_000)),
  }));
  const [picked, ms] = timed(() => pick(coins, 150_000n));
  expect(ms).toBeLessThan(1000);
  const total = picked!.reduce((s, c) => s + c.value, 0n);
  expect(total).toBe(150_000n);
  expect(picked!.length === 1 || picked![1]!.kind === 'note').toBe(true);
  // against brute force on a sample
  const few = coins.slice(0, 300);
  const best = (need: bigint) => {
    let min: bigint | null = few.find((c) => c.value >= need)?.value ?? null;
    for (const c of few) if (c.value >= need && (min === null || c.value < min)) min = c.value;
    for (const a of few)
      for (const b of few)
        if (a !== b && b.kind === 'note' && a.value + b.value >= need && (min === null || a.value + b.value < min))
          min = a.value + b.value;
    return min;
  };
  for (const need of [5_000n, 99_999n, 150_000n, 199_000n]) {
    expect(pick(few, need)?.reduce((s, c) => s + c.value, 0n) ?? null).toBe(best(need));
  }
});

const note = (i: number): NoteRecord => ({
  chainId: 1n,
  tokenId: 1,
  value: BigInt(i + 1),
  salt: bytesToHex(new Uint8Array(32).fill(i % 256)),
  source: 'received',
  peer: '0x1111111111111111111111111111111111111111',
  atNs: 1_700_000_000_000_000_000n,
  noteHash: bytesToHex(new Uint8Array(32).fill(i % 256)),
  watch: { key: key(i), from: 0, scannedTo: 0 },
  found: [],
});

test('10k notes take their hits in one pass', () => {
  const notes = Array.from({ length: 10_000 }, (_, i) => note(i));
  const hits = notes.map((_, i) => ({ key: key(i), position: i, tentative: false }));
  const [, ms] = timed(() => applyHits(notes, [], hits));
  expect(ms).toBeLessThan(1000);
  expect(notes.every((n, i) => n.found.length === 1 && n.found[0]!.index === i)).toBe(true);
});

test('the saved state of 10k confirmed notes stays a few MB', () => {
  const state = emptyWalletState('0x2222222222222222222222222222222222222222');
  // confirmed received notes keep no watches
  state.notes = Array.from({ length: 10_000 }, (_, i) => ({
    ...note(i),
    watch: null,
    found: [{ index: i, tentative: false, spent: i % 2 === 0, confirmed: true }],
  }));
  const key = new Uint8Array(32).fill(7);
  const [sealed, sealMs] = timed(() => sealState(key, state));
  const [opened, openMs] = timed(() => openState(key, sealed));
  expect(sealed.length).toBeLessThan(5_000_000);
  expect(sealMs + openMs).toBeLessThan(2000);
  expect(opened!.notes.length).toBe(10_000);
});
