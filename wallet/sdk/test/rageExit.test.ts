import { type Hex, encodePacked, keccak256 } from 'viem';
import { expect, test } from 'vitest';
import { walkBack } from '../src/rageExit.js';

type Fields = [bigint, bigint, bigint, bigint];

/** A hash chain's next link; the ledger's own hash is beside the point here. */
const next = (chain: bigint, f: Fields) =>
  BigInt(keccak256(encodePacked(['uint256', 'uint256', 'uint256', 'uint256', 'uint256'], [chain, ...f])));

test('a rage exit walks back from a far checkpoint a segment at a time, each call ending where the one before began', () => {
  const index = 7;
  for (const distance of [1, 900, 901, 1800, 1801, 5000]) {
    const list = Array.from({ length: distance }, (_, k): Fields => [BigInt(k), 1n, 2n, 3n]);
    const before: Hex[] = [];
    let chain = 5n;
    for (const f of list) {
      before.push(`0x${chain.toString(16)}`);
      chain = next(chain, f);
    }
    // the ledger: the hash chain at each checkpoint, from the one at `index + distance`
    const checkpoints = new Map([[index + distance, chain]]);
    const { calls, end } = walkBack(index, index + distance, list, before);
    for (const [at, prev, commits] of calls) {
      // what `checkpointBefore` verifies before it records `prev` at the segment's start
      expect(commits.reduce(next, prev)).toBe(checkpoints.get(Number(at)));
      checkpoints.set(Number(at) - commits.length, prev);
    }
    // the rage exit's own segment, from the deposit to the last checkpoint
    expect(end - index).toBeGreaterThan(0);
    expect(end - index).toBeLessThanOrEqual(900);
    expect(list.slice(0, end - index).reduce(next, BigInt(before[0]))).toBe(checkpoints.get(end));
  }
});
