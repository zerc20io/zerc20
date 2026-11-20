import { expect, test } from 'vitest';
import type { CanisterClient } from '../src/canister.js';
import { readSequences } from '../src/sync.js';

test('a long sequence is read in a few round trips, up to its first empty slot, and a short one in one', async () => {
  // slots by id, the id being the slot's index in one byte after the sequence's
  const filled = (seq: number, length: number) =>
    Array.from({ length }, (_, i) => [`${seq}:${i}`, { data: new Uint8Array([seq]), at_ns: BigInt(i) }] as const);
  const slots = new Map([...filled(1, 700), ...filled(2, 3)]);
  let rounds = 0;
  const reader = (counted: boolean) => ({
    get_slots: async (_: unknown, ids: Uint8Array[]) => {
      if (counted) rounds++;
      return ids.map((id) => {
        const slot = slots.get(`${id[0]}:${new DataView(id.buffer).getUint16(1)}`);
        return slot ? [slot] : [];
      });
    },
  });
  const client = { actor: reader(false), replicated: reader(true) } as unknown as CanisterClient;
  const idAt = (seq: number) => (i: number) => {
    const id = new Uint8Array(32);
    id[0] = seq;
    new DataView(id.buffer).setUint16(1, i);
    return id;
  };
  const [long, short] = await readSequences(client, { Lane: null }, [
    { next: 0, idAt: idAt(1) },
    { next: 0, idAt: idAt(2) },
  ]);
  expect(long!.map(({ slot }) => slot.at_ns)).toEqual(Array.from({ length: 700 }, (_, i) => BigInt(i)));
  expect(short).toHaveLength(3);
  // the long one 1, 16, 32, 64, 128, 256 and the last 203 slots at a time: a replicated read each
  expect(rounds).toBe(7);
});
