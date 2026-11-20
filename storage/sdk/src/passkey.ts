// Seeds kept for passkeys. A wallet whose account was restored from its recovery phrase opens it with a passkey whose
// PRF output is not the seed, so the seed is sealed in Outgoing slots whose ids and key only that PRF output derives:
// the passkey, synced to another device, finds and opens it there. Outgoing slots join no log and every blob has one
// length, so the canister tells these from no other record.

import { type CanisterClient, StorageError } from './canister.js';
import { equal, open, seal } from './crypto.js';
import { passkeySeedId, passkeySeedKey, passkeySeedPlaintext, readPasskeySeed } from './formats.js';
import { readSequences } from './sync.js';

const OUTGOING = { Outgoing: null };
/** Submits a store makes before it gives up: each `Occupied` means someone who saw the slot's id asked for wrote first. */
const STORE_TRIES = 3;

/** The seeds kept for `prf`'s passkey, in slot order, and the first empty slot. A slot that does not open is passed
 * over: someone who saw its id asked for may have written it first. */
async function kept(client: CanisterClient, prf: Uint8Array): Promise<{ seeds: Uint8Array[]; end: number }> {
  const key = passkeySeedKey(prf, client.canisterId);
  const idAt = (i: number) => passkeySeedId(prf, client.canisterId, i);
  const [filled] = await readSequences(client, OUTGOING, [{ next: 0, idAt }]);
  const seeds = filled.flatMap(({ id, slot }) => {
    const plain = open(key, id, slot.data);
    const seed = plain && readPasskeySeed(plain);
    return seed ? [seed] : [];
  });
  return { seeds, end: filled.length };
}

/** The seed kept for the passkey whose PRF output is `prf`, or `null` if none is. The last one counts, so that a later
 * version appends a record rather than rewrite one. */
export async function fetchPasskeySeed(client: CanisterClient, prf: Uint8Array): Promise<Uint8Array | null> {
  return (await kept(client, prf)).seeds.at(-1) ?? null;
}

/** Keeps `seed` for the passkey whose PRF output is `prf`, unless it is the one kept already: a retry, or a device that
 * kept it only on its own, writes nothing twice. */
export async function storePasskeySeed(client: CanisterClient, prf: Uint8Array, seed: Uint8Array): Promise<void> {
  for (let tries = 1; ; tries++) {
    const { seeds, end } = await kept(client, prf);
    const last = seeds.at(-1);
    if (last && equal(last, seed)) return;
    const id = passkeySeedId(prf, client.canisterId, end);
    const data = seal(passkeySeedKey(prf, client.canisterId), id, passkeySeedPlaintext(seed));
    try {
      return await client.submit([{ Put: { kind: OUTGOING, id, data } }]);
    } catch (e) {
      if (!(e instanceof StorageError && e.occupied) || tries === STORE_TRIES) throw e;
    }
  }
}
