// Bytes the canister checks: signed messages and proof-of-work digests, and the vetKD input. They must match
// canister/src/registry.rs, audit.rs and store.rs byte for byte; test/wire.test.ts pins the same fixtures as the
// canister's `wire_fixtures` test.

import type { Principal } from '@icp-sdk/core/principal';
import { sha256 } from '@noble/hashes/sha2.js';
import type { Action, KindName, Registration } from './candid.js';
import { concat, hex, lengthPrefixed, taggedHash, u64be, utf8 } from './crypto.js';

/** Sized for a five-year-old budget Android phone (the canister's `lib.rs` says how). */
export const POW_BITS = 14;
/** Address inboxes are public, so opening a channel costs more work than a plain write. */
export const OPEN_POW_BITS = 17;
export const REGISTER_POW_BITS = 18;
/** Every blob is exactly this long, so its length tells nothing of what it holds. */
export const BLOB_LEN = 256;
export const MAX_READ = 256;
/** Lane slot ids per `get_log` call. */
export const MAX_LOG_READ = 8192;
/** Longest a signed request stays valid. */
export const MAX_TTL_NS = 600_000_000_000n;

/** The canister's `Kind` numbers (Rust's, not the .did's alphabetical order). */
const KIND_CODE: Record<KindName, number> = { Outgoing: 0, Lane: 1 };

/** Tags a registration's proof-of-work digest and the text its owner signs. */
const REGISTRATION_TAG = 'zerc20/storage/registration/v1';

/** The vetKD input, which is also the IBE identity, of the key to the escrow of `address`'s registration with
 * `notifyKey`. */
export const vetkdInput = (address: Uint8Array, notifyKey: Uint8Array): Uint8Array => concat(address, notifyKey);

/** What an address owner signs (EIP-191) to register. */
export function registerMessage(canister: Principal, r: Registration): string {
  return (
    `zERC20 storage registration\ncanister: ${canister.toText()}\naddress: 0x${hex(r.address)}\n` +
    `public_key: 0x${hex(r.public_key)}\nnotify_key: 0x${hex(r.notify_key)}\n` +
    `escrow_sha256: 0x${hex(sha256(r.escrow))}\nexpiry_ns: ${r.expiry_ns}\ntag: ${REGISTRATION_TAG}`
  );
}

export function registerDigest(r: Registration): Uint8Array {
  return taggedHash(REGISTRATION_TAG, [r.address, r.public_key, r.notify_key, r.escrow, u64be(r.expiry_ns)]);
}

export function actionsDigest(actions: Action[]): Uint8Array {
  const parts = actions.flatMap((action) => {
    if ('OpenChannel' in action) {
      const { inbox, enc_announcement, outgoing_id, enc_outgoing } = action.OpenChannel;
      return [Uint8Array.of(0), lengthPrefixed([inbox, enc_announcement, outgoing_id, enc_outgoing])];
    }
    const { kind, id, data } = action.Put;
    const code = KIND_CODE[Object.keys(kind)[0] as KindName];
    return [Uint8Array.of(1, code), lengthPrefixed([id, data])];
  });
  return sha256(concat(...parts));
}

export const requiredPowBits = (actions: Action[]): number =>
  actions.some((action) => 'OpenChannel' in action) ? OPEN_POW_BITS : POW_BITS;

const POW_TAG = utf8('zerc20/storage/pow/v1');

function leadingZeroBits(bytes: Uint8Array): number {
  let zeros = 0;
  for (const byte of bytes) {
    if (byte !== 0) return zeros + Math.clz32(byte) - 24;
    zeros += 8;
  }
  return zeros;
}

export function powOk(digest: Uint8Array, nonce: bigint, bits: number): boolean {
  return leadingZeroBits(sha256(concat(POW_TAG, digest, u64be(nonce)))) >= bits;
}

/** The first nonce whose proof of work reaches `bits`, searched in a Web Worker so a page stays
 * responsive. Where there is none (Node), or it does not start (a bundler that left out
 * powWorker.js), on this thread, yielding every ~100 ms. */
export async function solvePow(digest: Uint8Array, bits: number): Promise<bigint> {
  if (typeof Worker !== 'undefined') {
    try {
      return await inWorker(digest, bits);
    } catch {
      // searched here instead
    }
  }
  return findNonce(digest, bits, 100);
}

async function inWorker(digest: Uint8Array, bits: number): Promise<bigint> {
  // this exact form is what bundlers (Vite, webpack) look for to emit the worker
  const worker = new Worker(new URL('./powWorker.js', import.meta.url), { type: 'module' });
  try {
    return await new Promise<bigint>((resolve, reject) => {
      worker.onmessage = ({ data }: MessageEvent<bigint>) => resolve(data);
      worker.onerror = reject;
      worker.postMessage({ digest, bits });
    });
  } finally {
    worker.terminate();
  }
}

/** The first nonce whose proof of work reaches `bits`. On a page's thread, yields to the event loop
 * every `yieldMs`, and no more often: each yield is a timer, which costs 4 ms in a visible tab and a
 * whole second in a hidden one. */
export async function findNonce(digest: Uint8Array, bits: number, yieldMs: number): Promise<bigint> {
  const buffer = concat(POW_TAG, digest, new Uint8Array(8));
  const nonce = new DataView(buffer.buffer, POW_TAG.length + digest.length, 8);
  let since = Date.now();
  for (let n = 0; ; n++) {
    nonce.setUint32(0, Math.floor(n / 2 ** 32), false);
    nonce.setUint32(4, n >>> 0, false);
    if (leadingZeroBits(sha256(buffer)) >= bits) return BigInt(n);
    if (n % 4096 === 4095 && Date.now() - since >= yieldMs) {
      await new Promise((resolve) => setTimeout(resolve, 0));
      since = Date.now();
    }
  }
}
