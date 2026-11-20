// Primitives: HKDF-SHA256, ChaCha20-Poly1305 with random nonces, X25519 ECIES, and byte helpers.

import { chacha20poly1305 } from '@noble/ciphers/chacha.js';
import { x25519 } from '@noble/curves/ed25519.js';
import { hkdf } from '@noble/hashes/hkdf.js';
import { sha256 } from '@noble/hashes/sha2.js';
import { bytesToHex, hexToBytes, randomBytes } from '@noble/hashes/utils.js';

export { bytesToHex as hex, hexToBytes as unhex, randomBytes };

export const utf8 = (text: string): Uint8Array => new TextEncoder().encode(text);

export function concat(...parts: Uint8Array[]): Uint8Array {
  const out = new Uint8Array(parts.reduce((n, p) => n + p.length, 0));
  let at = 0;
  for (const part of parts) {
    out.set(part, at);
    at += part.length;
  }
  return out;
}

export function u16be(n: number): Uint8Array {
  const out = new Uint8Array(2);
  new DataView(out.buffer).setUint16(0, n, false);
  return out;
}

export function u32be(n: number): Uint8Array {
  const out = new Uint8Array(4);
  new DataView(out.buffer).setUint32(0, n, false);
  return out;
}

export function u64be(n: bigint): Uint8Array {
  const out = new Uint8Array(8);
  new DataView(out.buffer).setBigUint64(0, n, false);
  return out;
}

export const readU16 = (bytes: Uint8Array, at: number): number =>
  new DataView(bytes.buffer, bytes.byteOffset).getUint16(at, false);

export const readU32 = (bytes: Uint8Array, at: number): number =>
  new DataView(bytes.buffer, bytes.byteOffset).getUint32(at, false);

export const readU64 = (bytes: Uint8Array, at: number): bigint =>
  new DataView(bytes.buffer, bytes.byteOffset).getBigUint64(at, false);

export function equal(a: Uint8Array, b: Uint8Array): boolean {
  return a.length === b.length && a.every((byte, i) => byte === b[i]);
}

/** Lexicographic (= big-endian numeric, for equal lengths) comparison. */
export function compare(a: Uint8Array, b: Uint8Array): number {
  for (let i = 0; i < Math.min(a.length, b.length); i++) {
    if (a[i] !== b[i]) return a[i] - b[i];
  }
  return a.length - b.length;
}

/** `u32_be(len) ‖ part` for every part, so fields can never run into each other. */
export function lengthPrefixed(parts: Uint8Array[]): Uint8Array {
  return concat(...parts.flatMap((part) => [u32be(part.length), part]));
}

/** Unix time in ns from the local clock. */
export const nowNs = (): bigint => BigInt(Date.now()) * 1_000_000n;

const KDF_SALT = utf8('zerc20/storage/kdf/v1');

/** HKDF-SHA256 of `key`, domain-separated by `label` and the length-prefixed `parts`. */
export function kdf(key: Uint8Array, label: string, parts: Uint8Array[] = []): Uint8Array {
  return hkdf(sha256, key, KDF_SALT, lengthPrefixed([utf8(label), ...parts]), 32);
}

/** SHA-256 of `tag` and `parts`, each length-prefixed: what anyone can compute, where `kdf` needs a key. */
export function taggedHash(tag: string, parts: Uint8Array[]): Uint8Array {
  return sha256(lengthPrefixed([utf8(tag), ...parts]));
}

/** `nonce(12) ‖ ChaCha20-Poly1305`. The nonce is random so that a retry after a failed but
 * already-visible call never reuses a (key, nonce) pair. */
export function seal(key: Uint8Array, aad: Uint8Array, msg: Uint8Array): Uint8Array {
  const nonce = randomBytes(12);
  return concat(nonce, chacha20poly1305(key, nonce, aad).encrypt(msg));
}

export function open(key: Uint8Array, aad: Uint8Array, blob: Uint8Array): Uint8Array | null {
  if (blob.length < 12) return null;
  try {
    return chacha20poly1305(key, blob.subarray(0, 12), aad).decrypt(blob.subarray(12));
  } catch {
    return null;
  }
}

/** ECIES to an X25519 public key: `ephemeral_pk(32) ‖ seal(..)`. `null` for a low-order key, whose
 * shared secret anyone could compute. */
export function sealTo(publicKey: Uint8Array, label: string, aad: Uint8Array, msg: Uint8Array): Uint8Array | null {
  const ephemeral = x25519.utils.randomSecretKey();
  const ephemeralPk = x25519.getPublicKey(ephemeral);
  let shared: Uint8Array;
  try {
    shared = x25519.getSharedSecret(ephemeral, publicKey);
  } catch {
    return null;
  }
  return concat(ephemeralPk, seal(kdf(shared, label, [ephemeralPk, publicKey]), aad, msg));
}

export function openFrom(secret: Uint8Array, label: string, aad: Uint8Array, blob: Uint8Array): Uint8Array | null {
  if (blob.length < 32) return null;
  const ephemeralPk = blob.subarray(0, 32);
  try {
    const shared = x25519.getSharedSecret(secret, ephemeralPk);
    const key = kdf(shared, label, [ephemeralPk, x25519.getPublicKey(secret)]);
    return open(key, aad, blob.subarray(32));
  } catch {
    return null;
  }
}
