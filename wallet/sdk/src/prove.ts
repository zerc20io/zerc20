// Groth16 proofs of JoinSplit and RageExit with snarkjs, on the user's device: the witness holds the private keys.

import { sha256 } from '@noble/hashes/sha2.js';
import { bytesToHex } from '@noble/hashes/utils.js';
import { fail } from './errors.js';
import type { Circuit } from './network.js';

/** A URL's bytes, through `f`; `file:` URLs from disk, for Node. */
export async function readUrl(url: string, f: typeof fetch): Promise<Uint8Array> {
  if (url.startsWith('file:')) {
    const fs = 'node:fs/promises';
    const { readFile } = (await import(/* @vite-ignore */ fs)) as { readFile: (path: URL) => Promise<Uint8Array> };
    return readFile(new URL(url));
  }
  const res = await f(url);
  if (!res.ok) return fail('unavailable', `${url}: HTTP ${res.status}`);
  return new Uint8Array(await res.arrayBuffer());
}

const artifacts = new Map<string, Promise<Uint8Array>>();

/** The artifact at `url`, fetched through `f` and checked against its pinned SHA-256: a swapped proving key could leak
 * the witness. */
function artifact(url: string, sha: string, f: typeof fetch): Promise<Uint8Array> {
  let p = artifacts.get(url);
  if (!p) {
    p = readUrl(url, f).then((bytes) => {
      if (bytesToHex(sha256(bytes)) !== sha.toLowerCase()) fail('invalid', `${url} does not match its SHA-256`);
      return bytes;
    });
    p.catch(() => artifacts.delete(url));
    artifacts.set(url, p);
  }
  return p;
}

/** Fetches (through `f`) and checks `circuit`'s artifacts, and loads snarkjs, ahead of its first proof, which then
 * waits for neither: a proof shares the fetch under way. A failed fetch is tried again by the proof, which reports it. */
export async function preload(circuit: Circuit, f: typeof fetch): Promise<void> {
  await Promise.all([
    artifact(circuit.wasm, circuit.wasmSha256, f),
    artifact(circuit.zkey, circuit.zkeySha256, f),
    import('snarkjs'),
  ]);
}

/** `Verifier.Groth16Proof`, with pB in the order the Solidity verifier takes. */
export interface Groth16 {
  pA: [bigint, bigint];
  pB: [[bigint, bigint], [bigint, bigint]];
  pC: [bigint, bigint];
}

/** A proof of `circuit` over `input`, its artifacts fetched through `f`. */
export async function prove(
  circuit: Circuit,
  input: object,
  f: typeof fetch,
): Promise<{ proof: Groth16; signals: bigint[] }> {
  const [wasm, zkey] = await Promise.all([
    artifact(circuit.wasm, circuit.wasmSha256, f),
    artifact(circuit.zkey, circuit.zkeySha256, f),
  ]);
  // loaded on the first proof: an app that only reads balances need not carry snarkjs
  const { groth16 } = await import('snarkjs');
  const { proof, publicSignals } = await groth16.fullProve(
    input,
    { type: 'mem', data: wasm },
    { type: 'mem', data: zkey },
  );
  const b = (x: string) => BigInt(x);
  return {
    proof: {
      pA: [b(proof.pi_a[0]), b(proof.pi_a[1])],
      pB: [
        [b(proof.pi_b[0][1]), b(proof.pi_b[0][0])],
        [b(proof.pi_b[1][1]), b(proof.pi_b[1][0])],
      ],
      pC: [b(proof.pi_c[0]), b(proof.pi_c[1])],
    },
    signals: publicSignals.map(b),
  };
}
