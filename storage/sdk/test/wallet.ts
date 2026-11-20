// A test EVM wallet that signs EIP-191 messages like `personal_sign`.

import { secp256k1 } from '@noble/curves/secp256k1.js';
import { keccak_256 } from '@noble/hashes/sha3.js';
import { concat, utf8 } from '../src/crypto.js';

const eip191 = (message: string): Uint8Array => {
  const msg = utf8(message);
  return keccak_256(concat(utf8(`\x19Ethereum Signed Message:\n${msg.length}`), msg));
};

const addressOf = (publicKey: Uint8Array): Uint8Array => keccak_256(publicKey.subarray(1)).slice(12);

export function wallet(seed: number) {
  const secret = new Uint8Array(32).fill(seed);
  return {
    address: addressOf(secp256k1.getPublicKey(secret, false)),
    /** Stands in for the zERC20 root seed of the wallet's private identity. */
    rootSeed: keccak_256(concat(utf8('test root seed'), secret)),
    /** `r ‖ s ‖ v` with `v` = 27 or 28. */
    sign: async (message: string): Promise<Uint8Array> => {
      const sig = secp256k1.sign(eip191(message), secret, { prehash: false, format: 'recovered' });
      return concat(sig.subarray(1), Uint8Array.of(27 + sig[0]!));
    },
  };
}

/** The address that signed `message`. */
export function signer(message: string, signature: Uint8Array): Uint8Array {
  const recovered = concat(Uint8Array.of(signature[64]! - 27), signature.subarray(0, 64));
  const point = secp256k1.Signature.fromBytes(recovered, 'recovered').recoverPublicKey(eip191(message));
  return addressOf(point.toBytes(false));
}
