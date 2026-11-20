// A view key as text: what `Wallet.watch` follows an account with, spending nothing.

import { bech32m } from '@scure/base';
import type { ViewKey } from '@zerc20/storage-sdk';
import { type Address, type Hex, bytesToHex, concat, getAddress, hexToBytes } from 'viem';
import type { Owner } from './context.js';
import { core } from './core.js';

const PREFIX = 'zerc20view';

/** `view` and the wallet's own `owner` as checksummed text (bech32m, `zerc20view1…`): `address(20) ‖ view seed(32) ‖
 * auth key hash(32) ‖ nullifying key(32)`. The public key is left for the holder to make from the last two, so that a
 * nullifying key that is not the account's makes a public key that is not either. */
export function encodeViewKey(view: ViewKey, owner: Owner): string {
  const bytes = concat([view.address, view.seed, hexToBytes(owner.authKeyHash), hexToBytes(owner.nullifyingKey)]);
  return bech32m.encode(PREFIX, bech32m.toWords(bytes), false);
}

function bytesOf(text: string): Uint8Array | null {
  try {
    const { prefix, bytes } = bech32m.decodeToBytes(text.trim(), false);
    return prefix === PREFIX && bytes.length === 116 ? bytes : null;
  } catch {
    return null;
  }
}

/** The account `text` is a view key of, or `null` if it is not one: to tell a key apart before it is opened. */
export function viewKeyAccount(text: string): Address | null {
  const bytes = bytesOf(text);
  return bytes && getAddress(bytesToHex(bytes.subarray(0, 20)));
}

/** The view key and owner `text` holds, or `null` for anything else. Needs `initCore`. */
export function decodeViewKey(text: string): { view: ViewKey; owner: Owner } | null {
  const bytes = bytesOf(text);
  if (!bytes) return null;
  const authKeyHash = bytesToHex(bytes.subarray(52, 84));
  const nullifyingKey = bytesToHex(bytes.subarray(84));
  try {
    const publicKey = core.publicKey(authKeyHash, nullifyingKey) as Hex;
    return {
      view: { address: bytes.slice(0, 20), seed: bytes.slice(20, 52) },
      owner: { authKeyHash, publicKey, nullifyingKey },
    };
  } catch {
    return null; // a value that is not a field element
  }
}
