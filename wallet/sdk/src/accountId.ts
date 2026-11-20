// A zERC20 ID: an account's address as text that no other wallet or exchange takes for an address, so that a payer
// pays the account privately, as only a zERC20 wallet does, and never by a public transfer to the address, which this
// wallet does not hold.

import { bech32m } from '@scure/base';
import { type Address, bytesToHex, getAddress, hexToBytes } from 'viem';

const PREFIX = 'zerc20id';

/** `address` as its zERC20 ID: checksummed text (bech32m, `zerc20id1…`) of its 20 bytes. */
export const accountId = (address: Address): string =>
  bech32m.encode(PREFIX, bech32m.toWords(hexToBytes(address)), false);

/** The account `text` is the zERC20 ID of, or `null` if it is not one. */
export function idAccount(text: string): Address | null {
  try {
    const { prefix, bytes } = bech32m.decodeToBytes(text.trim());
    return prefix === PREFIX && bytes.length === 20 ? getAddress(bytesToHex(bytes)) : null;
  } catch {
    return null;
  }
}
