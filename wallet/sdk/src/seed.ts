// A seed from the wallet's own signature, so the account alone restores it. It holds only for wallets whose
// signatures are deterministic (RFC 6979, as MetaMask's and hardware wallets' are): keep the fingerprint, and if a
// later derivation gives another one, the wallet signs differently each time and the seed must be backed up itself.
// And only for an account that is a key: a contract account answers with whatever its contract takes for a signature,
// bytes that may begin alike for every account of its kind, and so would give them all one seed.
// Anything that gets the user to sign the same message gets the seed. Or the other way round, an account from a seed:
// for an app whose seed comes from elsewhere (a passkey), and that has no wallet of its own.

import { secp256k1 } from '@noble/curves/secp256k1.js';
import { entropyToMnemonic } from '@scure/bip39';
import { wordlist } from '@scure/bip39/wordlists/english.js';
import {
  type Hex,
  type WalletClient,
  bytesToHex,
  encodeAbiParameters,
  hexToBytes,
  isAddressEqual,
  keccak256,
  parseAbiParameters,
  recoverMessageAddress,
} from 'viem';
import { mnemonicToAccount } from 'viem/accounts';
import { fail, guard } from './errors.js';

/** The private key of the account a seed's own app holds its public funds in: the first account of the seed's recovery
 * phrase (the seed as 24 BIP-39 words) by the standard derivation, BIP-44's m/44'/60'/0'/0/0. Any wallet given the
 * phrase opens the same account, so its public funds stay reachable without this app. */
export function accountKey(seed: Uint8Array): Hex {
  const key = mnemonicToAccount(entropyToMnemonic(seed, wordlist)).getHdKey().privateKey;
  return bytesToHex(key ?? fail('invalid', 'the seed derives no account key'));
}

/** The private key that signs where the refunds of the deposit address handed out with burn address `index` of
 * `tokenId` on `chainId` go (`DepositAddress.refundTo`). One per address, so that the addresses name neither one another
 * nor the account; from the seed itself, not the view key, since whoever holds it moves those refunds. */
export function refundKey(seed: Uint8Array, chainId: bigint, tokenId: number, index: number): Hex {
  return keccak256(
    encodeAbiParameters(parseAbiParameters('string, bytes32, uint64, uint32, uint32'), [
      'zerc20/wallet/refund-signer/v1',
      bytesToHex(seed),
      chainId,
      tokenId,
      index,
    ]),
  );
}

/** `raw` in canonical form, low s and v = 27/28, so that equivalent signatures give one seed. Throws unless it is the
 * 65 bytes of a signature of `text` by `address`'s own key: a contract account's answer is refused, however long. */
async function ownSignature(raw: Uint8Array, text: string, address: Hex): Promise<Uint8Array> {
  if (raw.length !== 65) throw new Error('not 65 bytes');
  let sig = secp256k1.Signature.fromBytes(raw.subarray(0, 64), 'compact');
  let v = raw[64] >= 27 ? raw[64] - 27 : raw[64];
  if (sig.hasHighS()) {
    sig = new secp256k1.Signature(sig.r, secp256k1.Point.CURVE().n - sig.s);
    v ^= 1;
  }
  const canonical = new Uint8Array([...sig.toBytes('compact'), 27 + v]);
  const signer = await recoverMessageAddress({ message: text, signature: bytesToHex(canonical) });
  if (!isAddressEqual(signer, address)) throw new Error('another signer');
  return canonical;
}

const message = (address: Hex) =>
  [
    'zERC20 wallet seed',
    'WARNING: signing this gives control of your private zERC20 funds.',
    'Sign it only in an app you trust to hold them.',
    `address: ${address.toLowerCase()}`,
    'tag: zerc20/wallet/seed/v1',
  ].join('\n');

/** The seed, a fingerprint to check later derivations against (store it; it reveals nothing about the seed), and the
 * canonical signature it comes from, which proves the seed is this account's. */
export async function seedFromSignature(
  walletClient: WalletClient,
  expectedFingerprint?: Hex,
): Promise<{ seed: Uint8Array; fingerprint: Hex; signature: Hex }> {
  const account = walletClient.account ?? fail('invalid', 'the wallet client has no account');
  const text = message(account.address);
  const raw = hexToBytes(await guard(walletClient.signMessage({ account, message: text })));
  const canonical = await ownSignature(raw, text, account.address).catch(() =>
    fail('unsupported-account', "the wallet's answer is not a signature of this account's own key"),
  );
  const seed = hexToBytes(keccak256(canonical));
  const fingerprint = keccak256(
    new Uint8Array([...new TextEncoder().encode('zerc20/wallet/seed-fingerprint/v1'), ...seed]),
  ).slice(0, 18) as Hex;
  if (expectedFingerprint && expectedFingerprint !== fingerprint) {
    fail(
      'invalid',
      'this wallet signs differently each time, so its signature cannot stand in for a seed: back the seed up instead',
    );
  }
  return { seed, fingerprint, signature: bytesToHex(canonical) };
}
