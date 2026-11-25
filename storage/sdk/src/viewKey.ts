// View keys and registration.
//
// An address's view key derives from the root seed of the address's zERC20 identity, so restoring a wallet needs
// nothing from the canister. It derives from the canister's id too: a testnet and mainnet share root seeds, and a key
// escrowed in one canister, which that canister's auditor, controllers and vetKD key can open, must open nothing in
// another. Registering (one wallet signature) publishes what payers need: the address's zERC20 public key and the key
// payers encrypt channel announcements to. It also escrows the view key to the auditor, whom vetKD alone can give the
// key to it. A later registration, from another root seed, replaces it.

import {
  DerivedPublicKey,
  EncryptedVetKey,
  IbeCiphertext,
  IbeIdentity,
  IbeSeed,
  TransportSecretKey,
} from '@icp-sdk/vetkeys';
import { x25519 } from '@noble/curves/ed25519.js';
import { secp256k1 } from '@noble/curves/secp256k1.js';
import { keccak_256 } from '@noble/hashes/sha3.js';
import type { Principal } from '@icp-sdk/core/principal';
import type { Registration } from './candid.js';
import type { CanisterClient } from './canister.js';
import { compare, concat, equal, kdf, nowNs, utf8 } from './crypto.js';
import { FR_BE, addressInbox } from './formats.js';
import { MAX_TTL_NS, registerMessage, vetkdInput } from './wire.js';

/** EIP-191 `personal_sign` by the address's wallet: `r ‖ s ‖ v`, 65 bytes. */
export type Signer = (message: string) => Promise<Uint8Array>;

/** An address's view key: the seed everything owner-only derives from. */
export interface ViewKey {
  address: Uint8Array;
  seed: Uint8Array;
}

/** `address`'s view key in `canister`, from the root seed of the address's zERC20 identity (in zERC20-v2, `keccak256`
 * of a canonical `personal_sign` signature). */
export function viewKey(rootSeed: Uint8Array, address: Uint8Array, canister: Principal): ViewKey {
  if (rootSeed.length !== 32) throw new Error('the root seed must be 32 bytes');
  return { address, seed: kdf(rootSeed, 'view', [address, canister.toUint8Array()]) };
}

/** The X25519 secret that opens announcements to `view`'s address inbox. */
export const notifySecret = (view: ViewKey): Uint8Array => kdf(view.seed, 'notify');

/** The key payers encrypt announcements to, which names `view`'s registration. */
export const notifyKey = (view: ViewKey): Uint8Array => x25519.getPublicKey(notifySecret(view));

/** `view`'s address registered with `publicKey`, the zERC20 public key payments to it are to be owned by. The first
 * check is a query, answered by one replica: only a missing or foreign registration is confirmed with an update call
 * before registering (one wallet signature) or throwing. Throws if the address is registered with another root seed;
 * `register` to take it over. */
export async function registeredViewKey(
  client: CanisterClient,
  rootSeed: Uint8Array,
  signer: Signer,
  address: Uint8Array,
  publicKey: Uint8Array,
): Promise<ViewKey> {
  const view = viewKey(rootSeed, address, client.canisterId);
  const ours = (r: Registration | null) => r && equal(r.notify_key, notifyKey(view)) && equal(r.public_key, publicKey);
  if (ours(await client.registration(address))) return view;
  const [r] = await client.replicated.registration(address, []);
  if (r && !equal(r.notify_key, notifyKey(view))) {
    throw new Error('the address is registered with another root seed: register to take it over');
  }
  if (!ours(r ?? null)) await register(client, signer, view, publicKey);
  return view;
}

/** Registers `view`'s address with `publicKey`, replacing whatever it registered before. */
export async function register(
  client: CanisterClient,
  signer: Signer,
  view: ViewKey,
  publicKey: Uint8Array,
): Promise<void> {
  if (publicKey.length !== 32) throw new Error('a public key is 32 bytes');
  const notify = notifyKey(view);
  const identity = IbeIdentity.fromBytes(vetkdInput(view.address, notify));
  const r: Registration = {
    address: view.address,
    public_key: publicKey,
    notify_key: notify,
    escrow: IbeCiphertext.encrypt(await client.escrowPublicKey(), identity, view.seed, IbeSeed.random()).serialize(),
    expiry_ns: nowNs() + MAX_TTL_NS / 2n,
    signature: new Uint8Array(),
  };
  r.signature = await signer(registerMessage(client.canisterId, r));
  await client.register(r);
}

/** The address that signed `message` with EIP-191 `personal_sign`, or `null`. */
export function eip191Signer(message: string, signature: Uint8Array): Uint8Array | null {
  if (signature.length !== 65) return null;
  const v = signature[64] >= 27 ? signature[64] - 27 : signature[64];
  if (v > 1) return null;
  const msg = utf8(message);
  const digest = keccak_256(concat(utf8(`\x19Ethereum Signed Message:\n${msg.length}`), msg));
  try {
    const sig = secp256k1.Signature.fromBytes(concat(Uint8Array.of(v), signature.subarray(0, 64)), 'recovered');
    if (sig.hasHighS()) return null;
    return keccak_256(sig.recoverPublicKey(digest).toBytes(false).subarray(1)).slice(12);
  } catch {
    return null;
  }
}

/** Whether `r` is what `address` signed: the canister checks this on write, and a payer checks it again so that a
 * canister cannot point it at keys of its own. */
export const verifyRegistration = (canister: Principal, address: Uint8Array, r: Registration): boolean =>
  equal(r.address, address) &&
  equal(eip191Signer(registerMessage(canister, r), r.signature) ?? new Uint8Array(), address);

/** Whom a payment to an address goes to: the zERC20 public key to own the note, and the inbox and key to announce a
 * channel to. */
export interface Recipient {
  address: Uint8Array;
  publicKey: Uint8Array;
  notifyKey: Uint8Array;
  inbox: Uint8Array;
}

/** `address` as a recipient, checked against its owner's signature, or `null` when it never registered: pay it
 * publicly instead, or ask for a receive code. An update call, so that no single replica can answer with a
 * registration the address has replaced; a canister can withhold one, but not forge one. */
export async function lookupRecipient(client: CanisterClient, address: Uint8Array): Promise<Recipient | null> {
  const [r] = await client.replicated.registration(address, []);
  if (!r || !verifyRegistration(client.canisterId, address, r) || compare(r.public_key, FR_BE) >= 0) return null;
  return { address, publicKey: r.public_key, notifyKey: r.notify_key, inbox: addressInbox(address, r.notify_key) };
}

/** For the auditor: the view key in `registration`'s escrow, from what `audit_escrow_key` returned (encrypted to
 * `transportKey`). `null` if the key or the escrow does not open. */
export function openEscrow(
  encrypted: Uint8Array,
  transportKey: TransportSecretKey,
  escrowPublicKey: DerivedPublicKey,
  registration: Registration,
): ViewKey | null {
  const { address, notify_key } = registration;
  try {
    const vetKey = EncryptedVetKey.deserialize(encrypted).decryptAndVerify(
      transportKey,
      escrowPublicKey,
      vetkdInput(address, notify_key),
    );
    const seed = IbeCiphertext.deserialize(registration.escrow).decrypt(vetKey);
    return seed.length === 32 ? { address, seed } : null;
  } catch {
    return null;
  }
}
