// What every blob holds, and the ids and keys of the slots that hold them.
//
// A plaintext is `type(1) ‖ body ‖ zeros`, padded to the one length its blob has: every blob is `BLOB_LEN` bytes, so
// its kind does not show. Each type has one fixed body. A reader takes the body and ignores what follows it, so a
// later version can append a field that an older reader passes over; a record an older reader must not misread takes
// a new type, which that reader drops.

import type { Principal } from '@icp-sdk/core/principal';
import { bech32m } from '@scure/base';
import { compare, concat, kdf, readU16, readU32, readU64, taggedHash, u16be, u32be, u64be, unhex } from './crypto.js';
import { BLOB_LEN } from './wire.js';

/** A sealed slot's plaintext: the blob less the nonce and the tag. */
export const SLOT_PLAIN = BLOB_LEN - 12 - 16;
/** An inbox announcement's plaintext: also less the ephemeral key. */
export const ANNOUNCE_PLAIN = BLOB_LEN - 32 - 12 - 16;
/** The most salts a burn block holds. */
export const BURN_BLOCK = 6;
/** The BN254 scalar field modulus `Fr`, big-endian. */
export const FR_BE = unhex('30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001');

/** Record types, the first byte of every plaintext. */
export const NOTE = 0x01;
export const CODE_NOTE = 0x02;
export const SELF_NOTE = 0x03;
export const DEPOSIT = 0x04;
export const BURN_BLOCK_RECORD = 0x05;
export const RETURNED = 0x06;
export const DEPOSIT_ADDRESS = 0x07;
export const POS_LANE = 0x08;
export const SENT_TO_ADDRESS = 0x10;
export const SENT_TO_CODE = 0x11;
export const CHANNEL = 0x20;
export const PASSKEY_SEED = 0x30;
export const RECEIVE_CODE = 0x40;

// ---- ids and keys ----

/** The inbox announcements of channels to `address` go to, under its registration's notify key: another
 * registration, another inbox, so payers then open fresh channels. */
export const addressInbox = (address: Uint8Array, notifyKey: Uint8Array): Uint8Array =>
  taggedHash('zerc20/storage/inbox/v1', [address, notifyKey]);

/** The payer's seed for its channel to `inbox`, recomputable from the payer's view key alone. */
export const channelSeed = (seed: Uint8Array, payer: Uint8Array, inbox: Uint8Array): Uint8Array =>
  kdf(seed, 'channel', [payer, inbox]);

/** A channel's lane key. Binding the inbox and the claimed payer means a seed learned from one channel opens
 * nothing when replayed into another inbox or under another name. */
export const channelKey = (channelSeed: Uint8Array, inbox: Uint8Array, payer: Uint8Array): Uint8Array =>
  kdf(channelSeed, 'channel-key', [inbox, payer]);

/** The lane key of receive code `index` (burn index `index` of `tokenId` on `chainId`). Every payer of the code
 * writes its notes to this one lane, and the owner finds them through the log: no inbox, no announcement. */
export const codeKey = (seed: Uint8Array, chainId: bigint, tokenId: number, index: number): Uint8Array =>
  kdf(seed, 'code', [u64be(chainId), u32be(tokenId), u32be(index)]);

/** The owner's own lane key: notes to self (merge outputs and change) and burn blocks, which only the owner's
 * devices write and read. */
export const ownKey = (seed: Uint8Array): Uint8Array => kdf(seed, 'own');

/** The key the owner's own burn addresses derive from. It only makes salts, which cannot spend, so it is derived from
 * the view key: a wallet hands out burn addresses while its seed is away. */
export const burnKey = (seed: Uint8Array): Uint8Array => kdf(seed, 'burn');

/** The key of the owner's point of sale `n`, handed to that point of sale alone: its burn key, and the key of the lane
 * where it records the addresses it makes for the owner, ahead of handing them out. */
export const posKey = (seed: Uint8Array, n: number): Uint8Array => kdf(seed, 'pos', [u32be(n)]);

/** The slot of record `slotIndex` on `chainId` in the lane of `laneKey`. */
export const slotId = (laneKey: Uint8Array, chainId: bigint, slotIndex: number): Uint8Array =>
  kdf(laneKey, 'slot', [u64be(chainId), u32be(slotIndex)]);
export const sealKey = (laneKey: Uint8Array): Uint8Array => kdf(laneKey, 'seal');

export const outgoingId = (seed: Uint8Array, index: number): Uint8Array => kdf(seed, 'outgoing-id', [u32be(index)]);
export const outgoingKey = (seed: Uint8Array): Uint8Array => kdf(seed, 'outgoing');

/** Slot `index` of the seeds kept for a passkey, from its PRF output `prf`: the passkey alone finds them, on any device
 * it syncs to. The canister is bound in, as for view keys, so that the same passkey's slots in two canisters do not
 * match. */
export const passkeySeedId = (prf: Uint8Array, canister: Principal, index: number): Uint8Array =>
  kdf(prf, 'passkey-seed-id', [canister.toUint8Array(), u32be(index)]);
export const passkeySeedKey = (prf: Uint8Array, canister: Principal): Uint8Array =>
  kdf(prf, 'passkey-seed', [canister.toUint8Array()]);

// ---- records ----

/** What an on-chain note commits to besides its owner's `public_key`:
 * `note_hash = Poseidon(chain_id, public_key, value, token_id, note_salt)`. */
export interface NoteOpening {
  chainId: bigint;
  tokenId: number;
  /** Big-endian, below 2^248 (its first byte is 0). */
  value: Uint8Array;
  /** Big-endian canonical `Fr` element, fresh for every note. */
  noteSalt: Uint8Array;
}

/** What a payment, withdrawal or merge was, kept on its note to self (its change, even of zero value, or a merge's
 * output), so that every device of the owner shows it: that note on chain says it landed. */
export interface Receipt {
  kind: 'sent' | 'sent-to-code' | 'withdrawn' | 'unwrapped' | 'merged';
  /** Big-endian, below 2^248, as a note's value: what was paid or withdrawn, or what a merge's note holds. */
  amount: Uint8Array;
  /** The same: what the relayer was paid for it. */
  fee: Uint8Array;
  /** Whom it paid: an address, a receive code's burn address, or for a merge 20 zero bytes. */
  counterparty: Uint8Array;
}

/** What the owner did that leaves no note to self, kept in the own lane so that every device of the owner shows it:
 * a deposit into its burn address returned to its sender (a rage exit), or a deposit address it registered for one. */
export type OwnReceipt = { chainId: bigint; tokenId: number; burnAddress: Uint8Array } & (
  | {
      kind: 'returned';
      /** The deposit's `commitment_index`. */
      index: number;
      recipient: Uint8Array;
      /** Big-endian, below 2^248. */
      amount: Uint8Array;
      txHash: Uint8Array;
    }
  | {
      kind: 'deposit-address';
      depositAddress: Uint8Array;
      /** Absent where the record does not tell them. */
      args?: DepositArgs;
    }
);

/** What a deposit address was registered with besides its token and burn address: with those, all the factory derives
 * it from, so all a flush of it takes, without the relayer that registered it. */
export interface DepositArgs {
  /** Big-endian, below 2^248: what the relayer takes out of each payment through it. */
  fee: Uint8Array;
  feeRecipient: Uint8Array;
  /** The key that signs where each refund goes. */
  refundSigner: Uint8Array;
  /** The app that handed it out, and its share of what is left after the fee (bps); zero where no app did. */
  referrer: Uint8Array;
  referralBps: number;
}

/** Where a record sat in its lane, and when the canister first stored it (kept in the clear). */
interface Stamped {
  /** Position in the lane's sequence for its chain (0, 1, 2, …), which locates its slot. Not the on-chain
   * `commitment_index`; slots that do not open leave gaps. */
  slotIndex: number;
  atNs: bigint;
}

export interface Note extends Stamped {
  kind: 'note';
  opening: NoteOpening;
  /** In a receive code's lane, the payer it claims to be (unverified). */
  payer?: Uint8Array;
  /** In the own lane, what it is the change or the output of; missing for a kind this version does not know. */
  receipt?: Receipt;
}

/** Not a note on chain: a deposit of `value` into the receiver's burn address of `burnSalt`, under the `public_key`
 * the payer looked up (zERC20-v2's `burn_address`), paid by a plain transfer. */
export interface Deposit extends Stamped {
  kind: 'deposit';
  chainId: bigint;
  tokenId: number;
  /** Big-endian, below 2^248, as a note's. */
  value: Uint8Array;
  burnSalt: Uint8Array;
  /** The burn address, which the receiver derives itself: for the payer's other devices, to find the transfer. */
  burnAddress: Uint8Array;
}

/** Burn addresses `first, first + 1, ..` of `tokenId` on `chainId`, by their salts, which their owner may have handed
 * out. Whoever hands one out records its block first, so every device of the owner finds the payments to it. Their
 * indices are those of zERC20-v2's `keys::derive_burn_address`: under the owner's `burnKey` in the own lane, under the
 * point of sale's key in its lane. Salts, because deriving an address takes about 2^16 hashes, and checking one from
 * its salt takes one. */
export interface BurnBlock {
  chainId: bigint;
  tokenId: number;
  first: number;
  /** 32 bytes each, 1 to `BURN_BLOCK` of them. */
  salts: Uint8Array[];
}

/** In the own lane: the owner made point of sale `n`, whose lane (`posKey`) its devices then read. */
export interface PosLane {
  n: number;
}

export type LaneRecord =
  | Note
  | Deposit
  | (BurnBlock & Stamped & { kind: 'burn-block' })
  | (OwnReceipt & Stamped)
  | (PosLane & Stamped & { kind: 'pos-lane' });

/** Which lane a record was read from: the records each holds, and who writes it. */
export type LaneKind = 'channel' | 'code' | 'own' | 'pos';

/** The lanes each record type belongs in. A code's notes name their payer, and only the own lane's say what they are
 * the change or the output of. */
const LANES: Record<number, LaneKind[]> = {
  [NOTE]: ['channel'],
  [CODE_NOTE]: ['code'],
  [SELF_NOTE]: ['own'],
  [DEPOSIT]: ['channel'],
  [BURN_BLOCK_RECORD]: ['own', 'pos'],
  [RETURNED]: ['own'],
  [DEPOSIT_ADDRESS]: ['own'],
  [POS_LANE]: ['own'],
};

/** `type ‖ body`, zero-padded to `size`. */
function record(type: number, body: Uint8Array, size = SLOT_PLAIN): Uint8Array {
  const out = new Uint8Array(size);
  out[0] = type;
  out.set(body, 1);
  return out;
}

/** A value's 31 bytes on the wire, or `null` if it is not below 2^248. */
function valueBytes(value: Uint8Array): Uint8Array | null {
  return value.length === 32 && value[0] === 0 ? value.subarray(1) : null;
}

const isField = (x: Uint8Array): boolean => x.length === 32 && compare(x, FR_BE) < 0;

const RECEIPTS: Receipt['kind'][] = ['sent', 'sent-to-code', 'withdrawn', 'unwrapped', 'merged'];

/** A value back from its 31 bytes on the wire. */
const wideValue = (b: Uint8Array): Uint8Array => concat(Uint8Array.of(0), b);

/** `kind(1) ‖ amount(31) ‖ fee(31) ‖ counterparty(20)`, or `null` if a field is out of range. */
function receiptBytes(r: Receipt): Uint8Array | null {
  const [amount, fee] = [valueBytes(r.amount), valueBytes(r.fee)];
  if (!amount || !fee || !RECEIPTS.includes(r.kind) || r.counterparty.length !== 20) return null;
  return concat(Uint8Array.of(RECEIPTS.indexOf(r.kind) + 1), amount, fee, r.counterparty);
}

/** The receipt in `b`, or `undefined` for a kind this version does not know: the note, which may be spendable change,
 * is kept all the same. */
function readReceipt(b: Uint8Array): Receipt | undefined {
  const kind = RECEIPTS[b[0] - 1];
  return (
    kind && {
      kind,
      amount: wideValue(b.subarray(1, 32)),
      fee: wideValue(b.subarray(32, 63)),
      counterparty: b.slice(63, 83),
    }
  );
}

/** A note's plaintext, `token_id(4) ‖ value(31) ‖ note_salt(32)`, or `null` if a field is out of the circuit's range
 * (an out-of-range field can hash like a different value). With `payer` it is a note to a receive code, naming its
 * payer; with `receipt`, a note to self, saying what it is the change or the output of. */
export function notePlaintext(
  opening: NoteOpening,
  extra: { payer: Uint8Array } | { receipt: Receipt } | null = null,
): Uint8Array | null {
  const value = valueBytes(opening.value);
  if (!value || !isField(opening.noteSalt)) return null;
  const body = concat(u32be(opening.tokenId), value, opening.noteSalt);
  if (!extra) return record(NOTE, body);
  if ('payer' in extra) return extra.payer.length === 20 ? record(CODE_NOTE, concat(body, extra.payer)) : null;
  const receipt = receiptBytes(extra.receipt);
  return receipt && record(SELF_NOTE, concat(body, receipt));
}

/** A deposit's announcement, `token_id(4) ‖ value(31) ‖ burn_salt(32) ‖ burn_address(20)`, or `null` if the value or
 * the salt is out of range. */
export function depositPlaintext(
  tokenId: number,
  value: Uint8Array,
  burnSalt: Uint8Array,
  burnAddress: Uint8Array,
): Uint8Array | null {
  const v = valueBytes(value);
  if (!v || !isField(burnSalt) || burnAddress.length !== 20) return null;
  return record(DEPOSIT, concat(u32be(tokenId), v, burnSalt, burnAddress));
}

/** `token_id(4) ‖ burn_address(20) ‖` then a return's `index(8) ‖ recipient(20) ‖ amount(31) ‖ tx_hash(32)`, or a
 * deposit address's `deposit_address(20) ‖ 1 ‖ args`, its zeros in place of `1 ‖ args` without them. */
export function ownReceiptPlaintext(r: OwnReceipt): Uint8Array {
  const amount = r.kind === 'returned' && valueBytes(r.amount);
  const args = r.kind === 'deposit-address' && r.args && depositArgsBytes(r.args);
  const rest =
    r.kind === 'returned'
      ? amount &&
        r.recipient.length === 20 &&
        r.txHash.length === 32 &&
        concat(u64be(BigInt(r.index)), r.recipient, amount, r.txHash)
      : r.depositAddress.length === 20 &&
        (r.args === undefined ? r.depositAddress : args && concat(r.depositAddress, Uint8Array.of(1), args));
  if (!rest || r.burnAddress.length !== 20)
    throw new Error('an own receipt holds 20-byte addresses, a 32-byte hash, values below 2^248 and a 16-bit rate');
  return record(r.kind === 'returned' ? RETURNED : DEPOSIT_ADDRESS, concat(u32be(r.tokenId), r.burnAddress, rest));
}

/** `fee(31) ‖ fee_recipient(20) ‖ refund_signer(20) ‖ referrer(20) ‖ referral_bps(2)`, or `null` if one is out of
 * range. */
function depositArgsBytes(a: DepositArgs): Uint8Array | null {
  const fee = valueBytes(a.fee);
  const addresses = [a.feeRecipient, a.refundSigner, a.referrer];
  const bps = Number.isInteger(a.referralBps) && a.referralBps >= 0 && a.referralBps <= 0xffff;
  return fee && bps && addresses.every((x) => x.length === 20) ? concat(fee, ...addresses, u16be(a.referralBps)) : null;
}

/** `token_id(4) ‖ first(4) ‖ count(1) ‖ salt(32) × count`. */
export function burnBlockPlaintext(b: BurnBlock): Uint8Array {
  if (b.salts.length === 0 || b.salts.length > BURN_BLOCK || b.salts.some((s) => s.length !== 32)) {
    throw new Error(`a burn block holds 1 to ${BURN_BLOCK} salts of 32 bytes`);
  }
  return record(BURN_BLOCK_RECORD, concat(u32be(b.tokenId), u32be(b.first), Uint8Array.of(b.salts.length), ...b.salts));
}

/** `n(4)`. */
export function posLanePlaintext(n: number): Uint8Array {
  return record(POS_LANE, u32be(n));
}

/** The record a slot of a `lane` lane on `chainId` held, or `null` if it is malformed or not one such a lane holds. */
export function readLaneRecord(
  lane: LaneKind,
  chainId: bigint,
  slotIndex: number,
  atNs: bigint,
  plain: Uint8Array,
): LaneRecord | null {
  const type = plain[0];
  if (plain.length !== SLOT_PLAIN || !LANES[type]?.includes(lane)) return null;
  const stamp = { slotIndex, atNs };
  const tokenId = readU32(plain, 1);
  if (type === BURN_BLOCK_RECORD) {
    const count = plain[9];
    if (count === 0 || count > BURN_BLOCK) return null;
    const salts = Array.from({ length: count }, (_, i) => plain.slice(10 + 32 * i, 42 + 32 * i));
    return { kind: 'burn-block', ...stamp, chainId, tokenId, first: readU32(plain, 5), salts };
  }
  if (type === POS_LANE) return { kind: 'pos-lane', ...stamp, n: readU32(plain, 1) };
  if (type === RETURNED || type === DEPOSIT_ADDRESS) {
    const head = { ...stamp, chainId, tokenId, burnAddress: plain.slice(5, 25) };
    if (type === DEPOSIT_ADDRESS) {
      const depositAddress = plain.slice(25, 45);
      if (plain[45] !== 1) return { ...head, kind: 'deposit-address', depositAddress };
      const args = {
        fee: wideValue(plain.subarray(46, 77)),
        feeRecipient: plain.slice(77, 97),
        refundSigner: plain.slice(97, 117),
        referrer: plain.slice(117, 137),
        referralBps: readU16(plain, 137),
      };
      return { ...head, kind: 'deposit-address', depositAddress, args };
    }
    const [recipient, amount, txHash] = [plain.slice(33, 53), wideValue(plain.subarray(53, 84)), plain.slice(84, 116)];
    return { ...head, kind: 'returned', index: Number(readU64(plain, 25)), recipient, amount, txHash };
  }
  // a note or a deposit
  const value = wideValue(plain.subarray(5, 36));
  const salt = plain.slice(36, 68);
  if (!isField(salt)) return null;
  if (type === DEPOSIT)
    return { kind: 'deposit', ...stamp, chainId, tokenId, value, burnSalt: salt, burnAddress: plain.slice(68, 88) };
  const note: Note = { kind: 'note', ...stamp, opening: { chainId, tokenId, value, noteSalt: salt } };
  if (type === CODE_NOTE) note.payer = plain.slice(68, 88);
  const receipt = type === SELF_NOTE && readReceipt(plain.subarray(68, 151));
  if (receipt) note.receipt = receipt;
  return note;
}

/** Where to pay: handed from receiver to payer over a trusted channel. It does not name the receiver, but whoever
 * swaps it in transit redirects the funds. Pay any amount, by a transfer to `burnAddress` (a deposit), or by a note
 * owned by `publicKey` written to the lane of `key`. */
export interface ReceiveCode {
  chainId: bigint;
  tokenId: number;
  /** zERC20-v2's `keys::derive_burn_address` address of the code's index. */
  burnAddress: Uint8Array;
  /** The zERC20 public key the paying note commits to: the code's own (`keys::code_spend_secret`), not the address's, so
   * codes cannot be linked to each other or to the address. */
  publicKey: Uint8Array;
  key: Uint8Array;
}

const codeBody = (c: ReceiveCode): Uint8Array => {
  if (c.burnAddress.length !== 20 || c.publicKey.length !== 32 || c.key.length !== 32)
    throw new Error('not a receive code');
  return concat(u64be(c.chainId), u32be(c.tokenId), c.burnAddress, c.publicKey, c.key);
};

const readCodeBody = (b: Uint8Array): ReceiveCode => ({
  chainId: readU64(b, 0),
  tokenId: readU32(b, 8),
  burnAddress: b.slice(12, 32),
  publicKey: b.slice(32, 64),
  key: b.slice(64, 96),
});

const CODE_PREFIX = 'zerc20';

/** A receive code as text: bech32m of `RECEIVE_CODE ‖ chain_id(8) ‖ token_id(4) ‖ burn_address(20) ‖ public_key(32) ‖
 * key(32)`, so a mistyped one fails its checksum instead of paying someone else. */
export function encodeCode(c: ReceiveCode): string {
  return bech32m.encode(CODE_PREFIX, bech32m.toWords(concat(Uint8Array.of(RECEIVE_CODE), codeBody(c))), false);
}

/** The receive code `text` holds, or `null` for anything else. */
export function decodeCode(text: string): ReceiveCode | null {
  try {
    const { prefix, bytes } = bech32m.decodeToBytes(text.trim(), false);
    if (prefix !== CODE_PREFIX || bytes.length !== 97 || bytes[0] !== RECEIVE_CODE) return null;
    return readCodeBody(bytes.subarray(1));
  } catch {
    return null;
  }
}

/** Where a payer paid, as its outgoing record keeps it: an address under one of its registrations (its notify key),
 * or a receive code. */
export type Target = { address: Uint8Array; notifyKey: Uint8Array } | ReceiveCode;

/** `address(20) ‖ notify_key(32)`, or the code's body. */
export function targetPlaintext(t: Target): Uint8Array {
  return 'address' in t ? record(SENT_TO_ADDRESS, concat(t.address, t.notifyKey)) : record(SENT_TO_CODE, codeBody(t));
}

export function readTarget(plain: Uint8Array): Target | null {
  if (plain.length !== SLOT_PLAIN) return null;
  if (plain[0] === SENT_TO_ADDRESS) return { address: plain.slice(1, 21), notifyKey: plain.slice(21, 53) };
  if (plain[0] === SENT_TO_CODE) return readCodeBody(plain.subarray(1, 97));
  return null;
}

/** `seed(32)`. */
export function passkeySeedPlaintext(seed: Uint8Array): Uint8Array {
  if (seed.length !== 32) throw new Error('a seed is 32 bytes');
  return record(PASSKEY_SEED, seed);
}

export function readPasskeySeed(plain: Uint8Array): Uint8Array | null {
  return plain.length === SLOT_PLAIN && plain[0] === PASSKEY_SEED ? plain.slice(1, 33) : null;
}

/** A channel's announcement, `payer(20) ‖ channel_seed(32)`: who claims to open it, and the seed its lane key derives
 * from. */
export function channelPlaintext(payer: Uint8Array, seed: Uint8Array): Uint8Array {
  return record(CHANNEL, concat(payer, seed), ANNOUNCE_PLAIN);
}

export function readChannel(plain: Uint8Array): { payer: Uint8Array; seed: Uint8Array } | null {
  if (plain.length !== ANNOUNCE_PLAIN || plain[0] !== CHANNEL) return null;
  return { payer: plain.slice(1, 21), seed: plain.slice(21, 53) };
}

/** How records reach a receiver: through a channel to its address, a receive code's lane, or the lane of one of its
 * points of sale. The code's owner knows it by its token and burn index; a payer by the code itself. */
export type Via =
  | { type: 'address' }
  | { type: 'code'; chainId: bigint; tokenId: number; index: number }
  | { type: 'code'; code: ReceiveCode }
  | { type: 'pos'; n: number };
