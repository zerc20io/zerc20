// zerc20-storage SDK: private note delivery for zERC20 on the Internet Computer.
//
// - View keys (`registeredViewKey`): an address's key, derived from its zERC20 root seed. Everything only the owner can
//   compute derives from it. Registering (one wallet signature) publishes what payers need: the address's zERC20
//   public key and the key announcements are encrypted to, which payers look up with `lookupRecipient`. It also
//   escrows the view key to the auditor.
// - History (`refresh`): both sides recover their channels and records from the view key alone, and each refresh
//   reads only what is new. Keep the state with `exportState`.
// - Payments (`planSend`, `planDeposit`, `planPayCode`, and `planSelf` for merge outputs and change, with what each
//   was), submitted with `commit`; `planReceipt` for what leaves no note to self.
// - Burn blocks (`planBurnBlock`): which burn addresses the owner's devices hand out, made from `burnKey`. Each of a
//   wallet's own is also a receive code (`encodeCode`), paid by a deposit or by a note, any amount, any number of
//   times.
// - Points of sale (`planPosLane`): a lane whose key (`posKey`) the owner hands to one point of sale, which records
//   there the burn addresses it hands out (`writePosBlocks`), for every device of the owner to find.
//
// Payers are not verified: a record's `peer` is only what was claimed.

export type { Action, AuditRecord, AuditRequest, CanisterError, Kind, Registration, Service, Slot } from './candid.js';
export { idlFactory } from './candid.js';
export { CanisterClient, StorageError } from './canister.js';
export {
  BURN_BLOCK,
  FR_BE,
  addressInbox,
  codeKey,
  decodeCode,
  burnKey,
  encodeCode,
  posKey,
  type BurnBlock,
  type Deposit,
  type DepositArgs,
  type LaneRecord,
  type Note,
  type NoteOpening,
  type OwnReceipt,
  type PosLane,
  type Receipt,
  type ReceiveCode,
  type Via,
} from './formats.js';
export { fetchPasskeySeed, storePasskeySeed } from './passkey.js';
export {
  commit,
  nextPosLane,
  planBurnBlock,
  planDeposit,
  planPayCode,
  planPosLane,
  planReceipt,
  planSelf,
  planSend,
  MAX_POS_BLOCKS,
  writePosBlocks,
} from './send.js';
export {
  type ChainLane,
  type NewRecord,
  type StoredLane,
  type SyncState,
  emptyState,
  exportState,
  importState,
  refresh,
} from './sync.js';
export {
  type Recipient,
  type Signer,
  type ViewKey,
  eip191Signer,
  lookupRecipient,
  notifyKey,
  notifySecret,
  openEscrow,
  registeredViewKey,
  register,
  verifyRegistration,
  viewKey,
} from './viewKey.js';
export {
  REGISTER_POW_BITS,
  actionsDigest,
  powOk,
  registerDigest,
  registerMessage,
  requiredPowBits,
  solvePow,
  vetkdInput,
} from './wire.js';
