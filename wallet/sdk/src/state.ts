// What a wallet keeps between sessions: one encrypted blob the app stores wherever it likes. Everything in it can
// be rebuilt from the seed and the account's address (given time and a birthday); it is a cache that keeps every
// sync incremental, plus the operations in flight, which are written before each step that leaves the device.

import { chacha20poly1305 } from '@noble/ciphers/chacha.js';
import { hkdf } from '@noble/hashes/hkdf.js';
import { sha256 } from '@noble/hashes/sha2.js';
import { bytesToHex, hexToBytes, randomBytes } from '@noble/hashes/utils.js';
import type { Receipt, SyncState } from '@zerc20/storage-sdk';
import type { Hex } from 'viem';
import type { Token } from './chain.js';
import type { ErrorCode } from './errors.js';
import type { Watch } from './scan.js';
import type { SpendData } from './spend.js';

/** Where a note or deposit sits in the commitment tree. */
export interface Position {
  index: number;
  /** Seen past the final count: a reorg may still move it. */
  tentative: boolean;
  /** Set once spent: by this wallet, or seen among the nullifiers. */
  spent: boolean;
  /** Looking for its nullifier, once final. */
  nullifier?: Watch;
  /** Where among the nullifiers its own was seen past the final count: spent by a JoinSplit in a block, which a reorg
   * may still drop. */
  nullifiedAt?: number;
  /** Its block's time (ms), read with its commitment: the same on every device. Unset until read. */
  atMs?: number;
  /** Found by a sync of its chain that has not ended: whether it is spent is looked for only later in that sync, so it
   * is not known to be unspent until then. Kept where that sync fails, until one ends. */
  unchecked?: true;
}

/** Known to be neither spent nor spent by a JoinSplit in a block (one waits only to be final, so it is gone already):
 * what a found note or deposit is once the sync that found it has looked for its spend. */
export const unspent = (f: Position): boolean => !f.spent && f.nullifiedAt === undefined && !f.unchecked;

/** What a payment, withdrawal or merge was, kept on its change or merged note in storage (the storage SDK's
 * `Receipt`): every device of the wallet shows it once that note lands. */
export interface NoteReceipt {
  kind: Receipt['kind'];
  amount: bigint;
  fee: bigint;
  /** Whom it paid: an address, or a receive code's burn address; zero for a merge. */
  counterparty: Hex;
}

/** A note this wallet may own: announced through storage (to its address or one of its receive codes), or a note to
 * self. */
export interface NoteRecord {
  chainId: bigint;
  tokenId: number;
  value: bigint;
  salt: Hex;
  source: 'received' | 'self';
  /** For a note to self, what it is the change or the output of. */
  receipt?: NoteReceipt;
  /** Who the payer claimed to be (unverified), if anyone. */
  peer: Hex | null;
  /** When storage first held it (ns), for notes it delivered. */
  atNs: bigint | null;
  /** For a note paid to a receive code, the code's index: the code's own key owns it. Otherwise the wallet's key does. */
  keyIndex?: number;
  /** Paid to a receive code whose key was not derived when storage told of it (another device's code, while the seed
   * was not held): its hash and watch wait for the seed, and nothing counts it until then. */
  unkeyed?: true;
  /** Its hash under the key that owns it. */
  noteHash: Hex;
  /** Its tag, watched until it is found where no reorg moves it. */
  watch: Watch | null;
  /** Found in the tree, and `confirmed` once its commitment was read: a 4-byte tag can match someone else's. */
  found: (Position & { confirmed?: boolean })[];
}

/** A burn address of this wallet and what was sent to it. */
export interface DepositRecord {
  chainId: bigint;
  /** The token it was handed out for, whose burn indices it counts in. Transfers of any token to it are found and
   * spendable. */
  tokenId: number;
  burnIndex: number;
  salt: Hex;
  address: Hex;
  createdMs: number;
  /** A deposit-relayer address that flushes into it, if one was registered. */
  depositAddress: Hex | null;
  /** Handed out by one of this wallet's points of sale, which recorded it in its lane (a burn block, `burnIndex` -1):
   * paid by deposit only. The wallet's own are recorded in its own lane, from 0 up, and each is also a receive code. */
  managed?: true;
  /** Chosen by a payer, who told it in storage (a burn), as claimed: its salt is the payer's, with no index
   * (`burnIndex` -1), and it is never handed out. */
  payer?: Hex;
  /** Recorded by another device of the wallet, or before a restore: taken as handed out, so never handed out here. A
   * flag of its own rather than the token's `burnNext`, which would also pass the one this device recorded ahead and
   * still holds: with two devices open, each would then record one more ahead each sync, without end. */
  elsewhere?: true;
  /** The transfer's tag under each token. */
  watches: { tokenId: number; watch: Watch }[];
  found: (Position & {
    tokenId: number;
    sender: Hex | null;
    amount: bigint | null;
    /** The ASP's decision, once it has made one: only an approved deposit is spent privately. */
    asp: 'approved' | 'rejected' | null;
    /** Until then, when it should come (ms): an estimate. */
    decidedByMs?: number;
  })[];
}

/** A deposit this wallet paid into someone else's burn address (`deposit({ to })`), as storage keeps it for every
 * device of the wallet: its transfer is watched as a deposit's is, to show once it landed, and never spent. */
export interface SentRecord extends Pick<
  DepositRecord,
  'chainId' | 'tokenId' | 'address' | 'createdMs' | 'watches' | 'found'
> {
  /** Whom it paid. */
  to: Hex;
}

/** What this wallet did that leaves no note to self, kept in storage's own lane so that every device of the wallet
 * shows it: a deposit returned to its sender by rage exit, or a deposit address registered for a burn address.
 * `unwritten` until storage holds it: every sync tries again. */
export type ReceiptRecord = { chainId: bigint; tokenId: number; burnAddress: Hex; atMs: number; unwritten?: true } & (
  | { kind: 'returned'; index: number; recipient: Hex; amount: bigint; txHash: Hex }
  | {
      kind: 'deposit-address';
      depositAddress: Hex;
      /** From the relayer's answer, or as storage told them. Absent where storage's record does not tell them, and then
       * only the relayer flushes it. */
      args?: DepositAddressArgs;
    }
);

/** What a deposit address was registered with besides its token and burn address: with those, all a flush of it takes.
 * A wallet's refunds go where a signer of its own signs for, so its refund address is zero. */
export interface DepositAddressArgs {
  fee: bigint;
  feeRecipient: Hex;
  refundSigner: Hex;
  referrer: Hex;
  referralBps: number;
}

export type DepositAddressReceipt = Extract<ReceiptRecord, { kind: 'deposit-address' }>;

/** A sample of the indexer's final counts, to bound where a note announced at some time can be. */
export interface Sample {
  atMs: number;
  commitments: number;
  nullifiers: number;
}

export interface ChainState {
  chainId: bigint;
  samples: Sample[];
  /** The next burn address index, per token. */
  burnNext: Record<number, number>;
  /** The chain's tokens as last read: what the records here name by id, kept so that they still show while the chain's
   * RPCs do not answer. */
  tokens?: Token[];
}

/** An operation's progress, written before every step that leaves the device, so `sync` can resume it. */
export type OperationRecord = DepositOperation | SpendOperation;

interface OperationBase {
  id: string;
  chainId: bigint;
  tokenId: number;
  amount: bigint;
  createdMs: number;
  status: 'pending' | 'done' | 'failed';
  error?: string;
  /** Why it failed, for the app to act on. */
  errorCode?: ErrorCode;
  /** While pending: why its next step keeps not going through, tried again every sync, and since when. */
  retrying?: { message: string; code?: ErrorCode; sinceMs: number };
}

/** A deposit from the account into a burn address. */
export interface DepositOperation extends OperationBase {
  kind: 'deposit';
  data: {
    burnAddress: Hex;
    /** Whose burn address it is, when not this wallet's (`deposit({ to })`). */
    to?: Hex;
    /** The receive code it paid, when `to` was one. */
    code?: string;
    /** Its transaction, once sent. */
    txHash?: Hex;
    /** What the burn address held before it was sent, in the token. */
    held?: bigint;
    /** Its sender and nonce, as a node held it waiting to be mined. */
    sent?: { from: Hex; nonce: number };
  };
}

/** JoinSplits, one step at a time: a send or a withdrawal's one, a consolidation's rounds. */
export interface SpendOperation extends OperationBase {
  kind: 'send' | 'withdraw' | 'consolidate';
  data: SpendData;
}

export interface WalletState {
  version: 1;
  address: Hex;
  /** The note storage history, `null` until its first refresh. */
  storage: SyncState | null;
  chains: ChainState[];
  notes: NoteRecord[];
  deposits: DepositRecord[];
  sent: SentRecord[];
  receipts: ReceiptRecord[];
  ops: OperationRecord[];
}

export const emptyWalletState = (address: Hex): WalletState => ({
  version: 1,
  address,
  storage: null,
  chains: [],
  notes: [],
  deposits: [],
  sent: [],
  receipts: [],
  ops: [],
});

const TAG = new TextEncoder().encode('zerc20/wallet/state/v1');
/** The key the state is sealed under: the seed's, kept while the seed is not, so that a sync saves without it. */
export const stateKey = (seed: Uint8Array) => hkdf(sha256, seed, TAG, new TextEncoder().encode('wallet-state'), 32);

/** `state` as bytes only the seed's `stateKey` opens: `nonce(12) ‖ ChaCha20-Poly1305(JSON)`. */
export function sealState(key: Uint8Array, state: WalletState): Uint8Array {
  const json = JSON.stringify(state, (_, v: unknown) =>
    typeof v === 'bigint' ? { $n: v.toString() } : v instanceof Uint8Array ? { $b: bytesToHex(v) } : v,
  );
  const nonce = randomBytes(12);
  const sealed = chacha20poly1305(key, nonce, TAG).encrypt(new TextEncoder().encode(json));
  return new Uint8Array([...nonce, ...sealed]);
}

/** The state `sealState` wrote, or `null` if `bytes` is not one `key` opens. */
export function openState(key: Uint8Array, bytes: Uint8Array): WalletState | null {
  try {
    const plain = chacha20poly1305(key, bytes.subarray(0, 12), TAG).decrypt(bytes.subarray(12));
    const state = JSON.parse(new TextDecoder().decode(plain), (_, v: unknown) => {
      if (typeof v === 'object' && v !== null && '$n' in v) return BigInt(v.$n as string);
      if (typeof v === 'object' && v !== null && '$b' in v) return hexToBytes(v.$b as string);
      return v;
    }) as WalletState;
    return state.version === 1 ? state : null;
  } catch {
    return null;
  }
}
