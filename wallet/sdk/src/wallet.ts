// The wallet an app works with. Amounts are bigints in a token's base units.

import {
  CanisterClient,
  type Signer,
  type SyncState,
  codeKey,
  commit,
  decodeCode,
  encodeCode,
  lookupRecipient,
  nextPosLane,
  notifyKey,
  planDeposit,
  planPosLane,
  posKey,
  registeredViewKey,
} from '@zerc20/storage-sdk';
import {
  type Account,
  type Address,
  type Hex,
  type LocalAccount,
  type WalletClient,
  bytesToHex,
  encodeFunctionData,
  formatUnits,
  getAddress,
  hexToBytes,
  isAddress,
  isAddressEqual,
  numberToHex,
  zeroAddress,
} from 'viem';
import { toAccount } from 'viem/accounts';
import { idAccount } from './accountId.js';
import {
  Chain,
  MAX_REFERRAL_BPS,
  NATIVE,
  type Reach,
  type Referrer,
  type Token,
  erc20Abi,
  fetchOf,
  tokenAbi,
} from './chain.js';
import {
  type ChainCtx,
  type Ctx,
  type SpendKey,
  chainCtx,
  chainState,
  owner,
  refundSigner,
  walletOn,
  walletSees,
} from './context.js';
import { burnAddressFor, core, initCore } from './core.js';
import { type ErrorCode, WalletError, fail, failsOperation, guard } from './errors.js';
import { type Network, checkNetwork } from './network.js';
import { preload } from './prove.js';
import { Asp, Indexer, type IndexerStatus, PAGE } from './servers.js';
import { type Route, flushDepositAddress, rageExit, refundDepositAddress } from './rageExit.js';
import { Relaying, registerDeposit, relayerFees, rewatchDeposit } from './services.js';
import {
  type Destination,
  type MergeStep,
  type SpendData,
  type Step,
  advanceSpend,
  bpsOf,
  cancellable,
  chosenSettling,
  coins,
  feesOf,
  grossed,
  inputsOf,
  landed,
  maxPayment,
  mergePool,
  mergeRound,
  minedInputsOf,
  payWith,
  planStep,
  roundsToMerge,
  settling,
  withdrawalOf,
} from './spend.js';
import {
  type DepositAddressReceipt,
  type DepositOperation,
  type DepositRecord,
  type OperationRecord,
  type WalletState,
  emptyWalletState,
  openState,
  sealState,
  stateKey,
  unspent,
} from './state.js';
import {
  WAIT_MS,
  commitmentTx,
  keyAll,
  nextBurn,
  recordBurn,
  storageState,
  syncAll,
  takeRefresh,
  tokenIds,
  topUpBurns,
  unusedBurn,
} from './sync.js';
import { decodeViewKey, encodeViewKey } from './viewKey.js';

/** The ledger's bound outside an emergency. */
const NO_BOUND = 2n ** 64n - 1n;

export interface OpenOptions extends Reach {
  network: Network;
  /** The account's key, held by the app as a viem local account (a private key's, or `accountKey`'s): the wallet sends
   * its transactions through each chain's RPC. Give this or `walletClient`. */
  account?: LocalAccount;
  /** The user's wallet (MetaMask, WalletConnect, ...) as a viem client with its account, which the wallet switches to
   * each chain it sends on. */
  walletClient?: WalletClient;
  /** The 32-byte root of every key (see `seedFromSignature`), held while the wallet is open. Or a function that gives
   * it, a passkey's say, to hold the seed only while it is needed: asked as the wallet opens, and again to pay,
   * withdraw, consolidate or exit, or for a receive code past those derived ahead, each time before the call waits on
   * anything (a browser shows a passkey prompt only in the click that asked). The seed goes at the end of a sync that
   * nothing waits behind, once nothing in flight signs again. */
  seed: Uint8Array | (() => Promise<Uint8Array>);
  /** Where the encrypted state lives between sessions. */
  persist: { load(): Promise<Uint8Array | null | undefined>; save(bytes: Uint8Array): Promise<void> };
  /** Where a wallet with no saved state starts looking: the block its seed was first used at, or roughly when. Without
   * it, an address registered before is looked for from the chain's start, and a new one from now on. */
  birthday?: bigint | Date;
  /** The app opening the wallet, when it takes a share of what reaches the deposit addresses it hands out. */
  referrer?: Referrer;
  /** Takes the wallet from another tab or window that holds it open, whose `taken` aborts, rather than failing with
   * `wallet-in-use`: for a user who opens it here, where the other may be a tab the browser keeps in the background. */
  take?: boolean;
}

export interface WatchOptions extends Pick<OpenOptions, 'network' | 'persist' | 'birthday'>, Reach {
  /** The account's view key, from its wallet's `viewKey()`. */
  viewKey: string;
}

/** What a deposit, or a deposit address, waits on: for an app to show while it does. */
export type DepositStep =
  /** Behind another call of this wallet: a sync, or another operation. */
  | 'queued'
  /** Recording a fresh burn address in storage first, a proof of work then a storage write (seconds). Only when none
   * was recorded ahead, as on a token's first deposit, or a second one before a sync has recorded the next. */
  | 'burn-address'
  /** The wallet is asked to approve the token to take the underlying asset; then the approval is mined (a block). */
  | 'approve'
  /** The wallet is asked to send the wrap into the burn address, or with `wrapped`, the transfer. */
  | 'wrap';

/** Why an amount is not spendable yet. */
export type PendingReason =
  /** A note this device's payment, withdrawal or merge under way is making, not yet read on chain. */
  | 'incoming'
  /** Waiting for a proved root that covers it (minutes). */
  | 'awaiting-root'
  /** Waiting for a proved root, which none will be until the protocol recovers: a forged root was proved, and the
   * protocol is in an emergency. A deposit can be rage-exited meanwhile. */
  | 'roots-halted'
  /** A deposit the ASP has not decided on yet. */
  | 'screening';

export interface Balance {
  token: Token;
  spendable: bigint;
  pending: { amount: bigint; reason: PendingReason }[];
  /** Deposits the ASP rejected: only `rageExit` returns them, to their sender. */
  blocked: bigint;
}

export interface Activity {
  /** The same across syncs and on every device of the wallet: `kind:chainId:index` of the commitment it made or found
   * (a payment's or withdrawal's: its change's). One shown from this device's operation has the operation's id. */
  id: string;
  /** `sale`: a payment to an address one of this wallet's points of sale handed out. `merged`: a consolidation folded
   * notes and deposits into one note. `returned`: a deposit rage-exited to its sender. */
  kind: 'received' | 'sent' | 'deposited' | 'sale' | 'withdrawn' | 'merged' | 'returned';
  token: Token;
  amount: bigint;
  /** What a payment, withdrawal or merge cost besides `amount`: the relayer's fee and the protocol's cut. Null where it
   * paid none. */
  fee: bigint | null;
  /** The other side, where known: a payer's claimed address (unverified), where a payment or withdrawal went, or whom a
   * returned deposit went back to. A payment's other side, `sent`'s or that of a `received` with no `burnAddress`, is a
   * zERC20 account, which an app shows by its zERC20 ID (`accountId`); any other is a public address. */
  counterparty: Address | null;
  /** What the counterparty alone does not say: the receive code a payment went to (it has no counterparty), or the
   * deposit address a deposit came through (its counterparty, which forwarded what was sent to it). */
  via: { code: string } | { depositAddress: Address } | null;
  /** The burn address of this wallet's that a deposit or a sale reached: for a sale, its id at the point of sale. */
  burnAddress: Address | null;
  /** When it reached the chain: its block's time. Until that is read, when storage recorded it; for a failed attempt,
   * when it started. */
  at: Date | null;
  /** Its place in the commitment tree, `chainId:index`: a deposit's (also a returned one's), a note's received or
   * merged, or a payment's or withdrawal's change. */
  coin: string | null;
  /** Its transaction, where the wallet keeps it: a rage exit's, or one shown from this device's operation.
   * `transaction` finds any. */
  txHash: Hex | null;
  /** `done` once on chain (in a block: a reorg may still take it back until final), `failed` for a payment or
   * withdrawal that cannot land, shown only on the device that tried it. What is not on chain yet is not activity:
   * an operation under way is in `operations()`, and the note it is making `incoming` in `balances()`. */
  status: 'done' | 'failed';
}

/** An unspent note or deposit on chain: what payments and consolidations spend, now or once it settles. */
export interface CoinInfo {
  /** Its place in the commitment tree, `chainId:index`. A deposit's is the id `rageExit` and `consolidate` take. */
  id: string;
  kind: 'note' | 'deposit';
  token: Token;
  amount: bigint;
  /** Spendable, why not yet, `spending` (an input of an operation under way), or `blocked` (a deposit the ASP
   * rejected: only `rageExit` returns it). */
  state: 'spendable' | Exclude<PendingReason, 'incoming'> | 'spending' | 'blocked';
  /** A note's payer (as claimed, unverified) or a deposit's sender, where known. */
  from: Address | null;
  /** The deposit address of this wallet's that a deposit came through (its `from`), as `Activity.via` names it: its
   * `rageExit` goes where `to` says. */
  via: { depositAddress: Address } | null;
  /** While `screening` or `awaiting-root`, when it should be spendable: the later of its AML check's deadline and when a
   * root should cover it, by how long commitments on its chain usually wait for one. An estimate: null until there is
   * one, and in other states. */
  readyBy: Date | null;
  /** When it landed: its block's time, null until read. */
  at: Date | null;
}

/** A coin on its way to spendable by itself: screening or settling, which `readyBy` has an estimate for. */
const onItsWay = (c: CoinInfo) => c.state === 'screening' || c.state === 'awaiting-root';

const total = (coins: CoinInfo[]) => coins.reduce((s, c) => s + c.amount, 0n);

/** Of `coins`, the one whose turning spendable makes them `need`, the soonest first; null where they never do, or the
 * one it takes has no estimate. */
export function waitsOn(coins: CoinInfo[], need: bigint): CoinInfo | null {
  const at = (c: CoinInfo) => c.readyBy?.getTime() ?? Infinity;
  // two coins with no estimate compare as equal, not as NaN
  const soonest = [...coins].sort((a, b) => Math.sign(at(a) - at(b)) || 0);
  let left = need;
  for (const c of soonest) {
    left -= c.amount;
    if (left <= 0n) return c.readyBy ? c : null;
  }
  return null;
}

export interface DepositInfo {
  id: string;
  /** The burn address it was sent to. */
  address: Address;
  /** Handed out by one of this wallet's points of sale (`posKey`), rather than for this wallet's own use. */
  managed: boolean;
  token: Token;
  /** Unknown until its commitment is read: a sync after it lands. It is read again once final. */
  amount: bigint | null;
  sender: Address | null;
  state: 'screening' | 'approved' | 'rejected' | 'spent';
}

export interface DepositAddressInfo {
  address: Address;
  token: Token;
  /** What the relayer takes out of each payment through it. Null where its receipt in storage does not say what it was
   * registered with: `flushDepositAddress` needs that, so only the relayer flushes such an address. */
  fee: bigint | null;
  /** When it was handed out, or watched again (`rewatchDepositAddress`), from which the deposit relayer watches it for
   * 7 days: when storage took its receipt. */
  at: Date;
}

/** A send's or withdrawal's recipient gets all of its amount, and the private balance pays `fee` on top. */
export interface FeeQuote {
  /** To the relayer. */
  relayer: bigint;
  /** The protocol's cut of the public withdrawal: a withdrawal's, or the one that pays the relayer. */
  protocol: bigint;
  /** `protocol` as a rate of that withdrawal, in basis points (35 is 0.35%): lower in tiers as the withdrawal grows. */
  protocolBps: number;
  /** `relayer + protocol`: the `maxFee` this quote passes. */
  fee: bigint;
  /** Transactions needed: one JoinSplit for a send or a withdrawal, a consolidation's merges (each pays the relayer's
   * fee again). */
  steps: number;
}

/** The most a send or withdrawal can pay now, and what its fees keep back of what is spendable. */
export interface MaxAmount {
  /** What the recipient would get: 0 where the fees take everything. */
  amount: bigint;
  /** The fees: the payment's, and those of the merges it needs first. Where they take everything, what they would be. */
  fee: bigint;
  /** Merges first, when one JoinSplit cannot spend all of it: each pays the relayer again. */
  merges: number;
}

export type OperationKind = OperationRecord['kind'];
export type OperationStatus = OperationRecord['status'];
export type CoinState = CoinInfo['state'];

export interface Operation {
  readonly id: string;
  readonly kind: OperationKind;
  /** The chain it is on: its token's. */
  readonly chainId: bigint;
  readonly status: OperationStatus;
  readonly error: string | undefined;
  /** Why it failed, the code `wait()` throws. */
  readonly errorCode: ErrorCode | undefined;
  /** While pending, why its next step has kept failing since `since`: an error trying again may get past (a service
   * down, a server behind the chain, or one of the wallet's own it cannot tell apart). It is tried again every sync;
   * null once a try goes through or only waits. */
  readonly retrying: { message: string; code: ErrorCode | undefined; since: Date } | null;
  /** The transactions it sent so far: a deposit's, a payment's one, a consolidation's one per round. */
  readonly txHashes: Hex[];
  /** How far a send, withdrawal or consolidation round has come, for an app to show; null for a deposit, or between
   * rounds. It moves during a sync: read it while one runs. */
  readonly stage: Step['stage'] | MergeStep['stage'] | null;
  /** Whom a deposit pays, when `deposit({ to })` named an address; null otherwise. One to a receive code shows its code
   * as `via` in `activity()`. */
  readonly to: Address | null;
  /** Whether `cancel()` can still end it: a send, withdrawal or consolidation that has paid nothing and has no request
   * out to the relayer. It moves during a sync: read it while one runs. */
  readonly cancellable: boolean;
  /** Syncs until the operation is in a block: a deposit's transaction, a payment's or withdrawal's JoinSplit, or a
   * consolidation's merges once nothing is left to merge, its note under a proved root. A reorg may still drop it, and
   * the wallet's syncs then send it again: it stays `pending` until final, which `until: 'final'` waits for, minutes
   * later on a chain slow to finalize. Throws if the operation fails, and not for a chain or server out of reach
   * meanwhile, which `retrying` tells of where it holds the operation back. */
  wait(options?: { until?: 'mined' | 'final' }): Promise<void>;
  /** Ends it while `cancellable`, and does nothing once it is cancelled: it paid nothing, its notes and deposits are free
   * again, it leaves `operations()` and `activity()`, and `wait()` throws `cancelled`. Throws otherwise, and when the
   * wallet cannot save it, which leaves it under way. */
  cancel(): Promise<void>;
}

export class Wallet {
  readonly #ctx: Ctx;
  #tokens: Token[] = [];
  #status = new Map<bigint, IndexerStatus & { halted: boolean }>();
  #queue: Promise<unknown> = Promise.resolve();
  /** Calls running or queued. */
  #busy = 0;
  readonly #lock: Hold;
  #referrer: Referrer | undefined;
  readonly #unlock: (() => Promise<Uint8Array>) | undefined;
  #readOnly = false;
  #closed = new AbortController();

  /** A wallet over `ctx`, held by `lock`: by default held nowhere, as where there are no Web Locks. */
  private constructor(
    ctx: Ctx,
    unlock?: () => Promise<Uint8Array>,
    lock: Hold = { release: () => {}, taken: new AbortController().signal, guard: (f) => f() },
  ) {
    this.#ctx = ctx;
    this.#unlock = unlock;
    this.#lock = lock;
    lock.taken.addEventListener('abort', () => this.#closed.abort(lock.taken.reason));
  }

  /** Lets this wallet go, for another tab or another account here. This object is done with: what is
   * queued fails with `wallet-closed`, a burn address search stops, and the wallet is let go once the task under way
   * ends, so that two never write its state at once. */
  close(): Promise<void> {
    this.#closed.abort(new WalletError('wallet-closed', 'this wallet was closed: open it again'));
    return this.#queue.then(() => this.#lock.release());
  }

  /** Aborts once another tab or window takes this wallet (`take`), which closes it here: what is queued fails with
   * `wallet-taken`, a burn address search stops, and the task under way saves nothing more, as the other tab reads the
   * state and writes it now. */
  get taken(): AbortSignal {
    return this.#lock.taken;
  }

  get address(): Address {
    return this.#ctx.address;
  }

  /** The account's view key, for `watch` to follow it with on another device: whoever holds it sees what this wallet
   * shows, except the private payments to receive codes, and can spend none of it. Checksummed text (bech32m,
   * `zerc20view1…`). */
  viewKey(): string {
    return encodeViewKey(this.#ctx.view, owner(this.#ctx)!);
  }

  /** Whether this wallet only watches its account (`watch`): it shows what the account holds and spends nothing. */
  get readOnly(): boolean {
    return this.#readOnly;
  }

  /** Opens the wallet. The first time on this address, registers it for payments: one signature. */
  static async open(opts: OpenOptions): Promise<Wallet> {
    checkNetwork(opts.network);
    // the factory refuses these, which the relayer would report as its own failure
    const r = opts.referrer;
    if (r) {
      if (!isAddress(r.address, { strict: false }) || r.address.toLowerCase() === zeroAddress)
        fail('invalid', `the referrer ${r.address} is not an address to pay`);
      if (!Number.isInteger(r.bps) || r.bps < 0 || r.bps > MAX_REFERRAL_BPS)
        fail('invalid', `a referrer takes 0 to ${MAX_REFERRAL_BPS} bps, not ${r.bps}`);
    }
    if (!opts.account === !opts.walletClient) fail('invalid', 'give an account or a wallet client, one of the two');
    const account = opts.account ?? opts.walletClient!.account ?? fail('invalid', 'the wallet client has no account');
    // asked once the options are checked, and before anything is waited on: a browser shows a passkey prompt only in
    // the click that opened
    const seed = typeof opts.seed === 'function' ? await opts.seed() : opts.seed;
    if (seed.length !== 32) fail('invalid', 'the seed is 32 bytes');
    await initCore();
    const hold = await lockWallet(account.address, opts.network, 'wallet', opts.take);
    try {
      return await Wallet.#open(opts, seed, account, hold);
    } catch (e) {
      hold.release();
      throw e;
    }
  }

  static async #open(opts: OpenOptions, seed: Uint8Array, account: Account, hold: Hold): Promise<Wallet> {
    const address = account.address;
    const chains = chainsOf(opts.network, opts);
    const code = await chains[0]?.chain.client.getCode({ address });
    // an EIP-7702 delegated account is still an EOA that signs
    if (code && code !== '0x' && !code.startsWith('0xef0100'))
      fail('unsupported-account', 'contract accounts cannot sign for a wallet');
    const signer: Signer = async (message) =>
      hexToBytes(
        await guard(
          account.type === 'local'
            ? account.signMessage({ message })
            : opts.walletClient!.signMessage({ account, message }),
        ),
      );
    const fetch = fetchOf(opts);
    const storage = await CanisterClient.connect(opts.network.storage.host, opts.network.storage.canisterId, fetch);
    const publicKey = hexToBytes((core.spendKey(seed) as SpendKey).publicKey);
    const saved = await hold.guard(() => opts.persist.load());
    // registered already: used before, here or on another device, so its past is looked for
    // ponytail: from genesis (~4 MB per million commitments); ask for a birthday once the chain has many
    const restoring =
      !saved?.length && opts.birthday === undefined && !!(await storage.registration(hexToBytes(address)));
    const view = await registeredViewKey(storage, seed, signer, hexToBytes(address), publicKey);
    const wallet = await Wallet.#begin(
      {
        network: opts.network,
        seed,
        owners: new Map(),
        refundSigners: new Map(),
        address,
        account,
        walletClient: opts.walletClient ?? null,
        storage,
        view,
        chains,
        fetch,
      },
      { persist: opts.persist, saved, key: stateKey(seed), from: restoring ? 0n : opts.birthday, hold },
      typeof opts.seed === 'function' ? opts.seed : undefined,
    );
    wallet.#referrer = opts.referrer;
    return wallet;
  }

  /** Opens an account to follow by its view key (`viewKey()`): its balances, coins and history as its own wallet shows
   * them, less the private payments to its receive codes, whose keys only the seed derives. It spends and writes
   * nothing: a call that would fails with `read-only`. The key must be the account's current one on this network. */
  static async watch(opts: WatchOptions): Promise<Wallet> {
    checkNetwork(opts.network);
    await initCore();
    const { view, owner } = decodeViewKey(opts.viewKey) ?? fail('invalid', 'not a view key');
    const address = getAddress(bytesToHex(view.address));
    const hold = await lockWallet(address, opts.network, 'view');
    try {
      const fetch = fetchOf(opts);
      const storage = await CanisterClient.connect(opts.network.storage.host, opts.network.storage.canisterId, fetch);
      // what the account signed: a nullifying key that is not the account's would show spent coins as unspent
      const r = await lookupRecipient(storage, view.address);
      if (!r || bytesToHex(r.publicKey) !== owner.publicKey || bytesToHex(r.notifyKey) !== bytesToHex(notifyKey(view)))
        fail('invalid', `not ${address}'s view key on ${opts.network.name}, or one it has replaced`);
      const wallet = await Wallet.#begin(
        {
          network: opts.network,
          seed: null,
          owners: new Map([['', owner]]),
          refundSigners: new Map(),
          address,
          // signs nothing: every call that would send is refused first
          account: toAccount(address),
          walletClient: null,
          storage,
          view,
          chains: chainsOf(opts.network, opts),
          fetch,
        },
        // registered, so its past is looked for
        {
          persist: opts.persist,
          saved: await hold.guard(() => opts.persist.load()),
          key: stateKey(view.seed),
          from: opts.birthday ?? 0n,
          hold,
        },
      );
      wallet.#readOnly = true;
      return wallet;
    } catch (e) {
      hold.release();
      throw e;
    }
  }

  /** The wallet over `base`, its state opened from what `persist` saved, with `key`, or started `from` a block or date,
   * as long as `hold` holds it. */
  static async #begin(
    base: Omit<Ctx, 'state' | 'save' | 'lastFullRefreshMs'>,
    {
      persist,
      saved,
      key,
      from,
      hold,
    }: {
      persist: OpenOptions['persist'];
      saved: Uint8Array | null | undefined;
      key: Uint8Array;
      from?: bigint | Date;
      hold: Hold;
    },
    unlock?: () => Promise<Uint8Array>,
  ): Promise<Wallet> {
    const loaded = saved?.length ? openState(key, saved) : null;
    // never started over in place: the first save would overwrite what it held, operations in flight included
    if (saved?.length && !loaded) {
      fail(
        'invalid',
        'the saved state does not open with this key (another seed or view key, a newer version, or damaged): clear it to start over, which finds what it held again',
      );
    }
    if (loaded && loaded.address.toLowerCase() !== base.address.toLowerCase())
      fail('invalid', `the saved state is ${loaded.address}'s: keep one per address`);
    const state: WalletState = loaded ?? emptyWalletState(base.address);
    const save = () => hold.guard(() => persist.save(sealState(key, state)));
    const ctx: Ctx = { ...base, state, save, lastFullRefreshMs: 0 };
    if (!loaded) await start(ctx, from);
    const wallet = new Wallet(ctx, unlock, hold);
    // a saved state names its tokens by id, and its coins stand by the chains' roots: read both now, so balances, coins
    // and history work before the first sync. A chain whose RPCs do not answer opens with the tokens saved of it, and a
    // fresh state, which names none, with none: the sync that reads the chain finds them
    const savedTokens = (chainId: bigint) => (loaded ? chainState(ctx, chainId).tokens : []);
    const [tokens] = await Promise.all([
      Promise.all(ctx.chains.map((c) => c.chain.tokens(savedTokens(c.config.chainId)))),
      wallet.#readRoots(),
    ]);
    wallet.#tokens = tokens.flat();
    keyAll(ctx, wallet.#tokens);
    // taken while it opened, before it listened
    hold.taken.throwIfAborted();
    return wallet;
  }

  /** Holds `seed`, asked of `#unlock`, once it is checked to be this wallet's. */
  #hold(seed: Uint8Array): void {
    if ((core.spendKey(seed) as SpendKey).publicKey !== owner(this.#ctx)!.publicKey)
      fail('invalid', "the seed given is another wallet's");
    this.#ctx.seed = seed;
    keyAll(this.#ctx, this.#tokens);
  }

  /** Within a task: the seed held, asked of `#unlock` if need be. */
  async #seed(): Promise<void> {
    if (!this.#ctx.seed) this.#hold(await this.#unlock!());
  }

  /** At the end of a sync: lets the seed go when it was opened with a function for it, nothing waits behind the sync,
   * and no payment, withdrawal or consolidation is in flight, as each may sign again (a JoinSplit that reverts is
   * proved again, and every merge round is signed). */
  #dropSeed(): void {
    if (!this.#unlock || this.#busy > 1) return;
    if (this.#ctx.state.ops.some((o) => o.status === 'pending' && o.kind !== 'deposit')) return;
    this.#ctx.seed = null;
  }

  /** `#exclusive` for a call that `needs` the seed: held first, asked of `#unlock` if need be before the call waits on
   * anything else (a browser shows a passkey prompt only in the click that asked), and queued in the step that took it,
   * so that a sync ending meanwhile does not let it go. */
  async #seeded<T>(f: () => Promise<T>, needs = true): Promise<T> {
    this.#writable();
    if (needs && !this.#ctx.seed) this.#hold(await this.#unlock!());
    return this.#exclusive(f);
  }

  /** Refuses a call that spends or writes to storage, in a wallet that watches. */
  #writable(): void {
    if (this.#readOnly) fail('read-only', 'this wallet watches its account by its view key: open it with its seed');
  }

  /** Runs `f` after everything queued before it: one state, changed by one task at a time. */
  #exclusive<T>(f: () => Promise<T>): Promise<T> {
    this.#busy++;
    const run = this.#queue
      .then(() => {
        this.#closed.signal.throwIfAborted();
        return f();
      })
      .finally(() => this.#busy--);
    this.#queue = run.catch(() => undefined);
    return run;
  }

  /** Each chain's latest proved root, which tells what is spendable, and whether the protocol is in an emergency. A
   * chain that does not answer keeps what was read before, and its error is returned. */
  async #readRoots(): Promise<unknown[]> {
    const errors: unknown[] = [];
    await Promise.all(
      this.#ctx.chains.map(async (c) => {
        try {
          const [status, bound] = await Promise.all([c.indexer.status(), c.chain.bound()]);
          // in an emergency the ledger accepts no root above its bound
          const latestRoot = status.latestRoot && BigInt(status.latestRoot.size) <= bound ? status.latestRoot : null;
          const halted = status.mismatch !== null || bound !== NO_BOUND;
          this.#status.set(c.config.chainId, { ...status, latestRoot, halted });
        } catch (e) {
          errors.push(e);
        }
      }),
    );
    return errors;
  }

  /** Catches up: new notes, deposits, spends and roots, then advances every operation in flight. A chain or server that
   * fails holds back only what needs it, and the first error is thrown once the rest is done. Settles before the burn
   * addresses are topped up, which can take a phone some seconds. */
  sync(): Promise<void> {
    return new Promise((resolve, reject) => {
      this.#exclusive(async () => {
        await this.#catchUp().then(resolve, reject);
        // still this task's: a deposit queued meanwhile finds the one recorded ahead, rather than writing at handout;
        // tried again after the next sync. A wallet that watches records none, as it writes nothing.
        if (!this.#readOnly) await topUpBurns(this.#ctx, this.#closed.signal).catch(() => {});
        this.#dropSeed();
      }).catch(reject); // closed before it ran
    });
  }

  async #catchUp(): Promise<void> {
    const errors = await syncAll(this.#ctx);
    errors.push(...(await this.#readRoots()));
    // as syncAll read them: a chain it could not read keeps those read before
    this.#tokens = this.#ctx.chains.flatMap((c) => c.chain.known);
    for (const op of this.#ctx.state.ops.filter((o) => o.status === 'pending')) {
      try {
        if (op.kind === 'send' || op.kind === 'withdraw' || op.kind === 'consolidate')
          await advanceSpend(this.#ctx, op);
        if (op.kind === 'deposit') await settleDeposit(this.#ctx, op);
        delete op.retrying;
      } catch (e) {
        // cancelled while it ran: it stays so. And a relayer relaying its request already answers the request that
        // started it, so whether a service keeps failing stays as the tries before found it.
        if (op.status !== 'pending' || e instanceof Relaying) continue;
        // what trying again may change is tried next sync, and kept on the operation, so that one that never gets past
        // it does not look merely slow
        if (!failsOperation(e)) {
          const message =
            e instanceof WalletError ? e.message : e instanceof Error ? `${e.name}: ${e.message}` : String(e);
          op.retrying = {
            message,
            code: e instanceof WalletError ? e.code : undefined,
            sinceMs: op.retrying?.sinceMs ?? Date.now(),
          };
          continue;
        }
        delete op.retrying;
        op.status = 'failed';
        op.error = e.message;
        op.errorCode = e.code;
        await this.#ctx.save();
      }
    }
    if (errors.length > 0) throw errors[0];
  }

  /** Syncs on its own: every 3 s while something is under way, every 10 s otherwise. Returns a stop function. */
  autoSync(onChange?: () => void, onError?: (e: unknown) => void): () => void {
    let stopped = false;
    let timer: ReturnType<typeof setTimeout> | undefined;
    const tick = async () => {
      try {
        await this.sync();
        onChange?.();
      } catch (e) {
        onError?.(e);
      }
      if (stopped || this.#closed.signal.aborted) return;
      const busy = this.#ctx.state.ops.some((o) => o.status === 'pending' && Date.now() - o.createdMs < WAIT_MS * 4);
      timer = setTimeout(tick, busy ? 3_000 : 10_000);
    };
    void tick();
    return () => {
      stopped = true;
      clearTimeout(timer);
    };
  }

  /** The tokens of every chain, as of opening or the last sync. */
  tokens(): Token[] {
    return this.#tokens;
  }

  #token(chainId: bigint, tokenId: number): Token {
    return (
      this.#tokens.find((t) => t.chainId === chainId && t.tokenId === tokenId) ??
      fail('invalid', `unknown token ${tokenId} on ${chainId}`)
    );
  }

  balances(): Balance[] {
    const coins = this.coins();
    // storage says which notes to look for, not that they come: a payer writes its notes there before its JoinSplit
    // leaves, and one that never lands leaves them behind. So a note counts once it is a coin (its commitment read);
    // before that, only a note this device's own operation under way is making counts, as incoming. A zero-value
    // change, there to carry its payment's receipt, never counts
    const making = new Set(
      this.#ctx.state.ops.flatMap((o) =>
        o.status === 'pending' && o.kind !== 'deposit' ? (o.data.changes ?? []) : [],
      ),
    );
    return this.#tokens.map((token) => {
      const { chainId, tokenId } = token;
      const b: Balance = { token, spendable: 0n, pending: [], blocked: 0n };
      for (const n of this.#ctx.state.notes.filter(
        (n) => n.chainId === chainId && n.tokenId === tokenId && n.value > 0n && making.has(n.salt),
      )) {
        if (!n.found.some((f) => f.confirmed && !f.unchecked)) b.pending.push({ amount: n.value, reason: 'incoming' });
      }
      for (const c of coins.filter((c) => c.token === token)) {
        if (c.state === 'spendable') b.spendable += c.amount;
        else if (c.state === 'blocked') b.blocked += c.amount;
        else if (c.state !== 'spending') b.pending.push({ amount: c.amount, reason: c.state });
      }
      return b;
    });
  }

  /** Every unspent note and deposit on chain, and where each stands, as of opening or the last sync. A note announced
   * but not read on chain yet is not one: `balances()` counts it as incoming if this device's operation is making it. */
  coins(): CoinInfo[] {
    const size = (chainId: bigint) => this.#status.get(chainId)?.latestRoot?.size ?? 0;
    const unproved = (chainId: bigint) => (this.#status.get(chainId)?.halted ? 'roots-halted' : 'awaiting-root');
    // when a root should cover a coin that landed at `atMs`
    const covered = (chainId: bigint, atMs: number | undefined) => {
      const secs = this.#status.get(chainId)?.settleSecs ?? null;
      return atMs === undefined || secs === null ? null : atMs + secs * 1000;
    };
    const date = (ms: number | null) => (ms === null ? null : new Date(ms));
    const spending = new Set(this.#ctx.state.ops.flatMap((o) => inputsOf(o).map((c) => `${o.chainId}:${c.index}`)));
    // spent by a JoinSplit or merge in a block, which waits only to be final: gone, as activity() counts it. Sync sees
    // it by its nullifier (`unspent`); this device's own is gone already from its relay on (a reorg that drops it
    // brings them back as spending, and the operation relays it again)
    const landed = new Set(this.#ctx.state.ops.flatMap((o) => minedInputsOf(o).map((c) => `${o.chainId}:${c.index}`)));
    const out: CoinInfo[] = [];
    // a zero-value change carries its payment's receipt, and is no coin
    for (const n of this.#ctx.state.notes.filter((n) => n.value > 0n)) {
      // a 4-byte tag alone matches someone else's now and then: a coin once its commitment is read. And one coin: a
      // note's hash is unique, so where a reorg moved it before its first place is final, both places hold it, and it
      // is at the final one, or else the latest
      const read = n.found.filter((f) => f.confirmed);
      const f = read.find((f) => !f.tentative) ?? read.at(-1);
      if (!f || !unspent(f)) continue;
      const id = `${n.chainId}:${f.index}`;
      if (landed.has(id)) continue;
      const state = spending.has(id) ? 'spending' : f.index >= size(n.chainId) ? unproved(n.chainId) : 'spendable';
      out.push({
        id,
        kind: 'note',
        token: this.#token(n.chainId, n.tokenId),
        amount: n.value,
        state,
        from: n.peer,
        via: null,
        readyBy: state === 'awaiting-root' ? date(covered(n.chainId, f.atMs)) : null,
        at: f.atMs === undefined ? null : new Date(f.atMs),
      });
    }
    for (const d of this.#ctx.state.deposits) {
      // a coin once its commitment is read, which names the amount
      for (const f of d.found.filter((f) => unspent(f) && f.amount !== null)) {
        const id = `${d.chainId}:${f.index}`;
        if (landed.has(id)) continue;
        const state =
          f.asp === 'rejected'
            ? 'blocked'
            : spending.has(id)
              ? 'spending'
              : f.asp === null
                ? 'screening'
                : f.index >= size(d.chainId)
                  ? unproved(d.chainId)
                  : 'spendable';
        // a root covers a deposit while it is screened, most often before its check ends
        const settles = covered(d.chainId, f.atMs);
        const readyBy =
          state === 'screening'
            ? date(f.decidedByMs === undefined ? null : Math.max(f.decidedByMs, settles ?? 0))
            : state === 'awaiting-root'
              ? date(settles)
              : null;
        out.push({
          id,
          kind: 'deposit',
          token: this.#token(d.chainId, f.tokenId),
          amount: f.amount!,
          state,
          from: f.sender,
          via: this.#via(d, f.sender),
          readyBy,
          at: f.atMs === undefined ? null : new Date(f.atMs),
        });
      }
    }
    return out;
  }

  /** Everything this wallet received, sent, deposited, sold, withdrew, merged and returned, newest first: the same on every
   * device of the wallet, read from storage and the chain. This device's operations add only what no other device can
   * know: a failed attempt, and a payment in a block whose change is not found yet. */
  activity(): Activity[] {
    const s = this.#ctx.state;
    const out: Activity[] = [];
    const ms = (t: number | bigint | null | undefined) => (t === null || t === undefined ? null : new Date(Number(t)));
    /** One on chain at `coin`, dated by its block, or else `fallbackMs`. */
    const at = (
      kind: Activity['kind'],
      chainId: bigint,
      f: { index: number; atMs?: number },
      fallbackMs: number | null,
    ) => ({
      id: `${kind}:${chainId}:${f.index}`,
      kind,
      coin: `${chainId}:${f.index}`,
      at: ms(f.atMs ?? fallbackMs),
      burnAddress: null as Address | null,
      status: 'done' as const,
    });
    // payments whose change shows them, by the change's salt
    const shown = new Set<Hex>();
    for (const n of s.notes) {
      // on chain, and its commitment read: a 4-byte tag alone matches someone else's now and then
      const f = n.found.find((f) => f.confirmed);
      if (!f) continue;
      const token = this.#token(n.chainId, n.tokenId);
      const stored = n.atNs === null ? null : Number(n.atNs / 1_000_000n);
      const r = n.receipt;
      if (n.source === 'received') {
        out.push({
          ...at('received', n.chainId, f, stored),
          token,
          amount: n.value,
          fee: null,
          counterparty: n.peer,
          via: null,
          txHash: null,
        });
      } else if (r?.kind === 'merged') {
        out.push({
          ...at('merged', n.chainId, f, stored),
          token,
          amount: n.value,
          fee: r.fee,
          counterparty: null,
          via: null,
          txHash: null,
        });
      } else if (r) {
        shown.add(n.salt);
        const kind = r.kind === 'withdrawn' || r.kind === 'unwrapped' ? 'withdrawn' : 'sent';
        const code = r.kind === 'sent-to-code' ? this.#paidCode(n.chainId, r.counterparty) : null;
        const counterparty = r.kind === 'sent-to-code' ? null : r.counterparty;
        out.push({
          ...at(kind, n.chainId, f, stored),
          token,
          amount: r.amount,
          fee: r.fee,
          counterparty,
          via: code ? { code } : null,
          txHash: null,
        });
      }
    }
    for (const d of s.deposits) {
      // on chain once found; shown once its commitment is read, which names the amount
      for (const f of d.found.filter((f) => f.amount !== null)) {
        // into a burn address a payer chose: theirs to this wallet, as a payment is
        const kind = d.managed ? 'sale' : d.payer ? 'received' : 'deposited';
        const entry = {
          ...at(kind, d.chainId, f, d.createdMs),
          token: this.#token(d.chainId, f.tokenId),
          amount: f.amount!,
          burnAddress: d.address,
        };
        out.push({ ...entry, fee: null, counterparty: f.sender, via: this.#via(d, f.sender), txHash: null });
      }
    }
    // a deposit that paid someone (`deposit({ to })`), once its transfer is found
    for (const x of s.sent) {
      for (const f of x.found.filter((f) => f.amount !== null)) {
        out.push({
          ...at('sent', x.chainId, f, x.createdMs),
          token: this.#token(x.chainId, f.tokenId),
          amount: f.amount!,
          fee: null,
          counterparty: x.to,
          via: null,
          txHash: null,
        });
      }
    }
    for (const r of s.receipts) {
      if (r.kind !== 'returned') continue;
      const entry = {
        ...at('returned', r.chainId, { index: r.index }, r.atMs),
        token: this.#token(r.chainId, r.tokenId),
        amount: r.amount,
      };
      out.push({ ...entry, fee: null, counterparty: r.recipient, via: null, txHash: r.txHash });
    }
    for (const op of s.ops) {
      const failed = op.status === 'failed';
      const base = {
        id: op.id,
        token: this.#token(op.chainId, op.tokenId),
        amount: op.amount,
        at: new Date(op.createdMs),
        coin: null,
        burnAddress: null,
        status: failed ? ('failed' as const) : ('done' as const),
      };
      if (op.kind === 'deposit') {
        // until its transfer is found, as above
        const found = s.sent.some(
          (x) =>
            x.chainId === op.chainId &&
            x.address === op.data.burnAddress.toLowerCase() &&
            x.found.some((f) => f.amount !== null),
        );
        const { to, code, txHash } = op.data;
        if ((!to && !code) || !txHash || op.status === 'pending' || found) continue;
        out.push({
          ...base,
          kind: 'sent',
          fee: null,
          counterparty: to ?? null,
          via: code ? { code } : null,
          txHash,
        });
        continue;
      }
      // under way (in operations()), or shown by its change
      if (op.kind === 'consolidate' || (!failed && !landed(op)) || shown.has(op.data.changes?.[0] ?? '0x')) continue;
      const to = op.data.to;
      out.push({
        ...base,
        kind: op.kind === 'send' ? 'sent' : 'withdrawn',
        fee: feesOf(op),
        counterparty:
          to.kind === 'public' ? to.address : to.kind === 'address' ? bytesToHex(to.recipient.address) : null,
        via: to.kind === 'code' ? { code: to.code } : null,
        txHash: op.data.txHashes?.at(-1) ?? null,
      });
    }
    return out.sort((a, b) => (b.at?.getTime() ?? 0) - (a.at?.getTime() ?? 0));
  }

  /** The deposit address `d` registered (here, or on another device, which says so in storage) if `sender` is it: what
   * a deposit from `sender` came through. */
  #via(d: DepositRecord, sender: Hex | null): { depositAddress: Address } | null {
    const registered =
      d.depositAddress ??
      this.#ctx.state.receipts.flatMap((r) =>
        r.kind === 'deposit-address' && r.chainId === d.chainId && r.burnAddress === d.address.toLowerCase()
          ? [r.depositAddress]
          : [],
      )[0];
    return registered && sender && isAddressEqual(sender, registered)
      ? { depositAddress: getAddress(registered) }
      : null;
  }

  /** The text of a receive code this wallet paid, by its burn address, from storage's record of paying it. */
  #paidCode(chainId: bigint, burnAddress: Hex): string | null {
    for (const c of this.#ctx.state.storage?.outgoing.lanes ?? []) {
      if ('code' in c.via && c.via.code.chainId === chainId && bytesToHex(c.via.code.burnAddress) === burnAddress)
        return encodeCode(c.via.code);
    }
    return null;
  }

  /** `a`'s transaction and its block's time, read now: for an app to show on asking, as a sync does not read them. A
   * coin's is the ledger's log of it, in the block the indexer names. Null while the chain does not show it. */
  async transaction(a: Activity): Promise<{ hash: Hex; at: Date | null } | null> {
    const c =
      this.#ctx.chains.find((c) => c.config.chainId === a.token.chainId) ??
      fail('invalid', `unknown chain ${a.token.chainId}`);
    let hash = a.txHash;
    let block: bigint | null = null;
    if (!hash && a.coin) {
      const tx = await commitmentTx(c.chain, c.indexer, Number(a.coin.split(':')[1]));
      if (!tx) return null;
      ({ hash, block } = tx);
    }
    if (!hash) return null;
    block ??= (await c.chain.client.getTransactionReceipt({ hash }).catch(() => null))?.blockNumber ?? null;
    if (block === null) return { hash, at: null }; // not mined, or not yet seen by this RPC
    const { timestamp } = await c.chain.client.getBlock({ blockNumber: block });
    return { hash, at: new Date(Number(timestamp) * 1000) };
  }

  /** Every deposit found, with the id `rageExit` takes. */
  deposits(): DepositInfo[] {
    return this.#ctx.state.deposits.flatMap((d) =>
      d.found.map((f) => ({
        id: `${d.chainId}:${f.index}`,
        address: d.address,
        managed: d.managed === true,
        token: this.#token(d.chainId, f.tokenId),
        amount: f.amount,
        sender: f.sender,
        state: f.spent ? 'spent' : f.asp === null ? 'screening' : f.asp,
      })),
    );
  }

  /** The deposit addresses this wallet handed out (`depositAddress`), on any of its devices, newest first: for an app to
   * show each while what is sent to it is on its way, which `activity()` shows once deposited. Each is dated, and its
   * fee told, by its receipt in storage, alike on every device. */
  depositAddresses(): DepositAddressInfo[] {
    return this.#ctx.state.receipts
      .flatMap((r) => {
        if (r.kind !== 'deposit-address') return [];
        const token = this.#token(r.chainId, r.tokenId);
        return [{ address: getAddress(r.depositAddress), token, fee: r.args?.fee ?? null, at: new Date(r.atMs) }];
      })
      .sort((a, b) => b.at.getTime() - a.at.getTime());
  }

  /** What `address` is to this wallet on `chainId`: one of its own burn addresses (`deposit`), one it paid someone
   * into (`payment`, `deposit({ to })` to an address), or neither (null), as is a receive code's that it paid. On chain
   * either is a plain transfer to an address that names no one: this tells an app listing the account's public
   * transfers which they were. Both are recorded before the transfer is sent. */
  burnAddressOf(chainId: bigint, address: Address): { kind: 'deposit' } | { kind: 'payment'; to: Address } | null {
    const s = this.#ctx.state;
    const a = address.toLowerCase();
    if (s.deposits.some((d) => d.chainId === chainId && d.address.toLowerCase() === a)) return { kind: 'deposit' };
    const paid = s.sent.find((x) => x.chainId === chainId && x.address.toLowerCase() === a);
    return paid ? { kind: 'payment', to: paid.to } : null;
  }

  /** The payments to the burn addresses this wallet's points of sale handed out. Spent ones are, normally, in a
   * merged note. */
  payments(): DepositInfo[] {
    return this.deposits().filter((d) => d.managed);
  }

  /** The key of a new point of sale (`PointOfSale.connect`): the lane where it records the payment addresses it makes
   * for this wallet, which this wallet, every other device of it and a restore read, and `payments()` shows what reaches
   * them. The point of sale can spend none of it. One key for one point of sale: two would hand out the same
   * addresses. */
  posKey(): Promise<Hex> {
    return this.#exclusive(async () => {
      this.#writable();
      const ctx = this.#ctx;
      const tokens = await tokenIds(ctx);
      let n = 0;
      // the number is the last plan's: after `Occupied`, another device took the first one
      const planned = (s: SyncState) => planPosLane(ctx.view, s, ctx.chains[0].config.chainId, (n = nextPosLane(s)));
      takeRefresh(ctx, await commit(ctx.storage, ctx.view, storageState(ctx), planned), tokens);
      await ctx.save();
      return bytesToHex(posKey(ctx.view.seed, n));
    });
  }

  /** Refunds deposit `id` to its sender without the ASP, the attester or a proved root: for a deposit the ASP
   * rejected, or when those services stop. The account's wallet sends the transactions and pays their gas, or with
   * `from` another wallet of the user's does, as `deposit({ from })` pays. One through a deposit address of this
   * wallet's (`CoinInfo.via`) goes to `to`, by default `from`'s account, else this account; any other goes back to its
   * sender, and one through a point of sale's deposit address to the refund address its payer named. */
  rageExit(id: string, opts: { from?: WalletClient; to?: Address } = {}): Promise<Hex[]> {
    const route = this.#route(opts);
    return this.#seeded(async () => {
      const [chain, index] = id.split(':');
      const record =
        this.#ctx.state.deposits.find((d) => `${d.chainId}` === chain && d.found.some((f) => `${f.index}` === index)) ??
        fail('invalid', `no deposit ${id}`);
      // an operation in flight may still land with it, and would then be taken for paid when this refund spends it
      const op = this.#ctx.state.ops.find(
        (o) => `${o.chainId}` === chain && inputsOf(o).some((c) => `${c.index}` === index),
      );
      if (op) fail('invalid', `deposit ${id} is an input of operation ${op.id}, which is in flight`);
      return rageExit(this.#ctx, record, Number(index), route);
    });
  }

  /** Sends what deposit address `address` of this wallet's holds of `asset` (NATIVE for the chain's own currency) to
   * `to`: another token sent to it, which it cannot wrap. What it can wrap is wrapped instead, as a payment to it is.
   * It deploys on its first flush, and refunds nothing before. `from` and `to` as for `rageExit`. */
  refundDepositAddress(
    address: Address,
    asset: Address,
    opts: { from?: WalletClient; to?: Address } = {},
  ): Promise<Hex> {
    if (!isAddress(asset, { strict: false }) || asset.toLowerCase() === zeroAddress)
      fail('invalid', `${asset} is not an asset's address`);
    const route = this.#route(opts);
    return this.#seeded(async () => {
      const record =
        this.#ctx.state.deposits.find((d) => !d.managed && this.#via(d, address)) ??
        fail('invalid', `${address} is not a deposit address of this wallet's`);
      return refundDepositAddress(this.#ctx, record, getAddress(address), getAddress(asset), route);
    });
  }

  /** Who sends a refund and where it goes (`rageExit`), checked before the seed is asked for. */
  #route(opts: { from?: WalletClient; to?: Address }): Route {
    const from = opts.from ?? null;
    if (from && !from.account) fail('invalid', 'the wallet client has no account');
    const to = opts.to ?? from?.account?.address ?? this.address;
    if (!isAddress(to, { strict: false }) || to.toLowerCase() === zeroAddress)
      fail('invalid', `${to} is not an address to refund to`);
    return { from, to: getAddress(to) };
  }

  operations(): Operation[] {
    return this.#ctx.state.ops.map((op) => this.#operation(op));
  }

  #operation(op: OperationRecord): Operation {
    return {
      id: op.id,
      kind: op.kind,
      chainId: op.chainId,
      get status() {
        return op.status;
      },
      get error() {
        return op.error;
      },
      get errorCode() {
        return op.errorCode;
      },
      get retrying() {
        const r = op.retrying;
        return r ? { message: r.message, code: r.code, since: new Date(r.sinceMs) } : null;
      },
      get txHashes() {
        return op.kind === 'deposit' ? (op.data.txHash ? [op.data.txHash] : []) : (op.data.txHashes ?? []);
      },
      get stage() {
        return op.kind === 'deposit' ? null : (op.data.step?.stage ?? null);
      },
      to: op.kind === 'deposit' ? (op.data.to ?? null) : null,
      get cancellable() {
        return cancellable(op);
      },
      wait: async ({ until = 'mined' } = {}) => {
        const reached = () => (until === 'mined' ? landed(op) : op.status === 'done');
        for (;;) {
          if (reached()) return;
          if (op.status === 'failed') throw new WalletError(op.errorCode ?? 'invalid', op.error ?? 'failed');
          // a sync that could not read everything has still taken the operation as far as it goes, and what holds the
          // operation itself back is its `retrying`: only a wallet that is closed ends the wait
          await this.sync().catch(() => this.#closed.signal.throwIfAborted());
          if (!reached() && op.status === 'pending') await new Promise((r) => setTimeout(r, 15_000));
        }
      },
      // at once, outside the queue: a sync under way may wait long on a service that does not answer, and a page closed
      // before a queued save would find the operation pending and relay it. That sync starts no further stage of it.
      cancel: async () => {
        if (op.errorCode === 'cancelled') return;
        if (!cancellable(op))
          fail(
            'invalid',
            op.status === 'pending'
              ? 'it has a request out to the relayer, or has paid: it finishes or fails on its own'
              : `it is ${op.status}`,
          );
        const ops = this.#ctx.state.ops;
        const at = ops.indexOf(op);
        if (at < 0) fail('invalid', 'this wallet no longer holds it');
        ops.splice(at, 1);
        Object.assign(op, { status: 'failed', errorCode: 'cancelled', error: 'cancelled' });
        try {
          await this.#ctx.save();
        } catch (e) {
          // not saved, so not cancelled: the saved state would resume it
          Object.assign(op, { status: 'pending', errorCode: undefined, error: undefined });
          ops.splice(at, 0, op);
          throw e;
        }
      },
    };
  }

  #newOp<K extends OperationKind>(
    kind: K,
    token: Token,
    amount: bigint,
    data: (OperationRecord & { kind: K })['data'],
  ): OperationRecord & { kind: K } {
    // `data` is the kind's own, which TypeScript cannot follow through a generic
    const op = {
      id: bytesToHex(crypto.getRandomValues(new Uint8Array(8))),
      kind,
      chainId: token.chainId,
      tokenId: token.tokenId,
      amount,
      createdMs: Date.now(),
      status: 'pending',
      data,
    } as OperationRecord & { kind: K };
    this.#ctx.state.ops.push(op);
    return op;
  }

  /** A fresh burn address of `token`, recorded in storage before anything is sent to it: the one recorded ahead, or
   * else a new one (about 2^16 hashes and a storage write), which `recording` is told of first. */
  async #burnAddress(token: Token, depositAddress: Address | null = null, recording: () => void = () => {}) {
    const ctx = this.#ctx;
    // taken once recorded: a search that close() stops changes nothing
    let record = unusedBurn(ctx, token.chainId, token.tokenId);
    if (!record) {
      recording();
      record = await recordBurn(ctx, token.chainId, token.tokenId, await tokenIds(ctx), {
        signal: this.#closed.signal,
      });
    }
    const next = chainState(ctx, token.chainId).burnNext;
    // recording may have read another device's later ones
    next[token.tokenId] = Math.max(next[token.tokenId] ?? 0, record.burnIndex + 1);
    record.createdMs = Date.now();
    record.depositAddress = depositAddress;
    await ctx.save();
    return record;
  }

  /** Moves `amount` of the account's public tokens into the private balance: wraps the underlying asset into a fresh
   * burn address (approving it first if needed). The deposit is spendable once the ASP has screened it. More than the
   * account holds fails at once (`insufficient-funds`), before anything is asked of the wallet.
   *
   * With `to`, an account that registered, by its address or its zERC20 ID, it pays them instead, privately: into a
   * fresh burn address of theirs, under the public key they registered, told to them in storage first as a note is
   * (`planDeposit`). They receive it as a deposit of their own, screened like any; the burn address names no one. It
   * shows in `activity()` as sent. Finding the address takes about 2^16 hashes (`burn-address`). Or `to` is a receive
   * code (`receiveCode`), paid into its burn address, which its owner already watches: storage is told nothing, so
   * only this device's `activity()` shows it as sent.
   *
   * With `wrapped`, it pays from the account's zERC20 itself, as a withdrawal pays out, rather than its underlying
   * asset: a plain transfer into the burn address, with no wrap and no approval.
   *
   * With `from`, another wallet of the user's (a browser wallet) pays instead of the account: its balance is checked,
   * it approves and wraps, and an exit refunds it there. The account pays nothing and signs nothing.
   *
   * Returns once the wrap is sent: the operation is done once it is mined, which `wait()` or the next sync finds. A
   * wallet may send another transaction in its place, a speed-up or a cancel: it is then done if that one paid the burn
   * address, and failed otherwise.
   * `onStep` hears what it waits on meanwhile, for an app to show. */
  async deposit(opts: {
    token: Token;
    amount: bigint;
    to?: string;
    wrapped?: boolean;
    from?: WalletClient;
    onStep?: (step: DepositStep) => void;
  }): Promise<Operation> {
    this.#writable();
    if (opts.amount <= 0n) fail('invalid', 'the amount must be positive');
    const payer = opts.from ? (opts.from.account ?? fail('invalid', 'the wallet client has no account')) : null;
    const to = opts.to === undefined ? null : recipientOf(opts.to, opts.token);
    const step = opts.onStep ?? (() => {});
    if (this.#busy > 0) step('queued');
    return this.#exclusive(async () => {
      const { token, amount } = opts;
      const account = payer ?? this.#ctx.account;
      const client = chainCtx(this.#ctx, token.chainId).chain.client;
      const { wrapped } = opts;
      const native = !wrapped && token.underlying.toLowerCase() === NATIVE.toLowerCase();
      // a wrap of more would revert, and an ERC20's only after the approval it asks for first
      const held = native
        ? await client.getBalance({ address: account.address })
        : await client.readContract({
            address: wrapped ? token.address : token.underlying,
            abi: erc20Abi,
            functionName: 'balanceOf',
            args: [account.address],
          });
      if (held < amount) {
        const of = wrapped ? token.symbol : `${token.symbol}'s underlying asset`;
        fail(
          'insufficient-funds',
          `${payer ? 'the wallet' : 'the account'} holds ${formatUnits(held, token.decimals)} of ${of}, less than ${formatUnits(amount, token.decimals)}`,
        );
      }
      const address = await this.#depositInto(token, amount, to, step);
      // a receive code's address holds what others paid it: a transaction the wallet sends in this one's place is told
      // apart by what reaches it on top
      const before = await client.readContract({
        address: token.address,
        abi: erc20Abi,
        functionName: 'balanceOf',
        args: [address],
      });
      const op = this.#newOp(
        'deposit',
        token,
        amount,
        to?.kind === 'code'
          ? { burnAddress: address, code: to.code, held: before }
          : to
            ? { burnAddress: address, to: to.address, held: before }
            : { burnAddress: address, held: before },
      );
      await this.#ctx.save();
      try {
        const wc = await walletOn(this.#ctx, token.chainId, opts.from ?? null);
        if (!native && !wrapped) {
          const allowance = await client.readContract({
            address: token.underlying,
            abi: erc20Abi,
            functionName: 'allowance',
            args: [account.address, token.address],
          });
          if (allowance < amount) {
            step('approve');
            const tx = await guard(wc.writeContract({ account, chain: null, ...approval(token, amount) }));
            // mined before the wrap, still holding every other call: an approval sets the allowance, so another
            // deposit's in between would overwrite this one's
            await client.waitForTransactionReceipt({ hash: tx });
            await walletSees(wc, tx);
          }
        }
        step('wrap');
        const tx = await guard(
          wrapped
            ? wc.writeContract({ account, chain: null, ...transfer(token, amount, address) })
            : wc.writeContract({ account, chain: null, ...wrap(token, amount, address), value: native ? amount : 0n }),
        );
        op.data.txHash = tx;
        // its receipt is for the next sync (settleDeposit): waiting for it here would hold every other call a block
      } catch (e) {
        // declined, or nothing sent for another reason: over. A sent one is settled by its receipt on a later sync.
        if (!op.data.txHash) {
          op.status = 'failed';
          op.error = (e as Error).message;
          if (e instanceof WalletError) op.errorCode = e.code;
        }
        await this.#ctx.save();
        throw e;
      }
      await this.#ctx.save();
      return this.#operation(op);
    });
  }

  /** The transactions that make the deposit `deposit` makes, for an app that sends them from a wallet of its own, in
   * order and before it takes another deposit's: with an ERC20 underlying asset its approval for the amount, which a
   * later one would replace, then the wrap into a fresh burn address of this wallet's, or of `to`'s as `deposit` takes
   * `to`; with `wrapped`, the zERC20's own transfer there instead. The address is recorded
   * before they are made and handed out to nothing else. The deposit shows once a sync finds it on chain: no operation
   * follows it, so one to a receive code shows as sent on no device. `onStep` hears what it waits on (`queued`,
   * `burn-address`). */
  async depositTransactions(opts: {
    token: Token;
    amount: bigint;
    to?: string;
    wrapped?: boolean;
    onStep?: (step: DepositStep) => void;
  }): Promise<{ to: Address; data: Hex; value: bigint }[]> {
    this.#writable();
    if (opts.amount <= 0n) fail('invalid', 'the amount must be positive');
    const to = opts.to === undefined ? null : recipientOf(opts.to, opts.token);
    const step = opts.onStep ?? (() => {});
    if (this.#busy > 0) step('queued');
    return this.#exclusive(async () => {
      const { token, amount } = opts;
      const address = await this.#depositInto(token, amount, to, step);
      if (opts.wrapped) {
        const call = transfer(token, amount, address);
        return [{ to: call.address, data: encodeFunctionData(call), value: 0n }];
      }
      const call = wrap(token, amount, address);
      if (token.underlying.toLowerCase() === NATIVE.toLowerCase())
        return [{ to: call.address, data: encodeFunctionData(call), value: amount }];
      const approve = approval(token, amount);
      return [
        { to: approve.address, data: encodeFunctionData(approve), value: 0n },
        { to: call.address, data: encodeFunctionData(call), value: 0n },
      ];
    });
  }

  /** Where a deposit of `amount` of `token` to `to` goes: a receive code's burn address, a fresh one of an account's
   * told to it in storage, or with no `to`, a fresh one of this wallet's. */
  async #depositInto(
    token: Token,
    amount: bigint,
    to: ReturnType<typeof recipientOf> | null,
    step: (step: DepositStep) => void,
  ): Promise<Hex> {
    if (to?.kind === 'code') return to.burnAddress;
    if (to) return this.#burnFor(token, amount, to.address, () => step('burn-address'));
    return (await this.#burnAddress(token, null, () => step('burn-address'))).address;
  }

  /** A fresh burn address of `to`'s, for a deposit of `amount` that pays them, told to them in storage: a note that only
   * shows on chain cannot be found. */
  async #burnFor(token: Token, amount: bigint, to: Address, searching: () => void): Promise<Hex> {
    const ctx = this.#ctx;
    const recipient = await lookupRecipient(ctx.storage, hexToBytes(to));
    if (!recipient) fail('recipient-not-registered', `${to} never opened a zERC20 wallet: ask for a receive code`);
    searching();
    const burn = await burnAddressFor(token.chainId, bytesToHex(recipient!.publicKey), this.#closed.signal);
    // with the address, so that every device of this wallet finds the transfer it then sends
    const value = hexToBytes(numberToHex(amount, { size: 32 }));
    const deposit = {
      chainId: token.chainId,
      tokenId: token.tokenId,
      value,
      burnSalt: hexToBytes(burn.salt),
      burnAddress: hexToBytes(burn.address),
    };
    const result = await commit(ctx.storage, ctx.view, storageState(ctx), (s) =>
      planDeposit(ctx.view, s, recipient!, deposit),
    );
    takeRefresh(ctx, result, await tokenIds(ctx));
    return burn.address;
  }

  /** An address that takes `token`'s underlying asset from anywhere (an exchange withdrawal, another wallet) and
   * deposits it privately, less `fee` (in the underlying's base units) to the deposit relayer each time: what arrives
   * must exceed it. A wallet opened with a `referrer` also pays it its `bps` of the rest. Watched for 7 days by the
   * deposit relayer. It names no account: its refunds go where a key of its own signs for (`rageExit`'s `to`,
   * `refundDepositAddress`). `depositAddresses()` lists it. `onStep` hears what it waits on (`queued`,
   * `burn-address`). */
  depositAddress(
    token: Token,
    opts: { onStep?: (step: DepositStep) => void } = {},
  ): Promise<{ address: Address; fee: bigint }> {
    const step = opts.onStep ?? (() => {});
    const ctx = this.#ctx;
    const code = (index: number) => ({ chainId: token.chainId, tokenId: token.tokenId, index });
    // the seed is asked for only past the refund signers derived ahead
    const derived = !!refundSigner(ctx, code(nextBurn(ctx, token.chainId, token.tokenId)));
    if (this.#busy > 0) step('queued');
    return this.#seeded(async () => {
      const c = chainCtx(ctx, token.chainId);
      const record = await this.#burnAddress(token, null, () => step('burn-address'));
      if (!refundSigner(ctx, code(record.burnIndex))) await this.#seed(); // calls queued before took the next ones
      const signer = refundSigner(ctx, code(record.burnIndex))!;
      const referrer = this.#referrer ?? { address: zeroAddress, bps: 0 };
      const { depositAddress, feeRecipient, fee } = await registerDeposit(
        c.chain,
        token.address,
        record.address,
        { signer },
        referrer,
      );
      record.depositAddress = depositAddress;
      // for the wallet's other devices, to show what comes through it and what it takes, and for a flush without the
      // relayer: written by the next sync
      const burnAddress = record.address.toLowerCase() as Hex;
      this.#ctx.state.receipts.push({
        kind: 'deposit-address',
        chainId: token.chainId,
        tokenId: token.tokenId,
        burnAddress,
        depositAddress,
        args: { fee, feeRecipient, refundSigner: signer, referrer: referrer.address, referralBps: referrer.bps },
        atMs: Date.now(),
        unwritten: true,
      });
      await this.#ctx.save();
      return { address: depositAddress, fee };
    }, !derived);
  }

  /** Has the deposit relayer watch deposit address `address` of this wallet's for another 7 days, at the fee it was
   * handed out with: what reached it after its 7 days is deposited then, and so is what reaches it within the next.
   * `depositAddresses()` dates it from now, on every device. */
  rewatchDepositAddress(address: Address): Promise<{ address: Address; fee: bigint }> {
    return this.#seeded(async () => {
      const receipt = this.#depositReceipt(address);
      const fee = await rewatchDeposit(chainCtx(this.#ctx, receipt.chainId).chain, getAddress(address));
      // for every device of the wallet, written by the next sync: storage dates it anew
      receipt.atMs = Date.now();
      receipt.unwritten = true;
      await this.#ctx.save();
      return { address: getAddress(address), fee };
    }, false);
  }

  /** Deposits what deposit address `address` of this wallet's holds, as the deposit relayer would, for when it does
   * not: down, or no longer watching the address. Its receipt says all the address was registered with, wherever its
   * `fee` is known (`depositAddresses()`), so no relayer is asked. `from`, another wallet of the user's, sends the
   * flush and pays its gas, and shows on chain as the depositor: never the account's own, which the address does not
   * name. What it holds must exceed the fee (`insufficient-funds`). It shows in `activity()` as any deposit through
   * the address. */
  flushDepositAddress(address: Address, opts: { from: WalletClient }): Promise<Hex> {
    if (!opts.from.account) fail('invalid', 'the wallet client has no account');
    return this.#seeded(() => flushDepositAddress(this.#ctx, this.#depositReceipt(address), opts.from), false);
  }

  /** The receipt of deposit address `address` of this wallet's. */
  #depositReceipt(address: Address): DepositAddressReceipt {
    return (
      this.#ctx.state.receipts.find(
        (r): r is DepositAddressReceipt => r.kind === 'deposit-address' && isAddressEqual(r.depositAddress, address),
      ) ?? fail('invalid', `${address} is not a deposit address of this wallet's`)
    );
  }

  /** A receive code for `token`, to hand to one payer: it pays any amount, as often as it likes, publicly by a transfer
   * of the token to the code's burn address (a deposit, like a point of sale's payment addresses), or privately by
   * `send`. It is one of this wallet's burn addresses, recorded in storage ahead of need, so handing it out writes
   * nothing; it names neither this address nor its public key. Anyone who gets the code can pay it, and see what its
   * other payers paid privately: give each payer its own. It is checksummed text (bech32m, `zerc201…`). */
  receiveCode(token: Token): Promise<string> {
    const ctx = this.#ctx;
    const code = (index: number) => ({ chainId: token.chainId, tokenId: token.tokenId, index });
    // the seed is asked for only past the codes derived ahead
    const derived = !!owner(ctx, code(nextBurn(ctx, token.chainId, token.tokenId)));
    return this.#seeded(async () => {
      const { burnIndex, address } = await this.#burnAddress(token);
      if (!owner(ctx, code(burnIndex))) await this.#seed(); // calls queued before took the next ones
      return encodeCode({
        chainId: token.chainId,
        tokenId: token.tokenId,
        burnAddress: hexToBytes(address),
        publicKey: hexToBytes(owner(ctx, code(burnIndex))!.publicKey),
        key: codeKey(ctx.view.seed, token.chainId, token.tokenId, burnIndex),
      });
    }, !derived);
  }

  /** What a send or withdrawal of `amount` would cost now, or a consolidation of what the wallet holds. A send or
   * withdrawal no single JoinSplit can pay now throws as it would (`needs-consolidation`, `funds-settling`,
   * `insufficient-funds`). A consolidation of chosen `coins` throws `funds-settling` until all of them are spendable. */
  async fees(opts: {
    kind: 'send' | 'withdraw' | 'consolidate';
    token: Token;
    amount?: bigint;
    coins?: string[];
  }): Promise<FeeQuote> {
    const { token } = opts;
    const amount = opts.amount ?? 0n;
    const c = chainCtx(this.#ctx, token.chainId);
    const relayer =
      (await relayerFees(c.chain)).fees.get(token.tokenId)?.fee ??
      fail('unavailable', 'the relayer does not relay this token');
    const size = this.#status.get(token.chainId)?.latestRoot?.size ?? 0;
    const all = coins(this.#ctx, token.chainId, token.tokenId, size);
    if (opts.kind === 'consolidate') {
      const chosen = opts.coins && this.#chosen(token, opts.coins);
      if (chosen && chosenSettling(this.#ctx, token.chainId, chosen, all)) {
        // all of them must be spendable: the last one on its way, where each is a coin with an estimate
        const ids = new Set(opts.coins);
        const picked = this.coins().filter((c) => ids.has(c.id));
        const waiting = picked.filter((c) => c.state !== 'spendable');
        throw new WalletError(
          'funds-settling',
          'a chosen note or deposit is still settling: quote again once coins() shows it spendable',
          picked.length === ids.size && waiting.every(onItsWay) ? waitsOn(waiting, total(waiting)) : null,
        );
      }
      const steps = BigInt(roundsToMerge(mergePool(all, chosen)));
      // a merge pays the relayer publicly, so the protocol takes its cut of that, grossed up as a payment's is
      const cut = steps === 0n ? 0n : (await grossed(this.#ctx, token.chainId, token.tokenId, relayer)) - relayer;
      return {
        relayer: relayer * steps,
        protocol: cut * steps,
        protocolBps: bpsOf(cut, relayer + cut),
        fee: (relayer + cut) * steps,
        steps: Number(steps),
      };
    }
    // as the payment's plan reckons it, so that `fee` is a `maxFee` it passes
    const { withdrawn, protocol } = await withdrawalOf(
      this.#ctx,
      token.chainId,
      token.tokenId,
      opts.kind === 'withdraw',
      amount,
      relayer,
    );
    const onTheWay =
      this.#ctx.state.ops.some((o) => o.status === 'pending') ||
      settling(this.#ctx, token.chainId, token.tokenId, size);
    const need = amount + relayer + protocol;
    try {
      payWith(all, need, relayer, onTheWay);
    } catch (e) {
      if (!(e instanceof WalletError) || e.code !== 'funds-settling') throw e;
      throw new WalletError(e.code, e.message, this.#waitsFor(token, need));
    }
    return { relayer, protocol, protocolBps: bpsOf(protocol, withdrawn), fee: relayer + protocol, steps: 1 };
  }

  /** Of `token`'s coins on their way, the one whose turning spendable lets a payment of `need` go, as
   * `WalletError.waitsOn` tells. None while an operation is short of a block, or a sync has yet to read its change
   * where the relayer put it, as that change is not a coin yet. */
  #waitsFor(token: Token, need: bigint): CoinInfo | null {
    const unread = (o: OperationRecord) =>
      o.kind !== 'deposit' &&
      this.#ctx.state.notes.some(
        (n) =>
          n.chainId === o.chainId &&
          n.value > 0n &&
          o.data.changes?.includes(n.salt) &&
          !n.found.some((f) => f.confirmed),
      );
    if (this.#ctx.state.ops.some((o) => o.status === 'pending' && (!landed(o) || unread(o)))) return null;
    const mine = this.coins().filter((c) => c.token.chainId === token.chainId && c.token.tokenId === token.tokenId);
    return waitsOn(mine.filter(onItsWay), need - total(mine.filter((c) => c.state === 'spendable')));
  }

  /** The most a send or withdrawal of `token` can pay: what is spendable, less the fees `fees` quotes on top of it, and
   * the merges first when one JoinSplit cannot spend it all, which `fees` then asks for (`needs-consolidation`). */
  async maxAmount(opts: { kind: 'send' | 'withdraw'; token: Token }): Promise<MaxAmount> {
    const { token } = opts;
    const c = chainCtx(this.#ctx, token.chainId);
    const relayer =
      (await relayerFees(c.chain)).fees.get(token.tokenId)?.fee ??
      fail('unavailable', 'the relayer does not relay this token');
    const size = this.#status.get(token.chainId)?.latestRoot?.size ?? 0;
    return maxPayment(
      this.#ctx,
      token.chainId,
      token.tokenId,
      opts.kind === 'withdraw',
      coins(this.#ctx, token.chainId, token.tokenId, size),
      relayer,
    );
  }

  /** What the next merge of a consolidation of everything would spend, as `coins()` ids: up to 100, the largest first,
   * for `consolidate({ coins })`. Null when nothing spendable is worth merging. */
  async nextMerge(token: Token): Promise<string[] | null> {
    const c = chainCtx(this.#ctx, token.chainId);
    const fee =
      (await relayerFees(c.chain)).fees.get(token.tokenId)?.fee ??
      fail('unavailable', 'the relayer does not relay this token');
    const size = this.#status.get(token.chainId)?.latestRoot?.size ?? 0;
    const merge = mergeRound(coins(this.#ctx, token.chainId, token.tokenId, size), fee);
    return merge && merge.map((m) => `${token.chainId}:${m.index}`);
  }

  /** Fetches what a send or withdrawal proves with, some 25 MB, once a page: an app calls it as a payment form opens,
   * so that the payment's proof does not wait for the download. Outside the queue of calls: a sync goes on meanwhile. */
  preloadProver(): Promise<void> {
    return preload(this.#ctx.network.circuits.joinsplit, this.#ctx.fetch);
  }

  /** Pays `amount` privately: to an account that has registered (any wallet that ever opened), by its address or its
   * zERC20 ID (`accountId`), or to a receive code (`receiveCode`). An account that never registered fails with
   * `recipient-not-registered`. One JoinSplit from what is spendable now, or it fails here: `needs-consolidation`,
   * `funds-settling` or `insufficient-funds`.
   * `amount` is what the recipient gets, and `maxFee` caps what it pays on top, `fees({ kind: 'send' }).fee`: the
   * relayer names its fee, so a quote the user saw is the cap. */
  async send(opts: { to: string; token: Token; amount: bigint; maxFee: bigint }): Promise<Operation> {
    const { token, amount } = opts;
    if (amount <= 0n) fail('invalid', 'the amount must be positive');
    // the JoinSplit is proved by a later sync, which holds the seed until the payment is done
    return this.#seeded(async () => {
      const r = recipientOf(opts.to, token);
      let to: Destination;
      if (r.kind === 'address') {
        const recipient = await lookupRecipient(this.#ctx.storage, hexToBytes(r.address));
        if (!recipient)
          fail('recipient-not-registered', `${opts.to.trim()} never opened a zERC20 wallet: ask for a receive code`);
        to = { kind: 'address', recipient: recipient! };
      } else to = { kind: 'code', code: r.code };
      return this.#newPayment('send', token, amount, { to, maxFee: opts.maxFee, step: null, paid: 0n });
    });
  }

  /** Merges `token`'s scattered notes and deposits into one note, without paying anyone: fewer, larger notes make
   * later payments a single JoinSplit. One Nova merge spends up to 100 of them and pays the relayer's fee once; the
   * network's merge prover proves it, seeing its witness in its enclave while it does: the openings of what it spends, but
   * no private key, so it can prove only the merge this wallet signed. More
   * take another merge, once a proved root is over the first one's note; `fees({ kind: 'consolidate' })` tells how
   * many. A lone deposit becomes a note. A payment that fails with `needs-consolidation` goes through after this.
   *
   * With `coins` (ids from `coins()`, notes and deposits), only those are merged, into one note, and nothing else is
   * touched; one still settling is waited for. `maxFee` caps the fees of every merge together,
   * `fees({ kind: 'consolidate' }).fee`. */
  consolidate(opts: { token: Token; coins?: string[]; maxFee: bigint }): Promise<Operation> {
    return this.#seeded(async () => {
      if (!this.#ctx.network.mergeProver) fail('invalid', 'this network has no merge prover');
      const to: Destination = { kind: 'self' };
      const data: SpendData = { to, maxFee: opts.maxFee, step: null, paid: 0n };
      if (opts.coins) data.chosen = this.#chosen(opts.token, opts.coins);
      const op = this.#newOp('consolidate', opts.token, 0n, data);
      await this.#ctx.save();
      return this.#operation(op);
    });
  }

  /** The commitment indices of coins `ids` of `token`, none blocked or already being spent. */
  #chosen(token: Token, ids: string[]): number[] {
    if (ids.length === 0) fail('invalid', 'choose at least one note or deposit');
    const coins = this.coins();
    return ids.map((id) => {
      const c = coins.find((x) => x.id === id) ?? fail('invalid', `no unspent note or deposit ${id}`);
      if (c.token.chainId !== token.chainId || c.token.tokenId !== token.tokenId)
        fail('invalid', `${id} is not ${token.symbol}`);
      if (c.state === 'blocked' || c.state === 'spending') fail('invalid', `${id} is ${c.state}`);
      return Number(id.split(':')[1]);
    });
  }

  /** Withdraws `amount` publicly to `to`, as zERC20 or with `unwrap` the underlying asset itself, so `to` needs no gas
   * to unwrap. One JoinSplit, as `send`, and as there `to` gets all of `amount` and `maxFee` caps what is paid on top
   * (`fees({ kind: 'withdraw' }).fee`). */
  async withdraw(opts: {
    to: Address;
    token: Token;
    amount: bigint;
    maxFee: bigint;
    unwrap?: boolean;
  }): Promise<Operation> {
    if (!isAddress(opts.to)) fail('invalid', `${String(opts.to)} is not an address`);
    if (opts.amount <= 0n) fail('invalid', 'the amount must be positive');
    return this.#seeded(async () => {
      const to: Destination = { kind: 'public', address: opts.to, unwrap: opts.unwrap };
      return this.#newPayment('withdraw', opts.token, opts.amount, { to, maxFee: opts.maxFee, step: null, paid: 0n });
    });
  }

  /** A send or withdrawal with its one JoinSplit planned now: it fails here rather than later, and its inputs are
   * taken at once, so a payment right after it cannot count on them. */
  async #newPayment(kind: 'send' | 'withdraw', token: Token, amount: bigint, data: SpendData): Promise<Operation> {
    const op = this.#newOp(kind, token, amount, data);
    try {
      data.step = (await planStep(this.#ctx, op)) as Step; // a payment's plan is a step, or a throw
    } catch (e) {
      this.#ctx.state.ops.splice(this.#ctx.state.ops.indexOf(op), 1);
      throw e;
    }
    await this.#ctx.save();
    return this.#operation(op);
  }
}

/** The approval of `amount` of `token`'s ERC20 underlying asset that a wrap of it needs first. */
const approval = (token: Token, amount: bigint) =>
  ({ address: token.underlying, abi: erc20Abi, functionName: 'approve', args: [token.address, amount] }) as const;

/** The wrap of `amount` of `token`'s underlying asset into `burnAddress`, which pays it as a deposit. */
const wrap = (token: Token, amount: bigint, burnAddress: Hex) =>
  ({ address: token.address, abi: tokenAbi, functionName: 'wrap', args: [amount, burnAddress] }) as const;

/** The transfer of `amount` of `token`'s zERC20 itself into `burnAddress`, a deposit with no wrap. */
const transfer = (token: Token, amount: bigint, burnAddress: Hex) =>
  ({ address: token.address, abi: erc20Abi, functionName: 'transfer', args: [burnAddress, amount] }) as const;

/** Whom `to` names, as `send` and `deposit` take it: an account, by its address or its zERC20 ID, or a receive code of
 * `token`'s. */
function recipientOf(
  to: string,
  token: Token,
): { kind: 'address'; address: Address } | { kind: 'code'; code: string; burnAddress: Hex } {
  const address = isAddress(to) ? to : idAccount(to);
  if (address) return { kind: 'address', address };
  const code = decodeCode(to);
  if (!code) return fail('invalid', 'not an address, a zERC20 ID or a receive code');
  if (code.chainId !== token.chainId || code.tokenId !== token.tokenId)
    fail('invalid', 'the receive code is for another token');
  return { kind: 'code', code: to.trim(), burnAddress: bytesToHex(code.burnAddress) };
}

/** Each chain of `network`, with its servers, reached as `reach` says. */
const chainsOf = (network: Network, reach: Reach): ChainCtx[] =>
  network.chains.map((config) => {
    const chain = new Chain(config, reach);
    return { config, chain, indexer: new Indexer(config.indexer, chain.fetch), asp: new Asp(config.asp, chain.fetch) };
  });

/** A wallet held open here (`lockWallet`): until `release`, or until another tab or window takes it, which aborts
 * `taken`. */
export interface Hold {
  release: () => void;
  taken: AbortSignal;
  /** Runs `f`, a read or a write of the wallet's saved state, with no other tab in one, and only while this one holds the
   * wallet: asked of the browser's lock manager, which knows of a take before this tab is told, so that a write lands
   * either before the tab that took the wallet reads the state, or not at all. */
  guard: <T>(f: () => Promise<T>) => Promise<T>;
}

/** Holds `address`'s wallet on each of `network`'s chains: two tabs with a chain in common would each overwrite the
 * other's state and spend the same notes there. It fails with `wallet-in-use` while another tab or window holds any of
 * them, unless it `take`s them from that one. A wallet over other chains only is held apart, as its notes are its own:
 * an app may open the account on each chain by itself. So is one that watches it (`view`). Neither where there are no
 * Web Locks. */
export async function lockWallet(
  address: Address,
  network: Pick<Network, 'chains'>,
  kind: 'wallet' | 'view' = 'wallet',
  take = false,
): Promise<Hold> {
  const taken = new AbortController();
  const locks = (globalThis as { navigator?: Navigator }).navigator?.locks;
  if (!locks) return { release: () => {}, taken: taken.signal, guard: (f) => f() };
  const account = `zerc20-${kind}:${address.toLowerCase()}`;
  const names = network.chains.map((c) => `${account}:${c.chainId}`);
  const lose = () => taken.abort(new WalletError('wallet-taken', 'this wallet was opened in another tab or window'));
  let release = () => {};
  const held = new Promise<void>((r) => (release = r));
  const got = await Promise.all(
    names.map(
      (name) =>
        new Promise<boolean>((resolve, reject) => {
          let mine = false;
          locks
            .request(name, take ? { steal: true } : { ifAvailable: true }, (lock) => {
              mine = lock !== null;
              resolve(mine);
              return mine ? held : undefined;
            })
            // a held lock's request rejects as another takes it
            .catch((e: unknown) => (mine ? lose() : reject(e)));
        }),
    ),
  );
  if (!got.every(Boolean)) {
    release(); // the chains it did get
    fail('wallet-in-use', 'this wallet is open in another tab or window: close it there first');
  }
  // one for the account, so that wallets of it on other chains read and write their state in turn
  const state = `${account}/state`;
  const guard = <T>(f: () => Promise<T>) =>
    locks.request(state, async () => {
      const holders = (await locks.query()).held ?? [];
      const holder = (n: string) => holders.find((l) => l.name === n)?.clientId;
      if (names.some((n) => holder(n) !== holder(state))) lose();
      taken.signal.throwIfAborted();
      return f();
    });
  return { release, taken: taken.signal, guard };
}

/** A deposit `deposit()` did not see through (a reload, a lost connection), settled by what the chain shows. Runs only
 * between tasks, so no `deposit()` is still on its way to sending it. Done once its transaction is mined, or failed if
 * that reverted or it never sent one. A wallet's speed-up or cancel puts another transaction at its nonce instead, and
 * this one is never mined: what reached the burn address since it was sent tells then. One not a receive code's is paid
 * by this deposit alone, so once it holds the amount more, the deposit is done whichever transaction paid it. Else its
 * nonce, noted while a node held it, tells: once the payer's mined transactions pass it without this one, the deposit
 * is done if the address holds the amount more than before, and failed if not. A read that fails is tried next sync. */
export async function settleDeposit(ctx: Ctx, op: DepositOperation): Promise<void> {
  const { txHash: hash, burnAddress, code, sent } = op.data;
  if (!hash) {
    op.status = 'failed';
    op.error = 'the deposit was never sent';
    await ctx.save();
    return;
  }
  const c = chainCtx(ctx, op.chainId);
  const client = c.chain.client;
  const settled = async () => {
    const receipt = await client.getTransactionReceipt({ hash }).catch(() => null);
    if (!receipt) return false;
    op.status = receipt.status === 'success' ? 'done' : 'failed';
    if (op.status === 'failed') op.error = 'the deposit transaction reverted';
    return true;
  };
  if (await settled()) return ctx.save();
  const waiting = await client.getTransaction({ hash }).catch(() => null);
  if (waiting) {
    if (sent) return;
    op.data.sent = { from: waiting.from, nonce: waiting.nonce };
    return ctx.save();
  }
  try {
    const block = await client.getBlockNumber();
    const token = (await c.chain.tokens()).find((t) => t.tokenId === op.tokenId)!;
    const holds = await client.readContract({
      address: token.address,
      abi: erc20Abi,
      functionName: 'balanceOf',
      args: [burnAddress],
      blockNumber: block,
    });
    const arrived = holds - (op.data.held ?? 0n) >= op.amount;
    const taken = !!sent && (await client.getTransactionCount({ address: sent.from, blockNumber: block })) > sent.nonce;
    if (arrived && (taken || !code)) op.status = 'done';
    else if (!taken) return;
    // mined since the first look, its receipt tells
    else if (!(await settled())) {
      op.status = 'failed';
      op.error = 'the wallet sent another transaction in its place, which paid nothing into the burn address';
    }
  } catch {
    return;
  }
  await ctx.save();
}

/** A fresh state: a new wallet looks only at what comes next, a restored one from its birthday on. */
async function start(ctx: Ctx, birthday: bigint | Date | undefined): Promise<void> {
  for (const c of ctx.chains) {
    const s = chainState(ctx, c.config.chainId);
    const status = await c.indexer.status();
    let floor = { commitments: status.commitmentsFinal, nullifiers: status.nullifiersFinal };
    if (birthday !== undefined) floor = await floorAt(c, birthday);
    s.samples.push({ atMs: 0, ...floor });
  }
  await ctx.save();
}

/** The counts before `birthday` (a block, or a date found by bisecting block times), from the indexer's marks. */
async function floorAt(
  c: { chain: Chain; indexer: Indexer },
  birthday: bigint | Date,
): Promise<{ commitments: number; nullifiers: number }> {
  let block = typeof birthday === 'bigint' ? birthday : 0n;
  if (birthday instanceof Date) {
    let [lo, hi] = [0n, await c.chain.client.getBlockNumber()];
    const target = BigInt(Math.floor(birthday.getTime() / 1000));
    while (lo < hi) {
      const mid = (lo + hi + 1n) / 2n;
      if ((await c.chain.client.getBlock({ blockNumber: mid })).timestamp <= target) lo = mid;
      else hi = mid - 1n;
    }
    block = lo;
  }
  // the last page of commitments that began before the birthday
  let floor = { commitments: 0, nullifiers: 0 };
  for (let p = 0; ; p++) {
    const marks = await c.indexer.page('marks', p);
    for (let k = 0; k < marks.length / 16; k++) {
      const view = new DataView(marks.buffer, marks.byteOffset + k * 16, 16);
      if (view.getBigUint64(0, false) > block) return floor;
      floor = { commitments: (p * PAGE + k) * PAGE, nullifiers: Number(view.getBigUint64(8, false)) };
    }
    if (marks.length < PAGE * 16) return floor;
  }
}
