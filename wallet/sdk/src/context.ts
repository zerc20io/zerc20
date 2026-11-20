// Everything an open wallet works with, shared by sync and the operations.

import type { CanisterClient, ViewKey } from '@zerc20/storage-sdk';
import {
  type Account,
  type Address,
  type Hex,
  type LocalAccount,
  type PublicClient,
  type WalletClient,
  type WriteContractParameters,
  createWalletClient,
  publicActions,
} from 'viem';
import { privateKeyToAccount } from 'viem/accounts';
import type { Chain } from './chain.js';
import { core } from './core.js';
import { guard } from './errors.js';
import type { ChainConfig, Network } from './network.js';
import { refundKey } from './seed.js';
import type { Asp, Indexer } from './servers.js';
import type { ChainState, WalletState } from './state.js';

export interface ChainCtx {
  config: ChainConfig;
  chain: Chain;
  indexer: Indexer;
  asp: Asp;
}

export interface SpendKey {
  /** The circuits' `private_key`: only this wallet's own proofs take it. */
  secret: Hex;
  /** The hash of the key that signs this key's spends, which the circuits take with `secret`. */
  authKeyHash: Hex;
  publicKey: Hex;
  nullifyingKey: Hex;
}

/** What a sync needs of a key: its public key and nullifying key, which find and follow what it owns but spend none of
 * it, and the signing key's hash, which with the nullifying key makes the public key. */
export type Owner = Pick<SpendKey, 'authKeyHash' | 'publicKey' | 'nullifyingKey'>;

export interface Ctx {
  network: Network;
  /** The root of every key. Opened with a function for it, held only while something needs it; watching, never;
   * otherwise always. */
  seed: Uint8Array | null;
  /** The owners derived while the seed was held, or given by a view key, by key: the wallet's own (`''`) and each
   * receive code's. */
  owners: Map<string, Owner>;
  /** The refund signers' addresses derived while the seed was held, by receive code (`refundSigner`). */
  refundSigners: Map<string, Address>;
  address: Hex;
  /** The account that holds the public funds, and signs for them. */
  account: Account;
  /** The user's wallet, when it is what signs and sends rather than an account of the app's own (`walletOn`). */
  walletClient: WalletClient | null;
  storage: CanisterClient;
  view: ViewKey;
  chains: ChainCtx[];
  /** What asks the servers and fetches the circuits: the app's (`Reach`), or the platform's. */
  fetch: typeof fetch;
  state: WalletState;
  save(): Promise<void>;
  /** When storage was last read in full rather than through its log (in memory: the first sync does it). */
  lastFullRefreshMs: number;
}

const keys = new WeakMap<Uint8Array, Map<string, SpendKey>>();

/** A receive code of this seed's: its chain, token and index (the burn index the code shares). */
export interface CodeId {
  chainId: bigint;
  tokenId: number;
  index: number;
}

const idOf = (code?: CodeId) => (code ? `${code.chainId}:${code.tokenId}:${code.index}` : '');

/** The seed, which the wallet holds whenever it does what needs it. */
export function seedOf(ctx: Ctx): Uint8Array {
  if (!ctx.seed) throw new Error('the wallet does not hold its seed now');
  return ctx.seed;
}

/** The key that owns this seed's notes and deposits on every chain and token, or with `code`, the notes paid to that
 * receive code. Its owner is kept for when the seed is not held. */
export function spendKey(ctx: Ctx, code?: CodeId): SpendKey {
  const seed = seedOf(ctx);
  let bySeed = keys.get(seed);
  if (!bySeed) keys.set(seed, (bySeed = new Map<string, SpendKey>()));
  const id = idOf(code);
  let key = bySeed.get(id);
  if (!key) {
    key = (code ? core.codeSpendKey(seed, code.chainId, code.tokenId, code.index) : core.spendKey(seed)) as SpendKey;
    bySeed.set(id, key);
  }
  const { authKeyHash, publicKey, nullifyingKey } = key;
  if (!ctx.owners.has(id)) ctx.owners.set(id, { authKeyHash, publicKey, nullifyingKey });
  return key;
}

/** `spendKey`'s owner: derived before, or now if the seed is held; null if neither. The wallet's own is derived as it
 * opens. */
export function owner(ctx: Ctx, code?: CodeId): Owner | null {
  return ctx.owners.get(idOf(code)) ?? (ctx.seed ? spendKey(ctx, code) : null);
}

/** The key that signs where the refunds of the deposit address handed out with `code`'s burn address go. */
export function refundAccount(ctx: Ctx, code: CodeId): LocalAccount {
  const account = privateKeyToAccount(refundKey(seedOf(ctx), code.chainId, code.tokenId, code.index));
  ctx.refundSigners.set(idOf(code), account.address);
  return account;
}

/** `refundAccount`'s address: derived before, or now if the seed is held; null if neither. */
export function refundSigner(ctx: Ctx, code: CodeId): Address | null {
  return ctx.refundSigners.get(idOf(code)) ?? (ctx.seed ? refundAccount(ctx, code).address : null);
}

export function chainCtx(ctx: Ctx, chainId: bigint): ChainCtx {
  const c = ctx.chains.find((c) => c.config.chainId === chainId);
  if (!c) throw new Error(`chain ${chainId} is not in this network`);
  return c;
}

export function chainState(ctx: Ctx, chainId: bigint): ChainState {
  let s = ctx.state.chains.find((c) => c.chainId === chainId);
  if (!s) ctx.state.chains.push((s = { chainId, samples: [], burnNext: {} }));
  return s;
}

/** `wc` on `chainId`, switched there first: a browser wallet is on one chain at a time. */
async function switched(wc: WalletClient, chainId: bigint): Promise<WalletClient> {
  if ((await wc.getChainId()) !== Number(chainId)) await guard(wc.switchChain({ id: Number(chainId) }));
  return wc;
}

/** The gas limit a transaction estimated at `gas` goes with: a quarter more. Its cost moves with the state it lands on,
 * as a balance another transaction empties first takes a fresh storage slot to fill again (17,100 gas more), and gas
 * left over is not paid for. */
export const headroom = (gas: bigint): bigint => gas + gas / 4n;

/** `wc`, its contract calls sent with `headroom` over their estimate on the chain's own RPC (`client`) rather than at
 * the estimate itself, which is what viem gives a local account. */
export function roomy(wc: WalletClient, client: PublicClient): WalletClient {
  const writeContract = (async (args: WriteContractParameters) => {
    const { address, abi, functionName, args: inputs, value, account = wc.account } = args;
    const call = { address, abi, functionName, args: inputs, value, account } as Parameters<
      PublicClient['estimateContractGas']
    >[0];
    return wc.writeContract({ ...args, gas: args.gas ?? headroom(await client.estimateContractGas(call)) });
  }) as WalletClient['writeContract'];
  return wc.extend(() => ({ writeContract }));
}

/** The client that sends the account's transactions on `chainId`: `from` (another wallet of the user's) or else the
 * user's wallet, switched to the chain, or the app's own account, through the chain's RPC. */
export async function walletOn(ctx: Ctx, chainId: bigint, from: WalletClient | null = null): Promise<WalletClient> {
  const c = chainCtx(ctx, chainId);
  const wallet = from ?? ctx.walletClient;
  const wc = wallet
    ? await switched(wallet, chainId)
    : createWalletClient({ account: ctx.account, transport: c.chain.transport });
  return roomy(wc, c.chain.client);
}

/** Waits until the wallet's own node has a transaction mined on ours too: the wallet simulates the next one there, and
 * where blocks are fast that node lags ours now and then, so the next one would show as reverting. A wallet that does
 * not answer is not waited on. */
export async function walletSees(wc: WalletClient, hash: Hex): Promise<void> {
  await wc
    .extend(publicActions)
    .waitForTransactionReceipt({ hash, pollingInterval: 1_000, timeout: 30_000 })
    .catch(() => {});
}
