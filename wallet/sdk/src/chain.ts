// What a wallet reads from the chain itself, through its own RPC: roots are taken from here, never from a server.

import {
  type Address,
  type Hex,
  type PublicClient,
  type Transport,
  HttpRequestError,
  createPublicClient,
  custom,
  decodeAbiParameters,
  encodeAbiParameters,
  http,
  keccak256,
  numberToHex,
  parseAbi,
  parseAbiParameters,
  shouldThrow,
  size,
  slice,
  toHex,
  zeroAddress,
} from 'viem';
import type { ChainConfig } from './network.js';

export const verifierAbi = parseAbi([
  'function ledger() view returns (address)',
  'function factory() view returns (address)',
  'function latestAspRoot() view returns (uint256)',
  'function withdrawFee(uint32 tokenId, uint256 amount) view returns (uint256)',
  'struct Groth16Proof { uint256[2] pA; uint256[2][2] pB; uint256[2] pC; }',
  'struct TransactSignals { uint256 tokenId; uint256 chainId; uint256 commitmentRoot; uint256 aspRoot; uint256 nullifier0; uint256 nullifier1; uint256 withdrawRecipient; uint256 withdrawAmount; uint256 withdrawIntent; uint256 noteHash1; uint256 noteHash2; }',
  'struct RageExitRequest { uint64 checkpointIndex; uint256 prevHashChain; uint256[4][] commitments; uint256 nullifier; Groth16Proof proof; }',
  'function rageExit(RageExitRequest request)',
]);

export const ledgerAbi = parseAbi([
  'function provedRoots(uint64 index, uint256 root) view returns (bool)',
  'function bound() view returns (uint64)',
  'function hashChainAt(uint64 index) view returns (uint256, bool)',
  'function reserveHashChain() returns (uint64 index, uint256 checkpoint)',
  'function verifySegment(uint64 end, uint256 prev, uint256[4][] commits) view returns (uint64 start)',
  'function checkpointBefore(uint64 end, uint256 prev, uint256[4][] commits) returns (uint64 start)',
]);

export const factoryAbi = parseAbi([
  'function tokenCount() view returns (uint32)',
  'function tokenById(uint32 tokenId) view returns (address)',
]);

export const tokenAbi = parseAbi([
  'function symbol() view returns (string)',
  'function decimals() view returns (uint8)',
  'function underlyingAsset() view returns (address)',
  'function wrap(uint256 amount, address receiver) payable',
]);

export const erc20Abi = parseAbi([
  'function balanceOf(address owner) view returns (uint256)',
  'function allowance(address owner, address spender) view returns (uint256)',
  'function approve(address spender, uint256 amount) returns (bool)',
  'function transfer(address to, uint256 amount) returns (bool)',
]);

export const depositFactoryAbi = parseAbi([
  'function predict(address token, address burnAddress, address refundAddress, address refundSigner, address feeRecipient, uint256 fee, address referrer, uint16 referralBps) view returns (address)',
  'function flush(address token, address burnAddress, address refundAddress, address refundSigner, address feeRecipient, uint256 fee, address referrer, uint16 referralBps) returns (address)',
]);

/** Where a deposit address sends back what it cannot wrap, and a rage exit's refund: a fixed address, which anyone may
 * refund to, or wherever the key at `signer` signs for each refund (`DepositAddress.refundTo`). */
export type Refund = { address: Address } | { signer: Address };

const refundArgs = (refund: Refund): [Address, Address] =>
  'address' in refund ? [refund.address, zeroAddress] : [zeroAddress, refund.signer];

/** What the factory derives a deposit address from, in the order its `predict` and `flush` take it. */
export type FactoryArgs = readonly [Address, Hex, Address, Address, Address, bigint, Address, number];

/** `FactoryArgs` for a deposit address of `token` into `burnAddress` whose refunds go as `refund` says, and whose flush
 * pays `fee` to `feeRecipient` and `referralBps` of the rest to `referrer`. */
export const factoryArgs = (
  token: Address,
  burnAddress: Hex,
  refund: Refund,
  feeRecipient: Address,
  fee: bigint,
  referrer: Address,
  referralBps: number,
): FactoryArgs => [token, burnAddress, ...refundArgs(refund), feeRecipient, fee, referrer, referralBps];

/** The factory's `MAX_REFERRAL_BPS`: the most of a deposit, after the relayer's fee, that a referrer can take. */
export const MAX_REFERRAL_BPS = 300;

/** An app that hands out deposit addresses and takes `bps` of each payment to them, of what is left after the relayer's
 * fee. `address` is paid, and also names the app on chain. */
export interface Referrer {
  address: Address;
  bps: number;
}

export const depositAddressAbi = parseAbi([
  'function refund(address asset)',
  'function refundTo(address asset, address to, uint256 deadline, bytes signature)',
]);

/** What a deposit address's refund signer signs to send its balance of `asset` to `to` until `deadline` (Unix seconds),
 * as an EIP-191 message: the chain and the address are in it, so it moves nothing at the same address elsewhere. */
export const refundDigest = (chainId: bigint, depositAddress: Address, asset: Address, to: Address, deadline: bigint) =>
  keccak256(
    encodeAbiParameters(parseAbiParameters('uint256, address, address, address, uint256'), [
      chainId,
      depositAddress,
      asset,
      to,
      deadline,
    ]),
  );

/** Multicall3, at the address it has on every chain the deposit relayer serves: it puts calls in one transaction. */
export const MULTICALL3: Address = '0xcA11bde05977b3631167028862bE2a173976CA11';

/** The native asset's stand-in for `underlyingAsset`. */
export const NATIVE: Address = '0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE';

/** `Protocol.UNWRAP_INTENT`: the `withdrawIntent` that pays a withdrawal out as the underlying asset. The EIP-712 struct
 * hash of `Unwrap()`, reduced into the BN254 field. */
export const UNWRAP_INTENT =
  BigInt(keccak256(keccak256(toHex('Unwrap()')))) %
  21888242871839275222246405745257275088548364400416034343698204186575808495617n;

/** A zERC20 token on one chain. Amounts are in its base units, the same as its underlying asset's. */
export interface Token {
  chainId: bigint;
  tokenId: number;
  /** The zERC20 token: what a public withdrawal pays out (unless it unwraps), and what `unwrap` turns back into
   * `underlying`. */
  address: Address;
  underlying: Address;
  symbol: string;
  decimals: number;
}

/** When each RPC, by its URL, last answered a call from here and last failed one without answering: kept for every
 * transport to it, so that what one finds, the others do not pay for again. */
const answeredAt = new Map<string, number>();
const failedAt = new Map<string, number>();

/** How long an RPC that failed a call without answering is tried after the others. */
const RESTING_MS = 5 * 60_000;

/** The indices of `urls` in the order a call tries them: the list's own, except that RPCs resting go after the others,
 * the one that answered last first among them. */
function order(urls: readonly string[], now: number): number[] {
  const resting = urls.map((url) => now - (failedAt.get(url) ?? -Infinity) < RESTING_MS);
  const answered = (i: number) => answeredAt.get(urls[i]) ?? 0;
  return urls
    .map((_, i) => i)
    .sort((i, j) => {
      if (resting[i] !== resting[j]) return resting[i] ? 1 : -1;
      return resting[i] ? answered(j) - answered(i) : i - j;
    });
}

/** Whether viem tries a call again after failure `e`, by its own rule: when no HTTP status came, or one that may pass. */
const passes = (e: unknown) =>
  !(e instanceof HttpRequestError && e.status) || [403, 408, 413, 429].includes(e.status) || e.status >= 500;

/** A transport to a chain's RPCs, `urls` in order of preference: a call one fails, or cannot be sent to, goes on to the
 * next, so one that a resolver, a firewall or an outage keeps from a device stops nothing. An RPC that fails a call
 * without answering rests for five minutes, tried after the others, and then takes its place in the list again (a bot's
 * paid RPC, which it lists first): Tenderly's gateways refuse Tor's exits, and a browser can hold other calls behind
 * such a refused CORS preflight until they time out, 10 s later, so that wait comes once in five minutes, not at every
 * call. When every RPC fails, what a node answered (as a balance too low for the gas) is what the call fails with, over
 * what kept another from answering. A public RPC also turns calls away beyond some per second (Tenderly's gateways,
 * about five `eth_call`s), which a sync and a deposit together pass: a call every one turned away is tried again, five
 * times, the first after 0.15 s and each after twice the last, 4.65 s in all, since viem's default three give up within
 * the second the limit counts. A filter's later calls are not kept to the RPC that made it, as viem's own fallback keeps
 * them: nothing here watches through filters. */
export function rpcTransport(urls: readonly string[]): Transport {
  const rpcs = urls.map((url) => http(url, { retryCount: 0 }));
  return (params) => {
    const made = rpcs.map((rpc) => rpc(params));
    const request = async (args: { method: string; params?: unknown }): Promise<unknown> => {
      let answer: unknown;
      const failures: unknown[] = [];
      for (const i of order(urls, Date.now())) {
        try {
          const result = await made[i].request(args);
          answeredAt.set(urls[i], Date.now());
          return result;
        } catch (e) {
          // a revert or a user's refusal is the call's own answer, which another RPC gives as well
          if (shouldThrow(e as Error)) throw e;
          // a JSON-RPC error is the node's answer; anything else kept it from answering
          if (typeof (e as { code?: unknown }).code === 'number') {
            answeredAt.set(urls[i], Date.now());
            answer ??= e;
          } else {
            failedAt.set(urls[i], Date.now());
            failures.push(e);
          }
        }
      }
      throw answer ?? failures.find(passes) ?? failures[0];
    };
    return custom({ request }, { key: 'rpcs', name: 'RPCs', retryCount: 5 })(params);
  };
}

/** `read`, made once and then kept. A read that fails is not kept: the next call reads again, rather than failing for
 * as long as the wallet is open. */
function once<T>(read: () => Promise<T>): () => Promise<T> {
  let kept: Promise<T> | undefined;
  return () =>
    (kept ??= read().catch((e: unknown) => {
      kept = undefined;
      throw e;
    }));
}

/** The platform's `fetch`, looked up at each call. */
export const platformFetch: typeof fetch = (input, init) => fetch(input, init);

/** How an app has the wallet reach the chains and the servers: through a node the user picked, a proxy or Tor. */
export interface Reach {
  /** The transport to a chain's RPCs; `rpcTransport(chain.rpcUrls)` if absent. */
  transport?: (chain: ChainConfig) => Transport;
  /** What asks every server (the indexers, the ASPs, the attesters, the relayers, the merge prover, the storage canister)
   * and fetches the circuits; the platform's `fetch` if absent. */
  fetch?: typeof fetch;
}

/** What asks the servers for an app that reaches them as `reach` says: its fetch, always called as a plain function (a
 * platform's fetch called as an object's method throws), or the platform's. */
export function fetchOf(reach: Reach): typeof fetch {
  const f = reach.fetch;
  return f ? (input, init) => f(input, init) : platformFetch;
}

export class Chain {
  readonly client: PublicClient;
  /** What reaches this chain's RPCs: its reads, and the account's own transactions. */
  readonly transport: Transport;
  /** What asks the servers beside this chain. */
  readonly fetch: typeof fetch;
  #tokens: Token[] = [];

  constructor(
    readonly config: ChainConfig,
    reach: Reach = {},
  ) {
    this.transport = reach.transport?.(config) ?? rpcTransport(config.rpcUrls);
    this.fetch = fetchOf(reach);
    this.client = createPublicClient({ transport: this.transport });
  }

  get chainId(): bigint {
    return this.config.chainId;
  }

  // the verifier's ledger and token factory are set once, as it is initialized
  readonly ledger = once(() =>
    this.client.readContract({ address: this.config.verifier, abi: verifierAbi, functionName: 'ledger' }),
  );
  readonly #factory = once(() =>
    this.client.readContract({ address: this.config.verifier, abi: verifierAbi, functionName: 'factory' }),
  );

  /** The deposit address the factory deploys for `args`. */
  predictDepositAddress(args: FactoryArgs): Promise<Address> {
    return this.client.readContract({
      address: this.config.depositAddressFactory,
      abi: depositFactoryAbi,
      functionName: 'predict',
      args,
    });
  }

  /** Where `address` refunds to if it is a deployed deposit address for `token` and `burnAddress`, whatever its refund,
   * fee and referral; null if it is not one. A clone's code ends with its immutable args,
   * `abi.encode(token, burnAddress, refundAddress, refundSigner, feeRecipient, fee, referrer, referralBps)`; the
   * factory's address for them confirms it, so code made to look like one does not pass. */
  async depositAddressRefund(address: Address, token: Address, burnAddress: Hex): Promise<Refund | null> {
    const code = await this.client.getCode({ address });
    if (!code || size(code) < 256) return null;
    // the uint16 read as a whole word, so code made to look like a clone cannot make the decoding throw
    const [refundAddress, refundSigner, feeRecipient, fee, referrer, referralBps] = decodeAbiParameters(
      parseAbiParameters('address, address, address, uint256, address, uint256'),
      slice(code, size(code) - 192),
    );
    // predict would revert
    if ((refundAddress === zeroAddress) === (refundSigner === zeroAddress) || feeRecipient === zeroAddress) return null;
    if (referralBps > MAX_REFERRAL_BPS || (referrer === zeroAddress && referralBps !== 0n)) return null;
    const refund: Refund = refundAddress === zeroAddress ? { signer: refundSigner } : { address: refundAddress };
    const expected = await this.predictDepositAddress(
      factoryArgs(token, burnAddress, refund, feeRecipient, fee, referrer, Number(referralBps)),
    );
    return expected.toLowerCase() === address.toLowerCase() ? refund : null;
  }

  /** Whether the ledger accepts `root` as the tree at `size` leaves. */
  async provedRoot(size: number, root: Hex): Promise<boolean> {
    return this.client.readContract({
      address: await this.ledger(),
      abi: ledgerAbi,
      functionName: 'provedRoots',
      args: [BigInt(size), BigInt(root)],
    });
  }

  /** `2^64 - 1`, unless the ledger is in an emergency: then it accepts no root above it, and proves none. */
  async bound(): Promise<bigint> {
    return this.client.readContract({ address: await this.ledger(), abi: ledgerAbi, functionName: 'bound' });
  }

  async latestAspRoot(): Promise<Hex> {
    const root = await this.client.readContract({
      address: this.config.verifier,
      abi: verifierAbi,
      functionName: 'latestAspRoot',
    });
    return numberToHex(root, { size: 32 });
  }

  withdrawFee(tokenId: number, amount: bigint): Promise<bigint> {
    return this.client.readContract({
      address: this.config.verifier,
      abi: verifierAbi,
      functionName: 'withdrawFee',
      args: [tokenId, amount],
    });
  }

  /** Every token the factory has registered, read once and then only the new ones. While the first read fails,
   * `saved` stands for it: what a wallet read of this chain before, so that a chain whose RPCs do not answer keeps no
   * saved wallet from opening. A read that answers is what counts: it tells the tokens as the chain has them now. */
  async tokens(saved?: Token[]): Promise<Token[]> {
    try {
      return await this.#readTokens();
    } catch (e) {
      if (this.#tokens.length > 0 || !saved) throw e;
      return (this.#tokens = saved);
    }
  }

  async #readTokens(): Promise<Token[]> {
    const factory = await this.#factory();
    const count = await this.client.readContract({ address: factory, abi: factoryAbi, functionName: 'tokenCount' });
    const known = this.#tokens;
    const fresh = await Promise.all(
      Array.from({ length: count - known.length }, async (_, i) => {
        const tokenId = known.length + i + 1;
        const address = await this.client.readContract({
          address: factory,
          abi: factoryAbi,
          functionName: 'tokenById',
          args: [tokenId],
        });
        const read = <F extends 'symbol' | 'decimals' | 'underlyingAsset'>(functionName: F) =>
          this.client.readContract({ address, abi: tokenAbi, functionName });
        const [symbol, decimals, underlying] = await Promise.all([
          read('symbol'),
          read('decimals'),
          read('underlyingAsset'),
        ]);
        return { chainId: this.chainId, tokenId, address, underlying, symbol, decimals };
      }),
    );
    this.#tokens = [...known, ...fresh];
    return this.#tokens;
  }

  /** The tokens as `tokens()` last read them, without reading again. */
  get known(): Token[] {
    return this.#tokens;
  }
}
