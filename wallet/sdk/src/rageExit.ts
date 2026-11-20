// Rage exit: a burn deposit refunded to its sender with nothing but the chain and the indexer's public pages, for
// when the ASP, the attester or root proving stop. The ledger authenticates the deposit itself, by re-hashing the
// commitments from it up to a checkpoint; a long way is walked back one transaction of commitments at a time. A deposit
// address's refunds, the rage exit's and any other, go where its refund signer, a key of this wallet's, signs for; and
// what reaches one is deposited without the deposit relayer by a flush of its own.

import {
  type Address,
  type Hex,
  type WalletClient,
  decodeEventLog,
  encodeFunctionData,
  isAddressEqual,
  multicall3Abi,
  numberToHex,
  parseAbi,
} from 'viem';
import {
  MULTICALL3,
  NATIVE,
  depositAddressAbi,
  depositFactoryAbi,
  erc20Abi,
  factoryArgs,
  ledgerAbi,
  refundDigest,
  verifierAbi,
} from './chain.js';
import { type ChainCtx, type Ctx, chainCtx, refundAccount, spendKey, walletOn, walletSees } from './context.js';
import { core } from './core.js';
import { fail, guard } from './errors.js';
import { prove } from './prove.js';
import { PAGE } from './servers.js';
import type { DepositAddressReceipt, DepositRecord } from './state.js';

/** Commitments per transaction: about a thousand fit in the 128 KB transaction size limit. */
const SEGMENT = 900;

const checkpointEvent = parseAbi(['event CheckpointRecorded(uint64 indexed index, uint256 hashChain)']);

type Fields = [bigint, bigint, bigint, bigint];

/** Commitments `[from, to)`, each with the hash chain before it, from the indexer's pages. */
async function commitments(c: ChainCtx, from: number, to: number): Promise<{ list: Fields[]; before: Hex[] }> {
  const list: Fields[] = [];
  const before: Hex[] = [];
  for (let p = Math.floor(from / PAGE); p * PAGE < to; p++) {
    const { hashChainBefore, entries } = await c.indexer.commitments(p);
    let chain = hashChainBefore;
    for (let j = 0; j < entries.length / 128; j++) {
      const i = p * PAGE + j;
      if (i >= to) break;
      const fields = [0, 1, 2, 3].map((f) =>
        BigInt(`0x${hexOf(entries.subarray(j * 128 + 32 * f, j * 128 + 32 * (f + 1)))}`),
      ) as Fields;
      if (i >= from) {
        list.push(fields);
        before.push(chain);
      }
      chain = core.hashChain(
        chain,
        fields.map((x) => numberToHex(x, { size: 32 })),
      ) as Hex;
    }
  }
  if (list.length !== to - from)
    return fail('unavailable', `the indexer does not serve commitments ${from}..${to} yet`);
  return { list, before };
}

const hexOf = (b: Uint8Array) => Array.from(b, (x) => x.toString(16).padStart(2, '0')).join('');

/** The `checkpointBefore` calls that walk back from the checkpoint at `end` to one at most a segment after `index`,
 * the nearest the checkpoint first, and the checkpoint they end at. Each records the hash chain before its segment as
 * the checkpoint the next one ends at. `list[k]` is the commitment at `index + k` and `before[k]` the chain before it. */
export function walkBack(index: number, end: number, list: Fields[], before: Hex[]) {
  const calls: [bigint, bigint, Fields[]][] = [];
  for (; end - index > SEGMENT; end -= SEGMENT) {
    const start = end - SEGMENT - index;
    calls.push([BigInt(end), BigInt(before[start]), list.slice(start, end - index)]);
  }
  return { calls, end };
}

/** The first index after `index` the ledger has a checkpoint at: a proved root's size, else a fresh reservation. */
async function checkpointAfter(ctx: Ctx, c: ChainCtx, index: number, send: Sender): Promise<number> {
  const ledger = await c.chain.ledger();
  for (let p = 0; ; p++) {
    const roots = await c.indexer.roots(p);
    const after = roots.find((r) => r.size > index);
    if (after) {
      const [, exists] = await c.chain.client.readContract({
        address: ledger,
        abi: ledgerAbi,
        functionName: 'hashChainAt',
        args: [BigInt(after.size)],
      });
      if (exists) return after.size;
    }
    if (roots.length < PAGE) break;
  }
  const receipt = await send({ address: ledger, abi: ledgerAbi, functionName: 'reserveHashChain', args: [] });
  for (const log of receipt.logs) {
    try {
      const ev = decodeEventLog({ abi: checkpointEvent, data: log.data, topics: log.topics });
      return Number(ev.args.index);
    } catch {}
  }
  return fail('unavailable', 'reserveHashChain recorded no checkpoint');
}

interface Call {
  address: Address;
  abi: readonly unknown[];
  functionName: string;
  args: readonly unknown[];
}

type Sender = (call: Call) => Promise<{ logs: { data: Hex; topics: [Hex, ...Hex[]] }[]; status: string }>;

/** Who sends a refund's transactions and pays their gas (null: the account's own wallet), and where a refund from one
 * of this wallet's deposit addresses goes. */
export interface Route {
  from: WalletClient | null;
  to: Address;
}

/** Sends from `from`, or from the account's own wallet, and waits for each transaction to land; `hashes` collects them. */
async function sender(ctx: Ctx, c: ChainCtx, from: WalletClient | null, hashes: Hex[]) {
  const wc = await walletOn(ctx, c.config.chainId, from);
  const account = from?.account ?? ctx.account;
  const send: Sender = async ({ address, abi, functionName, args }) => {
    const hash = await guard(
      wc.writeContract({ account, chain: null, address, abi: abi as never, functionName, args }),
    );
    hashes.push(hash);
    const receipt = await c.chain.client.waitForTransactionReceipt({ hash });
    if (receipt.status !== 'success') fail('unavailable', `${functionName} reverted`);
    await walletSees(wc, hash);
    return receipt as never;
  };
  return { send, account };
}

/** The call that sends on what `address` holds of `asset`, if it is a deposit address of `token` into `record`'s burn
 * address, and where it goes: to `to`, signed by `record`'s refund signer, from one that names it; to its refund
 * address, from one that names one. Null for anything else, a deposit address that names another signer included. */
async function refundCall(
  ctx: Ctx,
  c: ChainCtx,
  record: DepositRecord,
  address: Address,
  token: Address,
  asset: Address,
  to: Address,
): Promise<{ call: Call; recipient: Address } | null> {
  const refund = await c.chain.depositAddressRefund(address, token, record.address);
  if (!refund) return null;
  if ('address' in refund) {
    return {
      call: { address, abi: depositAddressAbi, functionName: 'refund', args: [asset] },
      recipient: refund.address,
    };
  }
  // only the burn addresses of this wallet's own lane have refund signers
  if (record.burnIndex < 0) return null;
  const signer = refundAccount(ctx, { chainId: record.chainId, tokenId: record.tokenId, index: record.burnIndex });
  if (signer.address.toLowerCase() !== refund.signer.toLowerCase()) return null;
  // long enough for any wallet's confirmation; sent again before it, the signature moves only more to the same `to`
  const deadline = BigInt(Math.floor(Date.now() / 1000) + 86_400);
  const signature = await signer.signMessage({
    message: { raw: refundDigest(c.config.chainId, address, asset, to, deadline) },
  });
  return {
    call: { address, abi: depositAddressAbi, functionName: 'refundTo', args: [asset, to, deadline, signature] },
    recipient: to,
  };
}

const call3 = ({ address, abi, functionName, args }: Call) => ({
  target: address,
  allowFailure: false,
  callData: encodeFunctionData({ abi, functionName, args }),
});

/** Refunds the deposit at `index` of `record` to its sender, sent by `route.from` or the account's own wallet, which
 * pays the gas. A deposit address sends it on in the same transaction (Multicall3), so that nothing is left on it
 * between two: one of this wallet's to `route.to`, a point of sale's to the refund address its payer named. */
export async function rageExit(ctx: Ctx, record: DepositRecord, index: number, route: Route): Promise<Hex[]> {
  const c = chainCtx(ctx, record.chainId);
  const found = record.found.find((f) => f.index === index) ?? fail('invalid', `no deposit at ${index}`);
  if (found.spent) fail('invalid', 'the deposit is already spent');
  const hashes: Hex[] = [];
  const { send, account } = await sender(ctx, c, route.from, hashes);

  const after = await checkpointAfter(ctx, c, index, send);
  const { list, before } = await commitments(c, index, after);
  const prev = before[0];
  const ledger = await c.chain.ledger();
  const { calls, end } = walkBack(index, after, list, before);
  for (const args of calls) await send({ address: ledger, abi: ledgerAbi, functionName: 'checkpointBefore', args });
  const segment = list.slice(0, end - index);
  // checked first, so a wrong page from the indexer costs no gas
  await c.chain.client.readContract({
    address: ledger,
    abi: ledgerAbi,
    functionName: 'verifySegment',
    args: [BigInt(end), BigInt(prev), segment],
  });

  const key = spendKey(ctx);
  const { proof, signals } = await prove(
    ctx.network.circuits.rageexit,
    {
      chain_id: `${record.chainId}`,
      commitment_index: `${index}`,
      burn_address: BigInt(record.address).toString(),
      private_key: key.secret,
      auth_key_hash: key.authKeyHash,
      burn_salt: record.salt,
    },
    ctx.fetch,
  );
  const request = {
    checkpointIndex: BigInt(end),
    prevHashChain: BigInt(prev),
    commitments: segment,
    nullifier: signals[0],
    proof,
  };
  const exit: Call = { address: c.config.verifier, abi: verifierAbi, functionName: 'rageExit', args: [request] };
  // the deposit's commitment, which the ledger just authenticated: `tag, sender, burn address, amount`. A point of sale
  // registers its deposit addresses without telling this wallet, and a record restored from storage no longer knows
  // its own, so whether the sender is one is read on chain.
  const [, from, , amount] = list[0];
  const depositor = numberToHex(from, { size: 20 });
  const token = (await c.chain.tokens()).find((t) => t.tokenId === found.tokenId)!;
  const forward = await refundCall(ctx, c, record, depositor, token.address, token.address, route.to);
  if (forward) {
    // alone first, so that a failing rage exit says why rather than that the batch failed
    await c.chain.client.simulateContract({
      account,
      address: c.config.verifier,
      abi: verifierAbi,
      functionName: 'rageExit',
      args: [request],
    });
    await send({
      address: MULTICALL3,
      abi: multicall3Abi,
      functionName: 'aggregate3',
      args: [[call3(exit), call3(forward.call)]],
    });
  } else {
    await send(exit);
  }
  found.spent = true;
  // for every device of the wallet, written by the next sync
  ctx.state.receipts.push({
    kind: 'returned',
    chainId: record.chainId,
    tokenId: found.tokenId,
    burnAddress: record.address.toLowerCase() as Hex,
    index,
    recipient: (forward?.recipient ?? depositor).toLowerCase() as Hex,
    amount,
    txHash: hashes.at(-1)!,
    atMs: Date.now(),
    unwritten: true,
  });
  await ctx.save();
  return hashes;
}

/** Sends what `record`'s deposit address `address` holds of `asset` to `route.to` (to its refund address, if it names
 * one), sent by `route.from` or the account's own wallet. */
export async function refundDepositAddress(
  ctx: Ctx,
  record: DepositRecord,
  address: Address,
  asset: Address,
  route: Route,
): Promise<Hex> {
  const c = chainCtx(ctx, record.chainId);
  const token = (await c.chain.tokens()).find((t) => t.tokenId === record.tokenId)!;
  const refund =
    (await refundCall(ctx, c, record, address, token.address, asset, route.to)) ??
    fail(
      'invalid',
      `${address} is not deployed yet, or not one of this wallet's deposit addresses: it deploys on its first flush`,
    );
  const hashes: Hex[] = [];
  const { send } = await sender(ctx, c, route.from, hashes);
  await send(refund.call);
  return hashes[0];
}

/** Deposits what deposit address `receipt.depositAddress` holds, as the deposit relayer would, by a flush with all its
 * receipt says it was registered with, sent by `from`. */
export async function flushDepositAddress(ctx: Ctx, receipt: DepositAddressReceipt, from: WalletClient): Promise<Hex> {
  const { depositAddress } = receipt;
  const registered =
    receipt.args ??
    fail(
      'invalid',
      `${depositAddress}'s receipt does not say what it was registered with: only the relayer flushes it`,
    );
  const c = chainCtx(ctx, receipt.chainId);
  const token = (await c.chain.tokens()).find((t) => t.tokenId === receipt.tokenId)!;
  const { fee, feeRecipient, refundSigner, referrer, referralBps } = registered;
  const args = factoryArgs(
    token.address,
    receipt.burnAddress,
    { signer: refundSigner },
    feeRecipient,
    fee,
    referrer,
    referralBps,
  );
  // the flush takes the very arguments checked here: others make another address, empty
  if (!isAddressEqual(await c.chain.predictDepositAddress(args), depositAddress))
    fail('invalid', `${depositAddress} is not the factory's address for what its receipt says`);
  const held =
    token.underlying.toLowerCase() === NATIVE.toLowerCase()
      ? await c.chain.client.getBalance({ address: depositAddress })
      : await c.chain.client.readContract({
          address: token.underlying,
          abi: erc20Abi,
          functionName: 'balanceOf',
          args: [depositAddress],
        });
  // its flush would revert: nothing reached it since, or the relayer flushed it first
  if (held <= fee) fail('insufficient-funds', `${depositAddress} holds ${held}, not more than its fee of ${fee}`);
  const hashes: Hex[] = [];
  const { send } = await sender(ctx, c, from, hashes);
  await send({ address: c.config.depositAddressFactory, abi: depositFactoryAbi, functionName: 'flush', args });
  return hashes[0];
}
