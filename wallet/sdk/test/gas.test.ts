import {
  type EIP1193RequestFn,
  type Hex,
  createPublicClient,
  createWalletClient,
  custom,
  parseAbi,
  parseTransaction,
} from 'viem';
import { generatePrivateKey, privateKeyToAccount } from 'viem/accounts';
import { expect, test } from 'vitest';
import { roomy } from '../src/context.js';

test('a contract call is signed with a quarter more gas than the chain estimates, or with the gas it names', async () => {
  const signed: bigint[] = [];
  // a node that estimates every call at 100,000 gas, and keeps what is sent to it
  const request = (async ({ method, params }: { method: string; params: unknown[] }) => {
    if (method === 'eth_chainId') return '0x1';
    if (method === 'eth_estimateGas') return '0x186a0';
    if (method === 'eth_getTransactionCount' || method === 'eth_maxPriorityFeePerGas') return '0x1';
    if (method === 'eth_getBlockByNumber') return { baseFeePerGas: '0x1', number: '0x1' };
    if (method === 'eth_sendRawTransaction') {
      signed.push(parseTransaction(params[0] as Hex).gas!);
      return `0x${'00'.repeat(32)}`;
    }
    throw new Error(`unexpected ${method}`);
  }) as EIP1193RequestFn;
  const account = privateKeyToAccount(generatePrivateKey());
  const wc = roomy(
    createWalletClient({ account, transport: custom({ request }) }),
    createPublicClient({ transport: custom({ request }) }),
  );
  const call = {
    account,
    chain: null,
    address: '0x0000000000000000000000000000000000000001',
    abi: parseAbi(['function f()']),
    functionName: 'f',
  } as const;
  await wc.writeContract(call);
  await wc.writeContract({ ...call, gas: 50_000n });
  expect(signed).toEqual([125_000n, 50_000n]);
});
