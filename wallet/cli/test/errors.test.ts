import { createPublicClient, http, parseAbi } from 'viem';
import { expect, test } from 'vitest';
import { told } from '../src/errors.js';

test('a call an RPC refuses is told once: the failure, what the RPC answered and which RPC', async () => {
  const fetchFn = async (_: unknown, init?: RequestInit) => {
    const { id } = JSON.parse(init!.body as string) as { id: number };
    return Response.json({ jsonrpc: '2.0', id, error: { code: 30, message: 'Request timeout on the free plan' } });
  };
  const client = createPublicClient({ transport: http('https://rpc.example', { fetchFn, retryCount: 0 }) });
  const read = client.readContract({
    address: '0x32c83780bc6Ac14e8A2938d4Fd192d3721ef3D9f',
    abi: parseAbi(['function symbol() view returns (string)']),
    functionName: 'symbol',
  });
  const e = await read.catch((e: Error) => e);
  expect(told(e as Error)).toBe('RPC Request failed. Request timeout on the free plan (https://rpc.example)');
});

test('any other error is told down its causes', () => {
  const e = new Error('the indexer does not answer', { cause: new Error('connect ECONNREFUSED') });
  expect(told(e)).toBe('the indexer does not answer\nconnect ECONNREFUSED');
});
