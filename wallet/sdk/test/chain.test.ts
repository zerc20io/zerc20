import { type Address, type Hex, decodeFunctionData, encodeFunctionResult, getAddress } from 'viem';
import { beforeAll, beforeEach, expect, test, vi } from 'vitest';
import { Chain, NATIVE, factoryAbi, tokenAbi, verifierAbi } from '../src/chain.js';
import type { ChainConfig } from '../src/network.js';

const VERIFIER: Address = '0x00000000000000000000000000000000000000a1';
const FACTORY: Address = '0x00000000000000000000000000000000000000f1';
const LEDGER = getAddress('0x00000000000000000000000000000000000000b1');
const tokenAt = (id: number): Address => `0x${id.toString(16).padStart(40, '0')}`;

/** The chain's RPC: a verifier whose factory has `count` tokens. Every call it answers is in `calls`, by function name
 * and argument; it refuses the next calls with the errors in `refusals`, a rate limit as Tenderly's gateways send it. */
const rpc = { count: 1, calls: [] as string[], refusals: [] as ('rate-limit' | 'invalid')[] };

function answer(to: Address, data: Hex): Hex {
  to = to.toLowerCase() as Address;
  if (to === VERIFIER) {
    const { functionName } = decodeFunctionData({ abi: verifierAbi, data });
    rpc.calls.push(functionName);
    if (functionName === 'factory') return encodeFunctionResult({ abi: verifierAbi, functionName, result: FACTORY });
    if (functionName === 'ledger') return encodeFunctionResult({ abi: verifierAbi, functionName, result: LEDGER });
  }
  if (to === FACTORY) {
    const call = decodeFunctionData({ abi: factoryAbi, data });
    if (call.functionName === 'tokenCount') {
      rpc.calls.push('tokenCount');
      return encodeFunctionResult({ abi: factoryAbi, functionName: 'tokenCount', result: rpc.count });
    }
    rpc.calls.push(`tokenById(${call.args[0]})`);
    return encodeFunctionResult({ abi: factoryAbi, functionName: 'tokenById', result: tokenAt(call.args[0]) });
  }
  const id = Number(BigInt(to));
  const { functionName } = decodeFunctionData({ abi: tokenAbi, data });
  rpc.calls.push(`${functionName}(${id})`);
  if (functionName === 'symbol') return encodeFunctionResult({ abi: tokenAbi, functionName, result: `z${id}` });
  if (functionName === 'decimals') return encodeFunctionResult({ abi: tokenAbi, functionName, result: 18 });
  return encodeFunctionResult({ abi: tokenAbi, functionName: 'underlyingAsset', result: NATIVE });
}

beforeAll(() => {
  vi.stubGlobal('fetch', async (_: unknown, init?: RequestInit) => {
    const { id, params } = JSON.parse(init!.body as string) as { id: number; params: [{ to: Address; data: Hex }] };
    const refusal = rpc.refusals.shift();
    if (refusal === 'rate-limit')
      return Response.json(
        { jsonrpc: '2.0', id, error: { code: -32005, message: 'rate limit exceeded' } },
        { status: 429 },
      );
    if (refusal === 'invalid')
      return Response.json({ jsonrpc: '2.0', id, error: { code: -32602, message: 'invalid params' } });
    return Response.json({ jsonrpc: '2.0', id, result: answer(params[0].to, params[0].data) });
  });
});

beforeEach(() => Object.assign(rpc, { count: 1, calls: [], refusals: [] }));

const chain = () => new Chain({ chainId: 1n, rpcUrls: ['https://rpc.example'], verifier: VERIFIER } as ChainConfig);

test('the factory is read once, its count every time, and each token only when it is new', async () => {
  const c = chain();
  const [first] = await c.tokens();
  expect((await c.tokens())[0]).toBe(first);
  rpc.count = 2;
  const tokens = await c.tokens();
  expect(tokens.map((t) => t.symbol)).toEqual(['z1', 'z2']);
  // the token read before is kept as it was: balances and coins find their token by identity
  expect(tokens[0]).toBe(first);
  expect(c.known).toBe(tokens);
  expect(rpc.calls.filter((f) => f === 'factory')).toHaveLength(1);
  expect(rpc.calls.filter((f) => f === 'tokenCount')).toHaveLength(3);
  expect(rpc.calls.filter((f) => f.startsWith('tokenById'))).toEqual(['tokenById(1)', 'tokenById(2)']);
});

test('nothing is known before the tokens are read', () => {
  expect(chain().known).toEqual([]);
});

test('while the first read fails the tokens saved stand for it, and a later read adds only the new ones', async () => {
  const saved = await chain().tokens();
  const c = chain();
  rpc.refusals = ['invalid'];
  // with none saved the failure is the answer: a saved wallet names tokens that nothing else tells
  await expect(c.tokens()).rejects.toThrow();
  rpc.refusals = ['invalid'];
  expect(await c.tokens(saved)).toBe(saved);
  expect(c.known).toBe(saved);
  rpc.count = 2;
  const tokens = await c.tokens(saved);
  expect(tokens.map((t) => t.symbol)).toEqual(['z1', 'z2']);
  expect(tokens[0]).toBe(saved[0]);
});

test('a read that fails is not kept: the next call reads again, and its result is kept', async () => {
  const c = chain();
  rpc.refusals = ['invalid'];
  await expect(c.ledger()).rejects.toThrow('Invalid parameters');
  expect(await c.ledger()).toBe(LEDGER);
  expect(await c.ledger()).toBe(LEDGER);
  expect(rpc.calls.filter((f) => f === 'ledger')).toHaveLength(1);

  rpc.refusals = ['invalid'];
  await expect(c.tokens()).rejects.toThrow('Invalid parameters');
  expect((await c.tokens()).map((t) => t.symbol)).toEqual(['z1']);
  await c.tokens();
  expect(rpc.calls.filter((f) => f === 'factory')).toHaveLength(1);
});

test('a rate limit is waited out past the second it counts', async () => {
  // four refusals: 0.15 + 0.3 + 0.6 + 1.2 s of waiting, beyond viem's default three retries
  rpc.refusals = ['rate-limit', 'rate-limit', 'rate-limit', 'rate-limit'];
  expect(await chain().ledger()).toBe(LEDGER);
  expect(rpc.refusals).toEqual([]);
}, 10_000);
