import { NATIVE, type Network, type Token } from '@zerc20/wallet-sdk';
import { expect, test } from 'vitest';
import { loadNetwork } from '../src/account.js';
import { Usage } from '../src/errors.js';
import { amount, chainNamed, csv, parseAmount, table, tokensNamed, underlyingSymbol } from '../src/format.js';

test('an amount is taken exactly, in the token’s units, and never rounded to fit', () => {
  expect(parseAmount('10', 6)).toBe(10_000_000n);
  expect(parseAmount('0.000001', 6)).toBe(1n);
  expect(parseAmount('1.5', 18)).toBe(1_500_000_000_000_000_000n);
  expect(amount(parseAmount('12.34', 6), { decimals: 6 })).toBe('12.34');
  for (const bad of ['0.0000001', '-1', '1e3', '1,5', '.5', '', 'max'])
    expect(() => parseAmount(bad, 6)).toThrow(Usage);
});

test('a chain goes by its id, its name, or the start of its name where that names one', () => {
  const testnet = loadNetwork('testnet');
  expect(chainNamed(testnet, 'base').chainId).toBe(84532n);
  expect(chainNamed(testnet, 'Sepolia').chainId).toBe(11155111n);
  expect(chainNamed(testnet, '421614').chainId).toBe(421614n);
  expect(() => chainNamed(testnet, 'optimism')).toThrow(Usage);
  // every chain of the mainnet has a name of its own to go by
  const mainnet = loadNetwork('mainnet');
  for (const name of ['ethereum', 'base', 'arbitrum', 'bnb', 'polygon'])
    expect(chainNamed(mainnet, name)).toBeDefined();
});

test('a token goes by its own symbol or its asset’s, on every chain or the one named', () => {
  const network = {
    chains: [{ chainId: 1n }, { chainId: 56n, nativeCurrency: { name: 'BNB', symbol: 'BNB' } }],
  } as Network;
  const token = (chainId: bigint, symbol: string, underlying = '0x01') => ({ chainId, symbol, underlying }) as Token;
  const tokens = [token(1n, 'zUSDC'), token(56n, 'zUSDC'), token(1n, 'zETH', NATIVE), token(56n, 'zBNB', NATIVE)];
  expect(tokensNamed(network, tokens, 'usdc')).toEqual([tokens[0], tokens[1]]);
  expect(tokensNamed(network, tokens, 'zUSDC', network.chains[1])).toEqual([tokens[1]]);
  expect(tokensNamed(network, tokens, 'ETH')).toEqual([tokens[2]]);
  expect(underlyingSymbol(network, tokens[3]!)).toBe('BNB');
  expect(tokensNamed(network, tokens, 'bnb')).toEqual([tokens[3]]);
  expect(tokensNamed(network, tokens, 'DAI')).toEqual([]);
});

test('a table lines its columns up, and a CSV quotes what would break a row', () => {
  expect(
    table(
      ['A', 'N'],
      [
        ['long cell', '1'],
        ['x', '100'],
      ],
      [1],
    ),
  ).toBe('A            N\nlong cell    1\nx          100');
  expect(csv([['a', 'b,c', 'say "hi"']])).toBe('a,"b,c","say ""hi"""');
});
