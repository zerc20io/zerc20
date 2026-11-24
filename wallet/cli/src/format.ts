// What commands take and print: amounts in a token's own units, chains by name, tables and CSV.

import { type ChainConfig, NATIVE, type Network, type Token } from '@zerc20/wallet-sdk';
import { formatUnits } from 'viem';
import * as viemChains from 'viem/chains';
import { Usage } from './errors.js';

/** An amount typed in a token's units, in its base units. Exact: one with more decimals than the token has is refused
 * rather than rounded, as what is paid is what was typed. */
export function parseAmount(text: string, decimals: number): bigint {
  const m = /^(\d+)(?:\.(\d+))?$/.exec(text);
  if (!m) throw new Usage(`${text} is not an amount`);
  const fraction = m[2] ?? '';
  if (fraction.length > decimals) throw new Usage(`${text} has more than ${decimals} decimals`);
  return BigInt(m[1] + fraction.padEnd(decimals, '0'));
}

/** `value` in the token's units, as `parseAmount` takes it back. */
export const amount = (value: bigint, token: Pick<Token, 'decimals'>) => formatUnits(value, token.decimals);

/** Each chain's name, the first where several share an id, as the local chain's tools do. */
const names = new Map<bigint, string>();
for (const c of Object.values(viemChains)) {
  if (typeof c === 'object' && 'id' in c && 'name' in c && !names.has(BigInt(c.id))) names.set(BigInt(c.id), c.name);
}

export const chainName = (chainId: bigint) => names.get(chainId) ?? `chain ${chainId}`;

/** The chain of `network` named `text`: its id, its name, or where that names one alone, how its name starts
 * (`base` for Base Sepolia). */
export function chainNamed(network: Network, text: string): ChainConfig {
  const t = text.toLowerCase();
  const name = (c: ChainConfig) => chainName(c.chainId).toLowerCase();
  const exact = network.chains.filter((c) => String(c.chainId) === t || name(c) === t);
  const found = exact.length ? exact : network.chains.filter((c) => name(c).startsWith(t));
  if (found.length !== 1)
    throw new Usage(`--chain ${text}: one of ${network.chains.map((c) => chainName(c.chainId)).join(', ')}`);
  return found[0];
}

/** The symbol of the asset under `token`: the chain's native currency's, or the zERC20's own without its z. */
export function underlyingSymbol(network: Network, token: Token): string {
  if (token.underlying.toLowerCase() !== NATIVE.toLowerCase()) return token.symbol.replace(/^z/, '');
  return network.chains.find((c) => c.chainId === token.chainId)?.nativeCurrency?.symbol ?? 'ETH';
}

/** The tokens `symbol` names, on `chain` if given: a zERC20 by its own symbol or by that of the asset under it, as
 * both name the one private balance. */
export function tokensNamed(network: Network, tokens: Token[], symbol: string, chain?: ChainConfig): Token[] {
  const s = symbol.toLowerCase();
  return tokens.filter(
    (t) =>
      (!chain || t.chainId === chain.chainId) &&
      (t.symbol.toLowerCase() === s || underlyingSymbol(network, t).toLowerCase() === s),
  );
}

/** Rows under `head` in columns as wide as their widest cell, those named in `right` aligned to the right. */
export function table(head: string[], rows: string[][], right: number[] = []): string {
  const all = [head, ...rows];
  const width = head.map((_, i) => Math.max(...all.map((r) => r[i].length)));
  return all
    .map((r) =>
      r
        .map((cell, i) => (right.includes(i) ? cell.padStart(width[i]) : cell.padEnd(width[i])))
        .join('  ')
        .trimEnd(),
    )
    .join('\n');
}

export const csv = (rows: string[][]) =>
  rows
    .map((r) => r.map((cell) => (/[",\n]/.test(cell) ? `"${cell.replaceAll('"', '""')}"` : cell)).join(','))
    .join('\n');

/** A long id or address with its middle cut, for a table a person reads. */
export const short = (text: string) => (text.length > 24 ? `${text.slice(0, 14)}…${text.slice(-6)}` : text);

/** A time to the minute, in UTC. */
export const minute = (at: Date | null) => (at ? at.toISOString().slice(0, 16).replace('T', ' ') : '');

/** How long until `at`, roughly. */
export function until(at: Date, now = Date.now()): string {
  const mins = Math.max(1, Math.round((at.getTime() - now) / 60_000));
  return mins < 90 ? `~${mins} min` : `~${Math.round(mins / 60)} h`;
}
