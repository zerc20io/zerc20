import { expect, test } from 'vitest';
import type { Token } from '../src/chain.js';
import type { Ctx } from '../src/context.js';
import type { ChainConfig } from '../src/network.js';
import { type Hold, Wallet, lockWallet } from '../src/wallet.js';

/** A wallet over `lock` with no context: what the tests ask of it is refused before anything reads one. */
const walletOf = (lock: Hold) =>
  new (Wallet as unknown as new (ctx: Ctx, unlock: undefined, lock: Hold) => Wallet)({} as Ctx, undefined, lock);

/** The chains the wallets here open on. */
const net = { chains: [{ chainId: 8453n }, { chainId: 1n }] as ChainConfig[] };

const taken = (h: Hold) =>
  h.taken.aborted ? Promise.resolve() : new Promise((r) => h.taken.addEventListener('abort', r));

test('one wallet is open in one place at a time, until it is closed or taken', async () => {
  const address = '0x00000000000000000000000000000000000000aa';
  const first = await lockWallet(address, net);
  await expect(lockWallet(address, net)).rejects.toMatchObject({ code: 'wallet-in-use' });
  await expect(lockWallet(address.toUpperCase().replace('0X', '0x') as typeof address, net)).rejects.toMatchObject({
    code: 'wallet-in-use',
  });
  (await lockWallet('0x00000000000000000000000000000000000000bb', net)).release(); // another address opens
  (await lockWallet(address, net, 'view')).release(); // and a wallet that watches this one
  const other = { chainId: 10n } as ChainConfig;
  (await lockWallet(address, { chains: [other] })).release(); // and the account's wallet on another chain
  await new Promise((r) => setTimeout(r, 0));
  // one with a chain in common does not, and keeps none of the others it got
  await expect(lockWallet(address, { chains: [other, net.chains[0]!] })).rejects.toMatchObject({
    code: 'wallet-in-use',
  });
  await new Promise((r) => setTimeout(r, 0));
  (await lockWallet(address, { chains: [other] })).release();
  first.release();
  await new Promise((r) => setTimeout(r, 0)); // the lock goes once the promise it holds settles
  const again = await lockWallet(address, net);
  const took = await lockWallet(address, net, 'wallet', true);
  await taken(again);
  expect(again.taken.reason).toMatchObject({ code: 'wallet-taken' });
  expect(took.taken.aborted).toBe(false);
  took.release();
});

test('a tab whose wallet was taken reads and writes its state no more', async () => {
  const address = '0x00000000000000000000000000000000000000cc';
  const first = await lockWallet(address, net);
  const took = await lockWallet(address, net, 'wallet', true);
  await expect(first.guard(async () => 'written')).rejects.toMatchObject({ code: 'wallet-taken' });
  expect(await took.guard(async () => 'written')).toBe('written');
  took.release();
});

test('a closed wallet takes no more tasks; amounts must be positive', async () => {
  // no context: both are refused before anything reads it
  const make = () => new (Wallet as unknown as new (ctx: Ctx) => Wallet)({} as Ctx);
  const open = make();
  await expect(open.deposit({ token: {} as Token, amount: 0n })).rejects.toMatchObject({ code: 'invalid' });
  await expect(
    open.send({ to: '0x00000000000000000000000000000000000000bb', token: {} as Token, amount: 0n, maxFee: 0n }),
  ).rejects.toMatchObject({ code: 'invalid' });
  const closed = make();
  await closed.close();
  await expect(closed.sync()).rejects.toMatchObject({ code: 'wallet-closed' });
});

test('a wallet another tab takes takes no more tasks', async () => {
  const address = '0x00000000000000000000000000000000000000dd';
  const lock = await lockWallet(address, net);
  const wallet = walletOf(lock);
  const took = await lockWallet(address, net, 'wallet', true);
  await taken(lock);
  await expect(wallet.sync()).rejects.toMatchObject({ code: 'wallet-taken' });
  took.release();
});
