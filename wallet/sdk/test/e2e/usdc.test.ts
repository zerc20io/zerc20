// zUSDC end to end, against the stack scripts/e2e.sh starts: a token over an ERC20 (a DummyUSDC anyone may mint) works
// as zETH does. A user mints USDC, deposits it (approving first), withdraws part publicly, and pays a deposit address
// from the account, which the deposit relayer flushes. The user's app takes a share of that payment as its referrer.

import { readFileSync } from 'node:fs';
import {
  type Address,
  type Hex,
  createPublicClient,
  createWalletClient,
  defineChain,
  erc20Abi,
  http,
  parseAbi,
} from 'viem';
import { generatePrivateKey, privateKeyToAccount } from 'viem/accounts';
import { expect, test } from 'vitest';
import { type Balance, type Referrer, Wallet, networkFromJson } from '../../src/index.js';

const path =
  process.env.NETWORK ??
  (() => {
    throw new Error('run through scripts/e2e.sh');
  })();
const network = networkFromJson(readFileSync(path, 'utf8'));
const chain = network.chains[0]!;
const anvil = defineChain({
  id: 31337,
  name: 'anvil',
  nativeCurrency: { name: 'ETH', symbol: 'ETH', decimals: 18 },
  rpcUrls: { default: { http: chain.rpcUrls } },
});
const publicClient = createPublicClient({ chain: anvil, transport: http() });
// anvil account 0 deployed; here it only funds the user with gas
const deployer = createWalletClient({
  account: privateKeyToAccount('0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80'),
  chain: anvil,
  transport: http(),
});
const USDC = 10n ** 6n;
const FEE = 10_000n; // the relayer's for zUSDC, set in scripts/dev-stack.sh

async function open(key: Hex, referrer?: Referrer): Promise<Wallet> {
  const walletClient = createWalletClient({ account: privateKeyToAccount(key), chain: anvil, transport: http() });
  let saved: Uint8Array | null = null;
  const seed = crypto.getRandomValues(new Uint8Array(32));
  return Wallet.open({
    network,
    walletClient,
    seed,
    persist: { load: async () => saved, save: async (b) => void (saved = b) },
    referrer,
  });
}

async function until(w: Wallet, what: string, done: () => boolean, ms = 300_000): Promise<void> {
  const end = Date.now() + ms;
  for (;;) {
    await w.sync();
    if (done()) return;
    if (Date.now() > end) throw new Error(`timed out: ${what}`);
    await new Promise((r) => setTimeout(r, 1000));
  }
}

test('an ERC20 token: mint, deposit (approve, then wrap), withdraw, a deposit address', async () => {
  const key = generatePrivateKey();
  const account = privateKeyToAccount(key).address;
  await publicClient.waitForTransactionReceipt({
    hash: await deployer.sendTransaction({ to: account, value: 10n ** 18n }),
  });
  const app: Referrer = { address: privateKeyToAccount(generatePrivateKey()).address, bps: 30 };
  const user = await open(key, app);
  await user.sync();
  const zusdc = user.tokens().find((t) => t.tokenId === 2)!;
  expect([zusdc.symbol, zusdc.decimals]).toEqual(['zUSDC', 6]);
  const balance = (): Balance => user.balances().find((b) => b.token.tokenId === 2)!;
  const balanceOf = (token: Address, owner: Address) =>
    publicClient.readContract({ address: token, abi: erc20Abi, functionName: 'balanceOf', args: [owner] });

  // the demo's mint button
  const own = createWalletClient({ account: privateKeyToAccount(key), chain: anvil, transport: http() });
  const minted = await own.writeContract({
    address: zusdc.underlying,
    abi: parseAbi(['function mint(address to, uint256 amount)']),
    functionName: 'mint',
    args: [account, 1000n * USDC],
  });
  await publicClient.waitForTransactionReceipt({ hash: minted });

  // more than the account holds fails at once, before any approval is asked for
  await expect(user.deposit({ token: zusdc, amount: 1001n * USDC })).rejects.toMatchObject({
    code: 'insufficient-funds',
  });
  expect(user.operations()).toEqual([]);

  // the SDK approves the token to take the USDC, then wraps it into a fresh burn address
  await (await user.deposit({ token: zusdc, amount: 100n * USDC })).wait();
  expect(await balanceOf(zusdc.underlying, account)).toBe(900n * USDC);
  await until(user, 'the deposit becomes spendable', () => balance().spendable === 100n * USDC);

  const carol = privateKeyToAccount(generatePrivateKey()).address;
  expect(await user.fees({ kind: 'withdraw', token: zusdc, amount: 10n * USDC })).toMatchObject({
    relayer: FEE,
    steps: 1,
  });
  await (await user.withdraw({ to: carol, token: zusdc, amount: 10n * USDC, maxFee: FEE })).wait();
  expect(await balanceOf(zusdc.address, carol)).toBe(10n * USDC);
  await until(user, 'the change', () => balance().spendable === 90n * USDC - FEE);

  // USDC sent to a deposit address, as from an exchange: the relayer takes its fee, the app 0.3% of the rest, and the
  // rest is wrapped into the burn address
  const { address: depositAddress, fee: depositFee } = await user.depositAddress(zusdc);
  const referral = (5n * USDC * 30n) / 10_000n;
  const sent = await own.writeContract({
    address: zusdc.underlying,
    abi: erc20Abi,
    functionName: 'transfer',
    args: [depositAddress, 5n * USDC + depositFee],
  });
  await publicClient.waitForTransactionReceipt({ hash: sent });
  await until(user, 'the deposit address is flushed', () =>
    user
      .deposits()
      .some((d) => d.amount === 5n * USDC - referral && d.sender?.toLowerCase() === depositAddress.toLowerCase()),
  );
  expect(await balanceOf(zusdc.underlying, app.address)).toBe(referral);
  await until(user, 'it is spendable too', () => balance().spendable === 95n * USDC - FEE - referral);
  await user.close();
});
