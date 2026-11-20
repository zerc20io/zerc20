// A merchant end to end, against the stack scripts/e2e.sh starts: the merchant's wallet makes a key for its point of
// sale, which records payment addresses in its lane and hands them out, holding no spending key; a customer pays in
// zETH to one and in ETH to a deposit address;
// with a merge prover (SPEED=fast or MERGE=1 runs one) the wallet merges both into one note; it withdraws, and
// returns a payment the ASP rejected, and one through a deposit address that names the payer's refund address. Every
// proof is real but the root and merge proofs SPEED=fast skips.

import { readFileSync } from 'node:fs';
import {
  type Address,
  type Hex,
  createPublicClient,
  createTestClient,
  createWalletClient,
  defineChain,
  http,
  parseAbi,
} from 'viem';
import { generatePrivateKey, privateKeyToAccount } from 'viem/accounts';
import { expect, test } from 'vitest';
import { type Balance, PointOfSale, Wallet, networkFromJson, seedFromSignature } from '../../src/index.js';

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
const testClient = createTestClient({ mode: 'anvil', chain: anvil, transport: http() });

// anvil account 11 is the sender the ASP rejects (dev-stack.sh)
const REJECTED = '0x701b615bbdfb9de65240bc28bd21bbc0d996645a3dd57e7b12bc2bdf6f192c82';
const ETH = 10n ** 18n;
const FEE = ETH / 1000n; // the relayer's, set in scripts/dev-stack.sh
const tokenAbi = parseAbi([
  'function wrap(uint256 amount, address receiver) payable',
  'function balanceOf(address) view returns (uint256)',
]);

/** A new account holding 100 ETH, set rather than sent, so tests running side by side share no nonce. */
async function fresh(): Promise<Hex> {
  const key = generatePrivateKey();
  await testClient.setBalance({ address: privateKeyToAccount(key).address, value: 100n * ETH });
  return key;
}

/** The merchant's wallet, keeping its state in `state` as an app would keep it in storage. */
async function open(key: Hex, state: { saved: Uint8Array | null }): Promise<Wallet> {
  const walletClient = createWalletClient({ account: privateKeyToAccount(key), chain: anvil, transport: http() });
  const { seed } = await seedFromSignature(walletClient);
  return Wallet.open({ network, walletClient, seed, persist: memory(state) });
}

const memory = (state: { saved: Uint8Array | null }) => ({
  load: async () => state.saved,
  save: async (b: Uint8Array) => void (state.saved = b),
});

const balance = (w: Wallet): Balance => w.balances().find((b) => b.token.tokenId === 1)!;

async function until(
  w: Wallet | null,
  what: string,
  done: () => boolean | Promise<boolean>,
  ms = 900_000,
): Promise<void> {
  const end = Date.now() + ms;
  for (;;) {
    await w?.sync();
    if (await done()) return;
    if (Date.now() > end) throw new Error(`timed out: ${what}`);
    await new Promise((r) => setTimeout(r, 1000));
  }
}

test('a point of sale hands out addresses with no key, and the wallet spends what they receive', async () => {
  const [merchantKey, customer] = [await fresh(), await fresh()];
  let merchant = await open(merchantKey, { saved: null });
  await merchant.sync();
  const zeth = merchant.tokens().find((t) => t.tokenId === 1)!;

  // The merchant's wallet makes a key for the point of sale, which makes and records payment addresses with it.
  const key = await merchant.posKey();
  const till = await PointOfSale.open({ network, persist: memory({ saved: null }) });
  await till.connect(merchant.address, key);
  const burn = await till.next({ via: 'burn', token: zeth, amount: ETH / 10n });
  const deposit = await till.next({ via: 'deposit', token: zeth, amount: (2n * ETH) / 10n });
  const refused = await till.next({ via: 'burn', token: zeth });
  expect(deposit.depositAddress).toMatch(/^0x/);
  expect(deposit.refundTo).toBe(merchant.address);
  expect(new Set([burn.burnAddress, deposit.burnAddress, refused.burnAddress]).size).toBe(3);

  // A customer pays 0.1 zETH (wrapping ETH straight into the burn address) and 0.2 ETH plus the deposit relayer's fee to
  // the deposit address, as an exchange withdrawal would; someone the ASP rejects pays 0.05 zETH.
  const pay = async (key: Hex, to: Address, amount: bigint, asEth = false) => {
    const client = createWalletClient({ account: privateKeyToAccount(key), chain: anvil, transport: http() });
    const hash = asEth
      ? await client.sendTransaction({ to, value: amount })
      : await client.writeContract({
          address: zeth.address,
          abi: tokenAbi,
          functionName: 'wrap',
          args: [amount, to],
          value: amount,
        });
    await publicClient.waitForTransactionReceipt({ hash });
  };
  await pay(customer, burn.burnAddress, ETH / 10n);
  await pay(customer, deposit.depositAddress!, (2n * ETH) / 10n + deposit.depositFee!, true);
  await pay(REJECTED, refused.burnAddress, ETH / 20n);

  // The point of sale sees each payment from the pages every wallet reads, all three in one pass: final, then as the
  // ASP decides.
  await until(null, 'the point of sale sees each payment decided', async () => {
    const [b, d, r] = (await till.refresh([burn.id, deposit.id, refused.id])).sales;
    return (
      b!.received === ETH / 10n &&
      b!.payments.every((p) => p.state === 'approved' && p.txHash !== null) &&
      d!.payments.some((p) => p.state === 'approved') &&
      r!.payments.some((p) => p.state === 'rejected')
    );
  });

  await until(merchant, 'the wallet holds both payments', () => balance(merchant).spendable === (3n * ETH) / 10n);
  // each shows as a sale, at the address its point of sale handed out
  const sold = merchant
    .activity()
    .filter((a) => a.kind === 'sale')
    .map((a) => a.burnAddress!.toLowerCase());
  expect(sold.sort()).toEqual(
    [burn.burnAddress, deposit.burnAddress, refused.burnAddress].map((a) => a.toLowerCase()).sort(),
  );

  // With the merge prover, the wallet merges the two approved payments into one note, paying the relayer once; the
  // payments read spent once their nullifiers are final, and the merged note takes their place.
  if (network.mergeProver) {
    await (await merchant.consolidate({ token: zeth, maxFee: FEE })).wait();
    const states = () =>
      merchant
        .payments()
        .map((p) => `${p.amount}:${p.state}`)
        .sort();
    const merged = [`${ETH / 10n}:spent`, `${(2n * ETH) / 10n}:spent`, `${ETH / 20n}:rejected`].sort();
    await until(
      merchant,
      'the wallet holds the merged note',
      () => states().join() === merged.join() && balance(merchant).spendable === (3n * ETH) / 10n - FEE,
    );
    expect(
      merchant
        .activity()
        .filter((a) => a.kind === 'merged')
        .map((a) => a.amount),
    ).toEqual([(3n * ETH) / 10n - FEE]);
  }

  // The merchant withdraws with its wallet, as any wallet would: without the merge, from the 0.2 payment alone.
  const payout = privateKeyToAccount(customer).address;
  const before = await publicClient.readContract({
    address: zeth.address,
    abi: tokenAbi,
    functionName: 'balanceOf',
    args: [payout],
  });
  await (await merchant.withdraw({ to: payout, token: zeth, amount: ETH / 10n, maxFee: FEE })).wait();
  const after = await publicClient.readContract({
    address: zeth.address,
    abi: tokenAbi,
    functionName: 'balanceOf',
    args: [payout],
  });
  expect(after - before).toBe(ETH / 10n);

  // The rejected payment goes back to its sender by rage exit, from the merchant's wallet.
  const rejected = merchant.payments().find((p) => p.state === 'rejected')!;
  const refundTo = privateKeyToAccount(REJECTED).address;
  const held = await publicClient.readContract({
    address: zeth.address,
    abi: tokenAbi,
    functionName: 'balanceOf',
    args: [refundTo],
  });
  await merchant.rageExit(rejected.id);
  expect(
    await publicClient.readContract({
      address: zeth.address,
      abi: tokenAbi,
      functionName: 'balanceOf',
      args: [refundTo],
    }),
  ).toBe(held + ETH / 20n);

  // A device starting from nothing (restoring from the chain's start) finds the same payments and balance from the
  // seed, storage and the chain, and makes the next point of sale a lane of its own.
  // Without the merge, the 0.1 payment is left as it was.
  await merchant.close();
  merchant = await open(merchantKey, { saved: null });
  const [spent, left] = network.mergeProver ? [3, (2n * ETH) / 10n - 2n * FEE] : [2, (2n * ETH) / 10n - FEE];
  await until(
    merchant,
    'a fresh wallet finds the payments',
    () => merchant.payments().length === 3 && merchant.payments().filter((p) => p.state === 'spent').length === spent,
  );
  await until(merchant, 'a fresh wallet finds the change', () => balance(merchant).spendable === left);
  expect(await merchant.posKey()).not.toBe(key);
  await merchant.close();
});

test("a payment through a deposit address that names the payer's refund address goes back there by rage exit", async () => {
  const [merchantKey, customer] = [await fresh(), await fresh()];
  const merchant = await open(merchantKey, { saved: null });
  await merchant.sync();
  const zeth = merchant.tokens().find((t) => t.tokenId === 1)!;
  const till = await PointOfSale.open({ network, persist: memory({ saved: null }) });
  await till.connect(merchant.address, await merchant.posKey());
  const refundTo = privateKeyToAccount(generatePrivateKey()).address;
  const sale = await till.next({ via: 'deposit', token: zeth, refundTo });
  expect(sale.refundTo).toBe(refundTo);

  const client = createWalletClient({ account: privateKeyToAccount(customer), chain: anvil, transport: http() });
  await publicClient.waitForTransactionReceipt({
    hash: await client.sendTransaction({ to: sale.depositAddress!, value: ETH / 10n + sale.depositFee! }),
  });
  await until(merchant, 'the wallet sees the payment approved', () =>
    merchant.payments().some((p) => p.amount === ETH / 10n && p.state === 'approved'),
  );

  // the rage exit lands on the deposit address, which the wallet forwards to the refund address its code names
  await merchant.rageExit(merchant.payments().find((p) => p.amount === ETH / 10n)!.id);
  expect(
    await publicClient.readContract({
      address: zeth.address,
      abi: tokenAbi,
      functionName: 'balanceOf',
      args: [refundTo],
    }),
  ).toBe(ETH / 10n);
  await merchant.close();
});
