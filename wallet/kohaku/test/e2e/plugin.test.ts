// The plugin end to end, against the stack scripts/e2e.sh starts, as a Kohaku wallet drives it: a host over a mnemonic
// keystore, memory storage and a viem provider. A user shields USDC from the host's own account (the host signs the
// approval and the wrap), pays another account of the same keystore privately, and unshields to a third address.

import { readFileSync } from 'node:fs';
import { type Host, InsufficientBalanceError, MemoryStorage, MnemonicKeystore } from '@kohaku-eth/plugins';
import { viem } from '@kohaku-eth/provider/viem';
import { networkFromJson } from '@zerc20/wallet-sdk';
import { createPublicClient, createWalletClient, defineChain, erc20Abi, http, parseAbi } from 'viem';
import { generatePrivateKey, privateKeyToAccount } from 'viem/accounts';
import { expect, test } from 'vitest';
import {
  type Zerc20AssetAmount,
  type Zerc20Instance,
  createZerc20Broadcaster,
  createZerc20Plugin,
} from '../../src/index.js';

const path =
  process.env.NETWORK ??
  (() => {
    throw new Error('run through scripts/e2e.sh');
  })();
const network = networkFromJson(readFileSync(path, 'utf8'));
const anvil = defineChain({
  id: 31337,
  name: 'anvil',
  nativeCurrency: { name: 'ETH', symbol: 'ETH', decimals: 18 },
  rpcUrls: { default: { http: network.chains[0]!.rpcUrls } },
});
const publicClient = createPublicClient({ chain: anvil, transport: http() });
// anvil account 0 deployed; here it only funds the host's account with gas
const deployer = createWalletClient({
  account: privateKeyToAccount('0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80'),
  chain: anvil,
  transport: http(),
});
const USDC = 10n ** 6n;
const FEE = 10_000n; // the relayer's for zUSDC, set in scripts/dev-stack.sh

const host = (keystore: MnemonicKeystore): Host => ({
  network: { fetch: (input, init) => fetch(input, init) },
  storage: new MemoryStorage(),
  keystore,
  provider: viem(publicClient),
});

async function until(what: string, done: () => Promise<boolean>, ms = 300_000): Promise<void> {
  const end = Date.now() + ms;
  while (!(await done())) {
    if (Date.now() > end) throw new Error(`timed out: ${what}`);
    await new Promise((r) => setTimeout(r, 1000));
  }
}

const spendable = async (plugin: Zerc20Instance, asset: Zerc20AssetAmount['asset']) =>
  (await plugin.balance([asset])).find((b) => b.tag === undefined)!.amount;

test('shield from the host, pay another account, unshield', async () => {
  const keystore = MnemonicKeystore.random();
  const alice = await createZerc20Plugin(host(keystore), { network, accountIndex: 0 });
  const bob = await createZerc20Plugin(host(keystore), { network, accountIndex: 1 });
  expect(await alice.instanceId()).toMatch(/^zerc20id1/);
  expect(await bob.instanceId()).not.toBe(await alice.instanceId());

  // the host's own account, which holds the public funds and signs what prepareShield returns
  const signer = createWalletClient({
    account: privateKeyToAccount(generatePrivateKey()),
    chain: anvil,
    transport: http(),
  });
  await publicClient.waitForTransactionReceipt({
    hash: await deployer.sendTransaction({ to: signer.account.address, value: 10n ** 18n }),
  });
  await alice.sync();
  const zusdc = alice.wallet.tokens().find((t) => t.tokenId === 2)!;
  const usdc = { __type: 'erc20', contract: zusdc.underlying } as const;
  await publicClient.waitForTransactionReceipt({
    hash: await signer.writeContract({
      address: zusdc.underlying,
      abi: parseAbi(['function mint(address to, uint256 amount)']),
      functionName: 'mint',
      args: [signer.account.address, 1000n * USDC],
    }),
  });

  const { txns } = await alice.prepareShield({ asset: usdc, amount: 100n * USDC });
  expect(txns.map((t) => t.to)).toEqual([zusdc.underlying, zusdc.address]); // the approval, then the wrap
  for (const tx of txns) await publicClient.waitForTransactionReceipt({ hash: await signer.sendTransaction(tx) });
  await until('the shield becomes spendable', async () => (await spendable(alice, usdc)) === 100n * USDC);

  await expect(alice.prepareTransfer({ asset: usdc, amount: 101n * USDC }, await bob.instanceId())).rejects.toThrow(
    InsufficientBalanceError,
  );
  const broadcaster = createZerc20Broadcaster(alice);
  const pay = await alice.prepareTransfer({ asset: usdc, amount: 10n * USDC }, await bob.instanceId());
  expect(pay.maxFee).toBeGreaterThanOrEqual(FEE); // the relayer's, and the protocol's cut of what pays it
  await broadcaster.broadcast(pay);
  await until('bob can spend the payment', async () => (await spendable(bob, usdc)) === 10n * USDC);

  // named by the underlying asset, an unshield pays it out unwrapped
  const carol = privateKeyToAccount(generatePrivateKey()).address;
  const out = await alice.prepareUnshield({ asset: usdc, amount: 5n * USDC }, carol);
  const { txHashes } = await broadcaster.broadcast(out);
  expect(txHashes).toHaveLength(1);
  expect(
    await publicClient.readContract({
      address: zusdc.underlying,
      abi: erc20Abi,
      functionName: 'balanceOf',
      args: [carol],
    }),
  ).toBe(5n * USDC);

  await alice.wallet.close();
  await bob.wallet.close();
});
