// A forged root end to end, against the stack scripts/e2e.sh starts with SPEED=fast, whose ledger takes any root as a
// soundness bug in the root circuit would. Someone proves a root the indexer does not derive; the root-prover puts the
// ledger in an emergency by itself; the wallet keeps spending what the last honest root covers and rage-exits what
// came after; the watcher reports it; and a recovery through Admin brings the roots back.

import { readFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import {
  type Address,
  type Hex,
  createPublicClient,
  createTestClient,
  createWalletClient,
  defineChain,
  encodeFunctionData,
  http,
  parseAbi,
} from 'viem';
import { generatePrivateKey, privateKeyToAccount } from 'viem/accounts';
import { expect, test } from 'vitest';
import { type Balance, Wallet, networkFromJson } from '../../src/index.js';

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
// anvil account 0 deployed, so it owns Admin, which owns the ledger with a zero delay
const deployer = createWalletClient({
  account: privateKeyToAccount('0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80'),
  chain: anvil,
  transport: http(),
});
const watcherLog = () => readFileSync(join(dirname(path), 'watcher.log'), 'utf8');
const ETH = 10n ** 18n;
const FEE = ETH / 1000n; // the relayer's, set in scripts/dev-stack.sh
const NO_BOUND = 2n ** 64n - 1n;

const ledgerAbi = parseAbi([
  'struct RootState { uint64 index; uint256 hashChain; uint256 root; }',
  'struct NovaDeciderProof { uint256 challenge; uint256[2] runningCmE; uint256[2] cmT; uint256[2] runningCmW; uint256[2] incomingCmW; uint256[12] proof; }',
  'function proveRootTransition(RootState newState, NovaDeciderProof proof)',
  'function nextIndex() view returns (uint64)',
  'function hashChain() view returns (uint256)',
  'function bound() view returns (uint64)',
  'function provedRoots(uint64 index, uint256 root) view returns (bool)',
  'function rootVerifier() view returns (address)',
  'function owner() view returns (address)',
  'function recover(uint64 index, uint256 root, address rootVerifier)',
]);
const managerAbi = parseAbi(['function execute(address target, bytes data) payable returns (uint32)']);
const tokenAbi = parseAbi([
  'function wrap(uint256 amount, address receiver) payable',
  'function balanceOf(address) view returns (uint256)',
]);
const noProof = {
  challenge: 0n,
  runningCmE: [0n, 0n],
  cmT: [0n, 0n],
  runningCmW: [0n, 0n],
  incomingCmW: [0n, 0n],
  proof: [0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n],
} as const;

const ledgerAddress = () =>
  publicClient.readContract({
    address: chain.verifier,
    abi: parseAbi(['function ledger() view returns (address)']),
    functionName: 'ledger',
  });
const bound = async () =>
  publicClient.readContract({ address: await ledgerAddress(), abi: ledgerAbi, functionName: 'bound' });
const indexerStatus = async () =>
  (await (await fetch(`${chain.indexer}/status`)).json()) as {
    latest_root: { index: number; root: Hex } | null;
    mismatch: { index: number; root: Hex } | null;
  };

async function open(key: Hex): Promise<Wallet> {
  const walletClient = createWalletClient({ account: privateKeyToAccount(key), chain: anvil, transport: http() });
  let saved: Uint8Array | null = null;
  const seed = crypto.getRandomValues(new Uint8Array(32));
  return Wallet.open({
    network,
    walletClient,
    seed,
    persist: { load: async () => saved, save: async (b) => void (saved = b) },
  });
}

const balance = (w: Wallet): Balance => w.balances().find((b) => b.token.tokenId === 1)!;

async function until(
  w: Wallet | null,
  what: string,
  done: () => boolean | Promise<boolean>,
  ms = 300_000,
): Promise<void> {
  const end = Date.now() + ms;
  for (;;) {
    await w?.sync();
    if (await done()) return;
    if (Date.now() > end) throw new Error(`timed out: ${what}`);
    await new Promise((r) => setTimeout(r, 1000));
  }
}

/**
 * Proves a made-up root over a fresh commitment, at the live head, before the honest root-prover gets there: with the
 * blocks mined here, the proof lands in the block after the commitment's, and the root-prover needs two.
 */
async function forgeRoot(zeth: Address): Promise<{ index: bigint; root: bigint }> {
  const ledger = await ledgerAddress();
  const mined = async (hash: Hex) => {
    await testClient.mine({ blocks: 1 });
    return publicClient.waitForTransactionReceipt({ hash });
  };
  await testClient.setIntervalMining({ interval: 0 });
  try {
    for (let root = 1234n; root < 1244n; root++) {
      await mined(
        await deployer.writeContract({
          address: zeth,
          abi: tokenAbi,
          functionName: 'wrap',
          args: [1n, '0x000000000000000000000000000000000000dEaD'],
          value: 1n,
        }),
      );
      const [index, hashChain] = await Promise.all([
        publicClient.readContract({ address: ledger, abi: ledgerAbi, functionName: 'nextIndex' }),
        publicClient.readContract({ address: ledger, abi: ledgerAbi, functionName: 'hashChain' }),
      ]);
      try {
        const hash = await deployer.writeContract({
          address: ledger,
          abi: ledgerAbi,
          functionName: 'proveRootTransition',
          args: [{ index: BigInt(index), hashChain, root }, noProof],
        });
        if ((await mined(hash)).status === 'success') return { index: BigInt(index), root };
      } catch {
        // the honest root-prover, or another commitment, got there first
      }
    }
  } finally {
    await testClient.setIntervalMining({ interval: 1 }); // scripts/dev-stack.sh's --block-time
  }
  throw new Error('no forged root landed');
}

test.skipIf(process.env.SPEED !== 'fast')(
  'a forged root: an emergency by itself, spends under the honest root, rage exits, recovery',
  async () => {
    // a user of its own, so the other tests' state never meets this one's
    const key = generatePrivateKey();
    const account = privateKeyToAccount(key).address;
    await publicClient.waitForTransactionReceipt({
      hash: await deployer.sendTransaction({ to: account, value: 2n * ETH }),
    });
    const dave = await open(key);
    await dave.sync();
    const zeth = dave.tokens().find((t) => t.tokenId === 1)!;
    const zethBalance = (owner: Address) =>
      publicClient.readContract({ address: zeth.address, abi: tokenAbi, functionName: 'balanceOf', args: [owner] });
    await (await dave.deposit({ token: zeth, amount: (2n * ETH) / 10n })).wait();
    await until(dave, 'the deposit becomes spendable', () => balance(dave).spendable === (2n * ETH) / 10n);

    // The indexer names the forged root and stays on the honest one before it; the root-prover bounds the ledger there.
    const forged = await forgeRoot(zeth.address);
    await until(
      null,
      'the indexer finds the forged root',
      async () => BigInt((await indexerStatus()).mismatch?.index ?? -1) === forged.index,
    );
    const honest = (await indexerStatus()).latest_root!;
    await until(null, 'the root-prover enters an emergency', async () => (await bound()) === BigInt(honest.index));

    // What the honest root covers is still spendable; the change waits for the protocol to recover.
    const carol = privateKeyToAccount(generatePrivateKey()).address;
    await until(dave, 'the deposit stays spendable', () => balance(dave).spendable === (2n * ETH) / 10n);
    await (await dave.withdraw({ to: carol, token: zeth, amount: ETH / 20n, maxFee: FEE })).wait();
    expect(await zethBalance(carol)).toBe(ETH / 20n);
    const change = (2n * ETH) / 10n - ETH / 20n - FEE;
    await until(dave, 'the change is halted', () =>
      balance(dave).pending.some((p) => p.reason === 'roots-halted' && p.amount === change),
    );

    // A deposit no root will cover until then leaves by rage exit, which needs no root.
    await (await dave.deposit({ token: zeth, amount: ETH / 10n })).wait();
    const halted = () =>
      dave.coins().find((c) => c.kind === 'deposit' && c.amount === ETH / 10n && c.state === 'roots-halted');
    await until(dave, 'the new deposit is halted', () => !!halted());
    const before = await zethBalance(account);
    await dave.rageExit(halted()!.id);
    expect((await zethBalance(account)) - before).toBe(ETH / 10n);

    await until(
      null,
      'the watcher reports both',
      () =>
        watcherLog().includes('CRITICAL [local] the ledger proved root') &&
        watcherLog().includes('CRITICAL [local] the ledger is in an emergency'),
    );

    // The recovery: through the AccessManager (a zero delay here), from the honest root, with the same verifier.
    const ledger = await ledgerAddress();
    const [manager, verifier] = await Promise.all([
      publicClient.readContract({ address: ledger, abi: ledgerAbi, functionName: 'owner' }),
      publicClient.readContract({ address: ledger, abi: ledgerAbi, functionName: 'rootVerifier' }),
    ]);
    const recover = encodeFunctionData({
      abi: ledgerAbi,
      functionName: 'recover',
      args: [BigInt(honest.index), BigInt(honest.root), verifier],
    });
    await publicClient.waitForTransactionReceipt({
      hash: await deployer.writeContract({
        address: manager,
        abi: managerAbi,
        functionName: 'execute',
        args: [ledger, recover],
      }),
    });
    expect(await bound()).toBe(NO_BOUND);
    expect(
      await publicClient.readContract({
        address: ledger,
        abi: ledgerAbi,
        functionName: 'provedRoots',
        args: [forged.index, forged.root],
      }),
    ).toBe(false);
    // the indexer names the withdrawn root until it reads the recovery: the root-prover must not act on it meanwhile
    for (const end = Date.now() + 12_000; Date.now() < end; await new Promise((r) => setTimeout(r, 1000))) {
      expect(await bound()).toBe(NO_BOUND);
    }

    // Roots come back, and with them the change.
    await until(dave, 'the change becomes spendable', () => balance(dave).spendable === change);
    expect((await indexerStatus()).mismatch).toBeNull();
    await until(
      null,
      'the watcher resolves both',
      () =>
        watcherLog().includes('RESOLVED [local] the ledger proved root') &&
        watcherLog().includes('RESOLVED [local] the ledger is in an emergency'),
    );
    await dave.close();
  },
);
