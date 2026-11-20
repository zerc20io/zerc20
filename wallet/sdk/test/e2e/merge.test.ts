// Consolidations end to end, against the stack scripts/e2e.sh starts. Bob holds two notes and two deposits, one paid
// to a receive code by a plain transfer and one through a deposit address, and no single JoinSplit withdraws most of
// it; Alice holds two deposits, chooses one to turn into a note and takes the other out by rage exit. Another device of
// each, starting from nothing, then shows the same history. Without a merge prover (SPEED=fast or MERGE=1 runs one)
// both wallets say why they cannot merge, and the merges themselves are skipped. Each test plays its own users on fresh accounts, side by
// side.

import { readFileSync } from 'node:fs';
import { decodeCode } from '@zerc20/storage-sdk';
import {
  type Address,
  type Hex,
  bytesToHex,
  createPublicClient,
  createTestClient,
  createWalletClient,
  defineChain,
  http,
  keccak256,
  parseAbi,
} from 'viem';
import { generatePrivateKey, privateKeyToAccount } from 'viem/accounts';
import { expect, test } from 'vitest';
import { type Balance, Wallet, networkFromJson } from '../../src/index.js';
import { sameElsewhere } from './history.js';

const path =
  process.env.NETWORK ??
  (() => {
    throw new Error('run through scripts/e2e.sh');
  })();
const network = networkFromJson(readFileSync(path, 'utf8'));
const rpc = network.chains[0]!.rpcUrls[0]!;
const anvil = defineChain({
  id: 31337,
  name: 'anvil',
  nativeCurrency: { name: 'ETH', symbol: 'ETH', decimals: 18 },
  rpcUrls: { default: { http: [rpc] } },
});
const publicClient = createPublicClient({ chain: anvil, transport: http() });
const testClient = createTestClient({ mode: 'anvil', chain: anvil, transport: http() });
const ETH = 10n ** 18n;
const FEE = ETH / 1000n; // the relayer's, set in scripts/dev-stack.sh
const tokenAbi = parseAbi([
  'function wrap(uint256 amount, address receiver) payable',
  'function transfer(address, uint256) returns (bool)',
  'function balanceOf(address) view returns (uint256)',
]);
// a merge is a note to self, shown as merged once on chain
const merged = network.mergeProver ? ['merged'] : [];

const client = (key: Hex) => createWalletClient({ account: privateKeyToAccount(key), chain: anvil, transport: http() });
const mined = async (hash: Promise<Hex>) => publicClient.waitForTransactionReceipt({ hash: await hash });

/** A new account holding 100 ETH, set rather than sent, so tests running side by side share no nonce. */
async function fresh(): Promise<Hex> {
  const key = generatePrivateKey();
  await testClient.setBalance({ address: privateKeyToAccount(key).address, value: 100n * ETH });
  return key;
}

/** A user's wallet on a device of its own, keeping its state in memory as an app would keep it in storage. */
async function open(key: Hex): Promise<Wallet> {
  const walletClient = client(key);
  let saved: Uint8Array | null = null;
  const seed = Uint8Array.from(Buffer.from(keccak256(key).slice(2), 'hex'));
  return Wallet.open({
    network,
    walletClient,
    seed,
    persist: { load: async () => saved, save: async (b) => void (saved = b) },
  });
}

const balance = (w: Wallet): Balance => w.balances().find((b) => b.token.tokenId === 1)!;
const kinds = (w: Wallet) =>
  w
    .activity()
    .map((a) => a.kind)
    .sort();

/** Syncs until `done` holds. */
async function until(w: Wallet, what: string, done: () => boolean, ms = 600_000): Promise<void> {
  const end = Date.now() + ms;
  for (;;) {
    await w.sync();
    if (done()) return;
    if (Date.now() > end)
      throw new Error(
        `timed out: ${what}; balance ${JSON.stringify(balance(w), (_, v) => (typeof v === 'bigint' ? `${v}` : v))}`,
      );
    await new Promise((r) => setTimeout(r, 1000));
  }
}

test.concurrent('notes, a receive code paid by a transfer and a deposit address, merged into one note', async () => {
  const [bobKey, payer] = [await fresh(), await fresh()];
  const bob = await open(bobKey);
  await bob.sync();
  const zeth = bob.tokens().find((t) => t.tokenId === 1)!;

  // Bob deposits 0.2 and pays himself 0.05 of it: two notes, the payment and the change.
  await (await bob.deposit({ token: zeth, amount: (2n * ETH) / 10n })).wait();
  await until(bob, 'the deposit becomes spendable', () => balance(bob).spendable === (2n * ETH) / 10n);
  await (await bob.send({ to: bob.address, token: zeth, amount: ETH / 20n, maxFee: FEE })).wait();
  await until(bob, 'the notes are spendable', () => balance(bob).spendable === (2n * ETH) / 10n - FEE);

  // He hands out a receive code, and someone pays it 0.1 zETH by a plain transfer to its burn address, a deposit like
  // any other.
  const payerAddress = privateKeyToAccount(payer).address;
  const burnAddress = bytesToHex(decodeCode(await bob.receiveCode(zeth))!.burnAddress);
  await mined(
    client(payer).writeContract({
      address: zeth.address,
      abi: tokenAbi,
      functionName: 'wrap',
      args: [ETH / 10n, payerAddress],
      value: ETH / 10n,
    }),
  );
  await mined(
    client(payer).writeContract({
      address: zeth.address,
      abi: tokenAbi,
      functionName: 'transfer',
      args: [burnAddress, ETH / 10n],
    }),
  );
  await until(bob, 'Bob sees the code paid by a deposit', () =>
    bob.deposits().some((d) => d.amount === ETH / 10n && d.sender?.toLowerCase() === payerAddress.toLowerCase()),
  );

  // He gets a deposit address and sends 0.1 ETH and the relayer's fee to it from his account, as an exchange
  // withdrawal would; the deposit relayer takes its fee and flushes the rest into his burn address.
  const { address: depositAddress, fee: depositFee } = await bob.depositAddress(zeth);
  expect(depositFee).toBeGreaterThan(0n);
  await mined(client(bobKey).sendTransaction({ to: depositAddress, value: ETH / 10n + depositFee }));
  await until(bob, 'the deposit address is flushed', () =>
    bob.deposits().some((d) => d.amount === ETH / 10n && d.sender?.toLowerCase() === depositAddress.toLowerCase()),
  );

  // No single JoinSplit withdraws 0.3 of what he holds (a deposit and the change make 0.249), merged it would: the
  // withdrawal fails at once and asks for a consolidation, which is the app's to run. With the merge prover, he
  // merges the notes and the deposits into one note without paying anyone: one merge, one relayer fee.
  const scattered = (2n * ETH) / 10n - FEE + ETH / 10n + ETH / 10n;
  await until(bob, 'the deposits are spendable', () => balance(bob).spendable === scattered);
  await expect(bob.fees({ kind: 'withdraw', token: zeth, amount: (3n * ETH) / 10n })).rejects.toMatchObject({
    code: 'needs-consolidation',
  });
  await expect(
    bob.withdraw({ to: payerAddress, token: zeth, amount: (3n * ETH) / 10n, maxFee: FEE }),
  ).rejects.toMatchObject({ code: 'needs-consolidation' });
  if (network.mergeProver) {
    expect(await bob.fees({ kind: 'consolidate', token: zeth })).toEqual({
      relayer: FEE,
      protocol: 0n,
      protocolBps: 0,
      fee: FEE,
      steps: 1,
    });
    await (await bob.consolidate({ token: zeth, maxFee: FEE })).wait();
    await until(bob, 'the merged note is spendable', () => balance(bob).spendable === scattered - FEE);
    expect((await bob.fees({ kind: 'consolidate', token: zeth })).steps).toBe(0);
    expect(bob.deposits().map((d) => d.state)).toEqual(['spent', 'spent', 'spent']);
  }
  await until(
    bob,
    "Bob's merge shows",
    () => bob.activity().filter((a) => a.kind === 'merged').length === merged.length,
  );
  expect(kinds(bob)).toEqual(['deposited', 'deposited', 'deposited', 'received', 'sent', ...merged].sort());
  if (network.mergeProver) expect(bob.activity().find((a) => a.kind === 'merged')!.fee).toBe(FEE);
  expect(
    bob
      .activity()
      .some(
        (a) =>
          a.via && 'depositAddress' in a.via && a.via.depositAddress.toLowerCase() === depositAddress.toLowerCase(),
      ),
  ).toBe(true);
  // another device of his, from nothing, shows the same: the deposit through the deposit address too
  await sameElsewhere(bob, () => open(bobKey));
});

test.concurrent('one chosen deposit turned into a note, the other out by rage exit', async () => {
  const aliceKey = await fresh();
  const alice = await open(aliceKey);
  await alice.sync();
  const zeth = alice.tokens().find((t) => t.tokenId === 1)!;

  // Two deposits. With the prover, Alice turns the 0.1 one, chosen alone, into a note, and the other stays.
  await (await alice.deposit({ token: zeth, amount: (2n * ETH) / 10n })).wait();
  await (await alice.deposit({ token: zeth, amount: ETH / 10n })).wait();
  const final = (amount: bigint) => alice.deposits().find((d) => d.amount === amount && d.state !== 'spent');
  await until(alice, 'the two deposits are final', () => !!final((2n * ETH) / 10n) && !!final(ETH / 10n));
  const [id, chosen] = [final((2n * ETH) / 10n)!.id, final(ETH / 10n)!.id];
  expect(
    alice
      .coins()
      .filter((c) => c.kind === 'deposit')
      .map((c) => c.id)
      .sort(),
  ).toEqual([id, chosen].sort());
  if (network.mergeProver) {
    // She cancels a first merge of it while a sync takes it through its stages, once a stage is done: nothing goes to
    // the relayer, the deposit is hers to spend again, and the merge after it spends it.
    const spendable = () => alice.coins().find((c) => c.id === chosen)!.state === 'spendable';
    await until(alice, 'the chosen deposit is spendable', spendable);
    const cancelled = await alice.consolidate({ token: zeth, coins: [chosen], maxFee: FEE });
    let synced = false;
    const syncing = alice.sync().finally(() => (synced = true));
    try {
      while (!synced && (cancelled.stage === null || cancelled.stage === 'planned'))
        await new Promise((r) => setTimeout(r, 20));
      expect(['noted', 'attested', 'proving']).toContain(cancelled.stage);
      await cancelled.cancel();
    } finally {
      await syncing;
    }
    await expect(cancelled.wait()).rejects.toMatchObject({ code: 'cancelled' });
    expect(alice.operations().some((o) => o.id === cancelled.id)).toBe(false);
    await alice.sync();
    expect(alice.deposits().find((d) => d.id === chosen)!.state).not.toBe('spent');
    expect(spendable()).toBe(true);
    await (await alice.consolidate({ token: zeth, coins: [chosen], maxFee: FEE })).wait();
    expect(alice.deposits().find((d) => d.id === chosen)!.state).toBe('spent');
    expect(alice.deposits().find((d) => d.id === id)!.state).not.toBe('spent');
    expect(alice.coins().some((c) => c.kind === 'note' && c.amount === ETH / 10n - FEE)).toBe(true);
  } else {
    await expect(alice.consolidate({ token: zeth, coins: [chosen], maxFee: FEE })).rejects.toMatchObject({
      code: 'invalid',
    });
  }

  // The other leaves by rage exit: no ASP, no attester, no root, back to Alice's account as zETH.
  const zethBalance = () =>
    publicClient.readContract({
      address: zeth.address,
      abi: tokenAbi,
      functionName: 'balanceOf',
      args: [alice.address as Address],
    });
  const before = await zethBalance();
  await alice.rageExit(id);
  expect((await zethBalance()) - before).toBe((2n * ETH) / 10n);
  await alice.sync();
  expect(alice.deposits().find((d) => d.id === id)!.state).toBe('spent');
  await until(
    alice,
    "Alice's merge shows",
    () => alice.activity().filter((a) => a.kind === 'merged').length === merged.length,
  );
  expect(kinds(alice)).toEqual(['deposited', 'deposited', 'returned', ...merged].sort());
  expect(alice.activity().find((a) => a.kind === 'returned')).toMatchObject({
    id: `returned:${id}`,
    amount: (2n * ETH) / 10n,
  });
  // another device of hers, from nothing, shows the same: the rage exit, which the next sync wrote to storage
  await sameElsewhere(alice, () => open(aliceKey));
});
