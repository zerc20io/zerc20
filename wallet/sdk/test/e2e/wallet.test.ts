// The wallet SDK end to end, as an app uses it, against the stack scripts/e2e.sh starts. Each test plays its own
// users on fresh accounts, side by side: Alice deposits, pays Bob privately by his address and pays herself, Bob
// withdraws to Carol, who never opened a wallet, and Alice pays a receive code of Bob's privately; Bob's view key shows
// his account, less the code's payment, on a device without his seed, which spends nothing; wallets opened with
// a function for their seed ask for it only to pay, and sync without it in between; a device starting from nothing
// finds a deposit; two devices of Bob's spend one note at once, and the late one fails and keeps its other note;
// Carol pays Alice privately from her public balance, into a burn address of Alice's, and Alice pays her back from
// her public zETH, then withdraws to a fresh address as ETH itself; another wallet of Alice's pays a receive code of
// Bob's, publicly into its burn address. Dave's deposit address names no account, and another wallet of his sends and
// pays for its refunds, to where it says. Then another device of each, starting from nothing, shows the same history.
// Consolidations are test/e2e/merge.test.ts's. Every proof is real and every contract the deployed one (SPEED=fast
// skips the root proofs).

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
import { type Balance, Wallet, WalletError, networkFromJson } from '../../src/index.js';
import { decodeViewKey, encodeViewKey } from '../../src/viewKey.js';
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
  'function balanceOf(address) view returns (uint256)',
]);

/** A new account holding 100 ETH, set rather than sent, so tests running side by side share no nonce. */
async function fresh(): Promise<Hex> {
  const key = generatePrivateKey();
  await testClient.setBalance({ address: privateKeyToAccount(key).address, value: 100n * ETH });
  return key;
}

/** A user's wallet on a device of its own, its account a key the app holds, keeping its state in memory as an app
 * would keep it in storage. With `asked`, it holds the seed only while it needs it, and `asked` counts each time it
 * asks for it, opening included. */
async function open(key: Hex, asked?: { n: number }): Promise<Wallet> {
  let saved: Uint8Array | null = null;
  const seed = Uint8Array.from(Buffer.from(keccak256(key).slice(2), 'hex'));
  return Wallet.open({
    network,
    account: privateKeyToAccount(key),
    seed: asked ? async () => (asked.n++, seed) : seed,
    persist: { load: async () => saved, save: async (b) => void (saved = b) },
  });
}

/** An account followed by its view key on a device of its own, which holds neither its seed nor its account's key. */
function watch(viewKey: string): Promise<Wallet> {
  let saved: Uint8Array | null = null;
  return Wallet.watch({ network, viewKey, persist: { load: async () => saved, save: async (b) => void (saved = b) } });
}

const balance = (w: Wallet): Balance => w.balances().find((b) => b.token.tokenId === 1)!;
const kinds = (w: Wallet) =>
  w
    .activity()
    .map((a) => a.kind)
    .sort();
const zethBalance = (zeth: Address, owner: Address) =>
  publicClient.readContract({ address: zeth, abi: tokenAbi, functionName: 'balanceOf', args: [owner] });

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

test.concurrent('deposit, pay an address privately and oneself, withdraw, pay a receive code privately', async () => {
  const [aliceKey, bobKey] = [await fresh(), await fresh()];
  const [alice, bob] = [await open(aliceKey), await open(bobKey)];
  const carol = privateKeyToAccount(generatePrivateKey()).address;
  await Promise.all([alice.sync(), bob.sync()]);
  const zeth = alice.tokens().find((t) => t.tokenId === 1)!;
  expect(zeth.symbol).toBe('zETH');

  // Alice wraps 1 ETH into a fresh burn address. It becomes spendable once final, screened and under a proved root.
  await (await alice.deposit({ token: zeth, amount: ETH })).wait();
  await until(alice, 'the deposit becomes spendable', () => balance(alice).spendable === ETH);
  expect(alice.deposits().map((d) => [d.amount, d.state])).toEqual([[ETH, 'approved']]);

  // She pays Bob 0.3 by his address: his wallet registered his key for zETH when it opened. The relayer takes its
  // fee as a public withdrawal (no protocol fee schedule here).
  const fees = await alice.fees({ kind: 'send', token: zeth, amount: (3n * ETH) / 10n });
  expect(fees).toEqual({ relayer: FEE, protocol: 0n, protocolBps: 0, fee: FEE, steps: 1 });
  // the relayer names its fee; what the user saw quoted caps it
  await expect(
    alice.send({ to: bob.address, token: zeth, amount: (3n * ETH) / 10n, maxFee: FEE - 1n }),
  ).rejects.toMatchObject({ code: 'fee-too-high' });
  await (await alice.send({ to: bob.address, token: zeth, amount: (3n * ETH) / 10n, maxFee: FEE })).wait();
  await until(bob, 'Bob sees the payment', () => balance(bob).spendable === (3n * ETH) / 10n);
  await until(alice, "Alice's change", () => balance(alice).spendable === ETH - (3n * ETH) / 10n - FEE);
  const received = bob.activity().find((a) => a.kind === 'received')!;
  expect([received.amount, received.counterparty?.toLowerCase(), received.status]).toEqual([
    (3n * ETH) / 10n,
    alice.address.toLowerCase(),
    'done',
  ]);

  // She pays herself 0.1 by her own address: the note comes back through her own inbox, in the very refresh that
  // wrote it.
  await (await alice.send({ to: alice.address, token: zeth, amount: ETH / 10n, maxFee: FEE })).wait();
  await until(
    alice,
    'Alice gets her own payment',
    () => balance(alice).spendable === ETH - (3n * ETH) / 10n - 2n * FEE,
  );
  expect(alice.activity().find((a) => a.kind === 'received')?.amount).toBe(ETH / 10n);

  // Carol never opened a wallet, so she cannot be paid privately; Bob withdraws to her publicly instead.
  await expect(alice.send({ to: carol, token: zeth, amount: 1n, maxFee: FEE })).rejects.toThrow(WalletError);
  await expect(alice.send({ to: carol, token: zeth, amount: 1n, maxFee: FEE })).rejects.toMatchObject({
    code: 'recipient-not-registered',
  });
  await (await bob.withdraw({ to: carol, token: zeth, amount: ETH / 10n, maxFee: FEE })).wait();
  expect(await zethBalance(zeth.address, carol)).toBe(ETH / 10n);
  await until(bob, "Bob's change", () => balance(bob).spendable === (3n * ETH) / 10n - ETH / 10n - FEE);

  // Bob hands out a receive code, and Alice pays it 0.05 privately, with a note owned by the code's own key.
  const code = await bob.receiveCode(zeth);
  await (await alice.send({ to: code, token: zeth, amount: ETH / 20n, maxFee: FEE })).wait();
  await until(
    bob,
    'Bob sees the code paid privately',
    () => balance(bob).spendable === (3n * ETH) / 10n - ETH / 10n - FEE + ETH / 20n,
  );

  // Bob's view key: his account as his wallet shows it, but for what reached the code, whose key only his seed derives
  const watching = await watch(bob.viewKey());
  expect(watching.readOnly).toBe(true);
  for (const refused of [
    () => watching.send({ to: alice.address, token: zeth, amount: 1n, maxFee: FEE }),
    () => watching.deposit({ token: zeth, amount: 1n }),
    () => watching.depositAddress(zeth),
    () => watching.receiveCode(zeth),
    () => watching.posKey(),
  ])
    await expect(refused()).rejects.toMatchObject({ code: 'read-only' });
  await until(
    watching,
    "Bob's view key shows his account",
    () => balance(watching).spendable === (3n * ETH) / 10n - ETH / 10n - FEE && kinds(watching).length === 2,
  );
  expect(kinds(watching)).toEqual(['received', 'withdrawn']);
  await watching.close();
  // a nullifying key that is not Bob's would show his spent notes as unspent: his registration refuses it
  const { view } = decodeViewKey(bob.viewKey())!;
  const { owner } = decodeViewKey(alice.viewKey())!;
  await expect(watch(encodeViewKey(view, owner))).rejects.toMatchObject({ code: 'invalid' });

  expect(kinds(alice)).toEqual(['deposited', 'received', 'sent', 'sent', 'sent'].sort());
  expect(kinds(bob)).toEqual(['received', 'received', 'withdrawn'].sort());
  const toCode = alice.activity().find((a) => a.via && 'code' in a.via)!;
  expect([toCode.kind, toCode.amount, toCode.fee]).toEqual(['sent', ETH / 20n, FEE]);
  // another device of each, from nothing, shows the same: the payments, the code, the withdrawal, their fees
  await Promise.all([sameElsewhere(alice, () => open(aliceKey)), sameElsewhere(bob, () => open(bobKey))]);
});

/** Until the wallet lets its seed go: a sync settles before it records a burn address ahead and lets the seed go, so a
 * second one, with nothing behind it, does so once the first is through, at once. */
async function idle(w: Wallet): Promise<void> {
  await w.sync();
  await w.sync();
  await new Promise((r) => setTimeout(r, 1000));
}

test.concurrent('opened with a function for its seed, a wallet asks for it to pay and syncs without it', async () => {
  const [aliceKey, bobKey] = [await fresh(), await fresh()];
  const [asked, bobAsked] = [{ n: 0 }, { n: 0 }];
  const [alice, bob] = [await open(aliceKey, asked), await open(bobKey, bobAsked)];
  expect([asked.n, bobAsked.n]).toEqual([1, 1]); // to open
  await Promise.all([idle(alice), idle(bob)]);
  const zeth = alice.tokens().find((t) => t.tokenId === 1)!;

  // her first burn address, from the burn key, takes no seed
  await (await alice.deposit({ token: zeth, amount: ETH / 2n })).wait();
  await until(alice, 'the deposit becomes spendable', () => balance(alice).spendable === ETH / 2n);
  expect(asked.n).toBe(1);
  // asked to pay, and let go once the payment is final: until then a reorg may have it proved again, which signs
  await (await alice.send({ to: bob.address, token: zeth, amount: ETH / 10n, maxFee: FEE })).wait({ until: 'final' });
  expect(asked.n).toBe(2);
  // Bob, without his seed since his first sync, finds the payment
  await until(bob, 'Bob sees the payment', () => balance(bob).spendable === ETH / 10n);
  expect(bobAsked.n).toBe(1);
  // his first receive code's owner was derived ahead as he opened: no seed; it then finds its payment
  const code = await bob.receiveCode(zeth);
  expect(bobAsked.n).toBe(1);
  // her change pays once a proved root covers it, which may come after final
  await until(alice, 'her change is spendable', () => balance(alice).spendable === ETH / 2n - ETH / 10n - FEE);
  await (await alice.send({ to: code, token: zeth, amount: ETH / 20n, maxFee: FEE })).wait();
  await until(bob, 'Bob sees the code paid', () => balance(bob).spendable === ETH / 10n + ETH / 20n);
  await idle(bob);
  await (await bob.withdraw({ to: bob.address, token: zeth, amount: ETH / 20n, maxFee: FEE })).wait();
  expect([asked.n, bobAsked.n]).toEqual([3, 2]);
});

test.concurrent('a device starting from nothing finds a deposit, and hands out no burn address again', async () => {
  const key = await fresh();
  const alice = await open(key);
  await alice.sync();
  const zeth = alice.tokens().find((t) => t.tokenId === 1)!;

  // A deposit Alice leaves alone, then a device of hers starting from nothing: it finds the deposit from the seed,
  // storage and the chain, and hands out no burn address again.
  await (await alice.deposit({ token: zeth, amount: ETH / 20n })).wait();
  await until(alice, 'the deposit is final', () =>
    alice.deposits().some((d) => d.amount === ETH / 20n && d.state !== 'spent'),
  );
  const handedOut = new Set(alice.deposits().map((d) => d.address));
  await alice.close();
  const restored = await open(key);
  await until(restored, 'a fresh device finds the deposit', () =>
    restored.deposits().some((d) => d.amount === ETH / 20n && d.state !== 'spent'),
  );
  expect(restored.deposits().some((d) => d.managed)).toBe(false);
  await (await restored.deposit({ token: zeth, amount: ETH / 100n })).wait();
  await until(restored, 'its own deposit is found', () => restored.deposits().some((d) => d.amount === ETH / 100n));
  expect(handedOut.has(restored.deposits().find((d) => d.amount === ETH / 100n)!.address)).toBe(false);
  await restored.close();
});

/** `open` on a machine of its own, whose Web Locks this process does not share: another device of the same wallet,
 * open at the same time. The prover's thread count stays this machine's. */
async function openElsewhere(key: Hex): Promise<Wallet> {
  const real = Object.getOwnPropertyDescriptor(globalThis, 'navigator')!;
  const { hardwareConcurrency } = globalThis.navigator;
  Object.defineProperty(globalThis, 'navigator', { value: { hardwareConcurrency }, configurable: true });
  try {
    return await open(key);
  } finally {
    Object.defineProperty(globalThis, 'navigator', real);
  }
}

test.concurrent(
  'two devices of one wallet spend a note at once: the late one fails, and keeps its other note',
  async () => {
    const [aliceKey, bobKey] = [await fresh(), await fresh()];
    const alice = await open(aliceKey);
    const [phone, laptop] = [await open(bobKey), await openElsewhere(bobKey)];
    await Promise.all([alice.sync(), phone.sync(), laptop.sync()]);
    const zeth = alice.tokens().find((t) => t.tokenId === 1)!;

    // Bob holds two notes, of 0.1 and 0.3, on both devices
    await (await alice.deposit({ token: zeth, amount: ETH })).wait();
    await until(alice, 'the deposit becomes spendable', () => balance(alice).spendable === ETH);
    await (await alice.send({ to: phone.address, token: zeth, amount: ETH / 10n, maxFee: FEE })).wait();
    await until(alice, "Alice's change", () => balance(alice).spendable === ETH - ETH / 10n - FEE);
    await (await alice.send({ to: phone.address, token: zeth, amount: (3n * ETH) / 10n, maxFee: FEE })).wait();
    const both = (4n * ETH) / 10n;
    await until(phone, 'the phone holds both notes', () => balance(phone).spendable === both);
    await until(laptop, 'the laptop holds both notes', () => balance(laptop).spendable === both);

    // The laptop takes both notes for 0.35; the phone, which does not see the laptop's locks, pays 0.05 with the 0.1
    // note, and lands first. The laptop's JoinSplit then reverts on that note, and its change never comes: it paid
    // nothing, and the 0.3 note is spendable there again, as on the phone
    const late = await laptop.send({ to: alice.address, token: zeth, amount: (35n * ETH) / 100n, maxFee: FEE });
    await (await phone.send({ to: alice.address, token: zeth, amount: ETH / 20n, maxFee: FEE })).wait();
    await expect(late.wait()).rejects.toMatchObject({ code: 'spent-elsewhere' });
    const left = (3n * ETH) / 10n + ETH / 10n - ETH / 20n - FEE;
    await until(phone, "the phone's change", () => balance(phone).spendable === left);
    await until(laptop, 'the laptop holds what the phone does', () => balance(laptop).spendable === left);
    await Promise.all([alice.close(), phone.close(), laptop.close()]);
  },
);

test.concurrent(
  "a private send: from the public balance into a burn address of the recipient's, told in storage",
  async () => {
    const [aliceKey, carolKey] = [await fresh(), await fresh()];
    const [carol, alice] = [await open(carolKey), await open(aliceKey)];
    await Promise.all([carol.sync(), alice.sync()]); // Carol's first: she registers, and can now write to storage
    const zeth = carol.tokens().find((t) => t.tokenId === 1)!;

    // An address that never opened a wallet has no public key to find a burn address under.
    await expect(
      carol.deposit({ token: zeth, amount: 1n, to: '0x000000000000000000000000000000000000dEaD' }),
    ).rejects.toMatchObject({
      code: 'recipient-not-registered',
    });

    // Carol wraps 0.1 ETH from her account into a burn address under Alice's public key, with a salt she tells Alice
    // in storage first. Alice's wallet watches it as a deposit of her own: received from Carol, then spendable.
    const op = await carol.deposit({ token: zeth, amount: ETH / 10n, to: alice.address });
    expect(op.to).toBe(alice.address);
    await op.wait();
    const fromCarol = (a: { counterparty: Address | null }) =>
      a.counterparty?.toLowerCase() === carol.address.toLowerCase();
    await until(alice, 'Alice finds the private send', () =>
      alice.activity().some((a) => a.kind === 'received' && a.amount === ETH / 10n && fromCarol(a)),
    );
    await until(alice, 'it becomes spendable', () =>
      alice
        .coins()
        .some(
          (c) =>
            c.kind === 'deposit' &&
            c.amount === ETH / 10n &&
            c.from?.toLowerCase() === carol.address.toLowerCase() &&
            c.state === 'spendable',
        ),
    );
    // from storage once the transfer is found, as on every device of hers: its transaction is found from where it landed
    const toAlice = (a: { kind: string; id: string }) => a.kind === 'sent' && a.id.startsWith('sent:');
    await until(carol, 'Carol finds her send', () => carol.activity().some(toAlice));
    const sent = carol.activity().find(toAlice)!;
    expect([sent.amount, sent.counterparty?.toLowerCase(), sent.status]).toEqual([
      ETH / 10n,
      alice.address.toLowerCase(),
      'done',
    ]);
    expect((await carol.transaction(sent))?.hash).toBe(op.txHashes[0]);
    // on chain a plain transfer to an address that names no one: to Alice one of her own, to Carol a payment to Alice
    const burn = alice.deposits().find((d) => d.sender?.toLowerCase() === carol.address.toLowerCase())!.address;
    expect(alice.burnAddressOf(zeth.chainId, burn)).toEqual({ kind: 'deposit' });
    expect(carol.burnAddressOf(zeth.chainId, burn)).toEqual({ kind: 'payment', to: alice.address.toLowerCase() });
    expect(carol.burnAddressOf(zeth.chainId, alice.address)).toBeNull();

    // Alice pays Carol 0.05 back from zETH she holds publicly (wrapped in her own account), as it is: a transfer, no
    // wrap.
    const own = createWalletClient({ account: privateKeyToAccount(aliceKey), chain: anvil, transport: http() });
    await publicClient.waitForTransactionReceipt({
      hash: await own.writeContract({
        address: zeth.address,
        abi: tokenAbi,
        functionName: 'wrap',
        args: [ETH / 20n, alice.address],
        value: ETH / 20n,
      }),
    });
    await (await alice.deposit({ token: zeth, amount: ETH / 20n, to: carol.address, wrapped: true })).wait();
    expect(await zethBalance(zeth.address, alice.address)).toBe(0n);
    const fromAlice = (a: { counterparty: Address | null }) =>
      a.counterparty?.toLowerCase() === alice.address.toLowerCase();
    await until(carol, 'Carol finds it', () =>
      carol.activity().some((a) => a.kind === 'received' && a.amount === ETH / 20n && fromAlice(a)),
    );

    // Alice withdraws 0.05 to a fresh address as ETH itself, which needs no gas to unwrap zETH with.
    const to = privateKeyToAccount(generatePrivateKey()).address;
    await (await alice.withdraw({ to, token: zeth, amount: ETH / 20n, maxFee: FEE, unwrap: true })).wait();
    expect([await publicClient.getBalance({ address: to }), await zethBalance(zeth.address, to)]).toEqual([
      ETH / 20n,
      0n,
    ]);
    // another device of each, from nothing, shows the same: the private sends both ways, and the withdrawal as ETH
    await Promise.all([sameElsewhere(carol, () => open(carolKey)), sameElsewhere(alice, () => open(aliceKey))]);
  },
);

test.concurrent('another wallet pays a receive code publicly, into its burn address, as a deposit', async () => {
  const [aliceKey, bobKey, otherKey] = [await fresh(), await fresh(), await fresh()];
  const [alice, bob] = [await open(aliceKey), await open(bobKey)];
  await Promise.all([alice.sync(), bob.sync()]);
  const zeth = alice.tokens().find((t) => t.tokenId === 1)!;
  const other = createWalletClient({ account: privateKeyToAccount(otherKey), chain: anvil, transport: http() });

  const code = await bob.receiveCode(zeth);
  const op = await alice.deposit({ token: zeth, amount: ETH / 20n, to: code, from: other });
  await op.wait();
  expect(await zethBalance(zeth.address, bytesToHex(decodeCode(code)!.burnAddress))).toBe(ETH / 20n);
  const sent = alice.activity().find((a) => a.id === op.id)!;
  expect([sent.kind, sent.amount, sent.via, sent.fee]).toEqual(['sent', ETH / 20n, { code }, null]);
  // Bob watches the code's burn address as one of his own: a deposit from that wallet
  await until(bob, 'Bob finds the payment', () =>
    bob
      .activity()
      .some((a) => a.amount === ETH / 20n && a.counterparty?.toLowerCase() === other.account.address.toLowerCase()),
  );
  await expect(
    alice.deposit({ token: { ...zeth, tokenId: 2 }, amount: 1n, to: code, from: other }),
  ).rejects.toMatchObject({ code: 'invalid' });
  await Promise.all([alice.close(), bob.close()]);
});

test.concurrent(
  'a deposit address names no account; its refunds, sent and paid for by another wallet, go where that wallet says',
  async () => {
    const [daveKey, payerKey, gasKey] = [generatePrivateKey(), await fresh(), await fresh()];
    const dave = await open(daveKey);
    await dave.sync();
    const [zeth, zusdc] = [1, 2].map((id) => dave.tokens().find((t) => t.tokenId === id)!);
    const payer = createWalletClient({ account: privateKeyToAccount(payerKey), chain: anvil, transport: http() });
    // another wallet of Dave's, which pays the gas: his account holds none, as a passkey account's need not
    const gas = createWalletClient({ account: privateKeyToAccount(gasKey), chain: anvil, transport: http() });
    const out = privateKeyToAccount(generatePrivateKey()).address;

    // 0.1 ETH paid to a deposit address of Dave's, as from an exchange; the relayer flushes it into his burn address
    const { address: depositAddress, fee } = await dave.depositAddress(zeth);
    await publicClient.waitForTransactionReceipt({
      hash: await payer.sendTransaction({ to: depositAddress, value: ETH / 10n + fee }),
    });
    const through = () => dave.coins().find((c) => c.via?.depositAddress === depositAddress);
    await until(dave, 'the deposit address is flushed', () => !!through());
    // the clone's code holds its args, the refund signer among them: none of it is Dave's account
    const code = await publicClient.getCode({ address: depositAddress });
    expect(code!.toLowerCase()).not.toContain(dave.address.slice(2).toLowerCase());

    // watched again at the fee it was handed out with, and dated anew in storage, for every device
    const [handedOut] = dave.depositAddresses();
    expect(await dave.rewatchDepositAddress(depositAddress)).toEqual({ address: depositAddress, fee });
    await dave.sync();
    const [rewatched, ...more] = dave.depositAddresses();
    expect(more).toEqual([]);
    expect(rewatched.at.getTime()).toBeGreaterThan(handedOut.at.getTime());

    // its receipt holds all it was registered with: Dave's own flush, without the relayer, finds the same address, now
    // empty, rather than refusing an address its receipt does not make
    await expect(dave.flushDepositAddress(depositAddress, { from: gas })).rejects.toMatchObject({
      code: 'insufficient-funds',
    });

    // USDC sent there by mistake, which a zETH address cannot wrap, goes where Dave says
    const usdc = zusdc.underlying;
    const erc20 = parseAbi([
      'function mint(address to, uint256 amount)',
      'function balanceOf(address) view returns (uint256)',
    ]);
    await publicClient.waitForTransactionReceipt({
      hash: await payer.writeContract({ address: usdc, abi: erc20, functionName: 'mint', args: [depositAddress, 5n] }),
    });
    await dave.refundDepositAddress(depositAddress, usdc, { from: gas, to: out });
    expect(await publicClient.readContract({ address: usdc, abi: erc20, functionName: 'balanceOf', args: [out] })).toBe(
      5n,
    );

    // the deposit leaves by rage exit, in one transaction from the other wallet, to where it says
    await dave.rageExit(through()!.id, { from: gas, to: out });
    expect(await zethBalance(zeth.address, out)).toBe(ETH / 10n);
    expect(await zethBalance(zeth.address, depositAddress)).toBe(0n);
    expect(await publicClient.getBalance({ address: dave.address })).toBe(0n);
    expect(dave.activity().find((a) => a.kind === 'returned')).toMatchObject({
      amount: ETH / 10n,
      counterparty: out.toLowerCase(),
    });
    await dave.close();
  },
);
