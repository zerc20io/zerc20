// The CLI end to end, against the stack scripts/e2e.sh starts: each step is the built `zerc20` run as a process of its
// own, with nothing shared between two but the state it keeps on disk. Alice makes an account, is paid twice through
// a deposit address, merges the two deposits through a prover on this machine, pays Bob and withdraws; Bob's view key
// shows his account and pays nothing.

import { execFile } from 'node:child_process';
import { mkdtempSync, readFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { entropyToMnemonic } from '@scure/bip39';
import { wordlist } from '@scure/bip39/wordlists/english.js';
import { networkFromJson } from '@zerc20/wallet-sdk';
import { createPublicClient, createTestClient, createWalletClient, defineChain, http, parseEther } from 'viem';
import { generatePrivateKey, privateKeyToAccount } from 'viem/accounts';
import { expect, test } from 'vitest';

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
const testClient = createTestClient({ mode: 'anvil', chain: anvil, transport: http() });

const bin = fileURLToPath(new URL('../../dist/main.js', import.meta.url));
const home = mkdtempSync(join(tmpdir(), 'zerc20-e2e-'));

/** One command, as a script runs it: the key in the environment, no terminal to ask on. */
const run = (args: string[], key?: string) =>
  new Promise<{ code: number; stdout: string; stderr: string }>((resolve) => {
    const env = {
      ...process.env,
      ZERC20_HOME: home,
      ZERC20_NETWORK: path,
      ZERC20_NO_UPDATE_CHECK: '1',
      ...(key ? { ZERC20_KEY: key } : {}),
    };
    const child = execFile(process.execPath, [bin, ...args], { env }, (_, stdout, stderr) =>
      resolve({ code: child.exitCode ?? 1, stdout, stderr }),
    );
    child.stdin!.end();
  });

/** A command's answer as JSON; a command that fails throws what it said. */
async function json<T>(args: string[], key?: string): Promise<T> {
  const r = await run([...args, '--json'], key);
  if (r.code !== 0) throw new Error(`zerc20 ${args.join(' ')}: ${r.stderr}`);
  return JSON.parse(r.stdout) as T;
}

async function until(what: string, done: () => Promise<boolean>, ms = 300_000): Promise<void> {
  const end = Date.now() + ms;
  while (!(await done())) {
    if (Date.now() > end) throw new Error(`timed out: ${what}`);
    await new Promise((r) => setTimeout(r, 1000));
  }
}

interface Account {
  id: string;
  phrase: string;
}
interface Balances {
  id: string;
  balances: { token: string; spendable: string }[];
}
interface Paid {
  txHashes: string[];
}

const spendable = async (key: string) =>
  (await json<Balances>(['balance'], key)).balances.find((b) => b.token === 'zETH')?.spendable ?? '0';

test('an account is made, paid into, merged, paid from and watched, one command at a time', async () => {
  const alice = await json<Account>(['new']);
  const bob = await json<Account>(['new']);
  expect(alice.phrase.split(' ')).toHaveLength(24);
  expect((await json<{ id: string }>(['receive'], alice.phrase)).id).toBe(alice.id);

  // a phrase no account was made of opens nothing, rather than making one
  const stranger = await run(['balance'], entropyToMnemonic(crypto.getRandomValues(new Uint8Array(32)), wordlist));
  expect([stranger.code, stranger.stdout]).toEqual([1, '']);
  expect(stranger.stderr).toContain('has no account');

  // paid twice through one deposit address, as from an exchange: two deposits
  const payer = createWalletClient({
    account: privateKeyToAccount(generatePrivateKey()),
    chain: anvil,
    transport: http(),
  });
  await testClient.setBalance({ address: payer.account.address, value: parseEther('100') });
  const address = await json<{ address: `0x${string}`; fee: string; asset: string }>(['deposit', 'ETH'], alice.phrase);
  expect(address.asset).toBe('ETH');
  for (const value of ['0.3', '0.2']) {
    const hash = await payer.sendTransaction({
      to: address.address,
      value: parseEther(value) + parseEther(address.fee),
    });
    await publicClient.waitForTransactionReceipt({ hash });
  }
  await until('both deposits are spendable', async () => (await spendable(alice.phrase)) === '0.5');
  expect(await json<unknown[]>(['coins'], alice.phrase)).toHaveLength(2);

  // nothing is paid where no one can confirm and --yes is not given, and what would be paid is told, fee included
  const unasked = await run(['send', '0.1', 'ETH', bob.id], alice.phrase);
  expect(unasked.code).toBe(2);
  expect(unasked.stderr).toMatch(/Send 0\.1 zETH on .*, fee [\d.]+ zETH\?/);
  expect(unasked.stderr).toContain('--yes');

  // merged into one note, through the stack's prover as one on this machine: no enclave, a loopback address. Each
  // merge and payment costs the relayer's 0.001 zETH, set in scripts/dev-stack.sh
  const prover = ['--prover', network.mergeProver!.url, '--yes'];
  expect((await json<Paid>(['merge', 'ETH', ...prover], alice.phrase)).txHashes).toHaveLength(1);
  await until('the merged note is spendable', async () => (await spendable(alice.phrase)) === '0.499');
  expect(await json<unknown[]>(['coins'], alice.phrase)).toHaveLength(1);

  // Alice pays Bob by his zERC20 ID, under either name of the token
  expect((await json<Paid>(['send', '0.1', 'zETH', bob.id, '--yes'], alice.phrase)).txHashes).toHaveLength(1);

  // Bob's view key shows what his phrase shows, and pays nothing
  const { viewKey } = await json<{ viewKey: string }>(['view-key'], bob.phrase);
  await until('Bob’s view key shows the payment', async () => (await spendable(viewKey)) === '0.1');
  expect(await json<Balances>(['balance'], viewKey)).toEqual(await json<Balances>(['balance'], bob.phrase));
  const seen = await json<{ kind: string; amount: string; counterparty: string }[]>(['history'], viewKey);
  expect(seen).toMatchObject([{ kind: 'received', amount: '0.1', counterparty: alice.id }]);
  const refused = await run(['send', '0.05', 'ETH', alice.id, '--yes'], viewKey);
  expect(refused.code).toBe(1);
  expect(refused.stderr).toContain('only watches');

  // a withdrawal pays out the asset itself: the recipient holds ETH, having had none
  const out = privateKeyToAccount(generatePrivateKey()).address;
  await until('the change is spendable', async () => (await spendable(alice.phrase)) === '0.398');
  // a higher fee than --max-fee allows fails before anything is paid
  const capped = await run(['withdraw', '0.1', 'ETH', out, '--yes', '--max-fee', '0.0001'], alice.phrase);
  expect(capped.code).toBe(1);
  expect(capped.stderr).toContain('above --max-fee');
  await json<Paid>(['withdraw', '0.1', 'ETH', out, '--yes'], alice.phrase);
  expect(await publicClient.getBalance({ address: out })).toBe(parseEther('0.1'));

  const csv = (await run(['history', '--csv'], alice.phrase)).stdout.trim().split('\n');
  expect(csv[0]).toBe('time,kind,status,amount,token,chain,chainId,fee,counterparty,depositAddress,coin,tx');
  expect(
    csv
      .slice(1)
      .map((row) => row.split(',')[1])
      .sort(),
  ).toEqual(['deposited', 'deposited', 'merged', 'sent', 'withdrawn'].sort());
});
