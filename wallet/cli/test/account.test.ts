import { spawnSync } from 'node:child_process';
import { mkdtempSync, readFileSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { entropyToMnemonic } from '@scure/bip39';
import { wordlist } from '@scure/bip39/wordlists/english.js';
import { accountKey, checkNetwork } from '@zerc20/wallet-sdk';
import { privateKeyToAccount } from 'viem/accounts';
import { expect, test } from 'vitest';
import { loadNetwork, lock, parseKey } from '../src/account.js';
import { MERGE_KEYS } from '../src/mergeKeys.js';

const repo = (path: string) => readFileSync(new URL(`../../../${path}`, import.meta.url), 'utf8');

test('a recovery phrase opens the account the wallet app opens with it, however it was typed', () => {
  const seed = new Uint8Array(32).fill(7);
  const phrase = entropyToMnemonic(seed, wordlist);
  const key = parseKey(`  ${phrase.toUpperCase().replaceAll(' ', '\n ')}\n`);
  expect(key).toEqual({ kind: 'seed', seed, address: privateKeyToAccount(accountKey(seed)).address });
});

test('what is no key is refused, a phrase one word off included', () => {
  const words = entropyToMnemonic(new Uint8Array(32).fill(7), wordlist).split(' ');
  expect(() => parseKey(words.slice(1).join(' '))).toThrow('not a view key');
  expect(() => parseKey([...words.slice(0, 23), 'zoo'].join(' '))).toThrow('not a view key');
  expect(() => parseKey('zerc20view1qqqq')).toThrow('not a view key');
  expect(() => parseKey(' \n')).toThrow('no key');
});

test('a second process is kept off an account’s state, and a lock no living process holds is taken over', () => {
  const dir = mkdtempSync(join(tmpdir(), 'zerc20-lock-'));
  const file = join(dir, 'a.bin.lock');
  const dead = spawnSync(process.execPath, ['-e', '']).pid;
  // a process that is gone, none at all, and this one, whose pid a run before it had
  for (const left of [String(dead), '', String(process.pid)]) {
    writeFileSync(file, left);
    lock(join(dir, 'a.bin'));
    expect(readFileSync(file, 'utf8')).toBe(String(process.pid));
  }
  writeFileSync(file, String(process.ppid));
  expect(() => lock(join(dir, 'a.bin'))).toThrow(`process ${process.ppid}`);
  expect(readFileSync(file, 'utf8')).toBe(String(process.ppid));
});

test('the networks that ship are the deployed ones: the committed contracts and canister, behind real enclaves', () => {
  const canisters = JSON.parse(repo('storage/canister_ids.json')) as { zerc20_storage: Record<string, string> };
  for (const name of ['mainnet', 'testnet']) {
    const network = loadNetwork(name);
    expect(network.name).toBe(name);
    checkNetwork(network);
    expect(network.storage).toEqual({ host: 'https://icp-api.io', canisterId: canisters.zerc20_storage[name] });
    for (const chain of network.chains) {
      const deployed = JSON.parse(repo(`contracts/deployments/${chain.chainId}.json`)) as Record<string, string>;
      expect(chain.verifier.toLowerCase()).toBe(deployed.verifier!.toLowerCase());
      expect(chain.depositAddressFactory.toLowerCase()).toBe(deployed.depositAddressFactory!.toLowerCase());
      expect('pcr0' in chain.attesterTrust).toBe(true);
    }
    expect(network.mergeProver && 'pcr0' in network.mergeProver.trust).toBe(true);
  }
});

test('the merge keys a prover fetches are of the setup the chains’ merge verifier is generated from', () => {
  const setup = /\(setup ([^)]*)\)/.exec(repo('contracts/src/verifiers/generated/MergeNovaVerifier.sol'))?.[1];
  expect(MERGE_KEYS.setup).toBe(setup);
});
