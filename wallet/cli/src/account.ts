// The account a command works on: its key, taken from anywhere but the arguments and never written down, and its
// wallet over a state file that only the key opens.

import { existsSync, mkdirSync, readFileSync, renameSync, rmSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { text } from 'node:stream/consumers';
import { fileURLToPath } from 'node:url';
import { mnemonicToEntropy, validateMnemonic } from '@scure/bip39';
import { wordlist } from '@scure/bip39/wordlists/english.js';
import { CanisterClient } from '@zerc20/storage-sdk';
import { type Network, Wallet, accountId, accountKey, networkFromJson, viewKeyAccount } from '@zerc20/wallet-sdk';
import { type Address, hexToBytes } from 'viem';
import { privateKeyToAccount } from 'viem/accounts';
import { Failure, Usage } from './errors.js';
import { home, localCircuit } from './files.js';

/** What opens an account: a view key to watch it, or the seed its recovery phrase spells, to pay from it. */
export type Key =
  { kind: 'view'; viewKey: string; address: Address } | { kind: 'seed'; seed: Uint8Array; address: Address };

export const seedKey = (seed: Uint8Array): Extract<Key, { kind: 'seed' }> => ({
  kind: 'seed',
  seed,
  address: privateKeyToAccount(accountKey(seed)).address,
});

/** The key `input` is: the two look nothing alike, so a command takes either without being told which. */
export function parseKey(input: string): Key {
  const t = input.trim();
  const watched = viewKeyAccount(t);
  if (watched) return { kind: 'view', viewKey: t, address: watched };
  const phrase = t.toLowerCase().split(/\s+/).join(' ');
  if (phrase.split(' ').length === 24 && validateMnemonic(phrase, wordlist))
    return seedKey(mnemonicToEntropy(phrase, wordlist));
  throw new Failure(
    t
      ? 'not a view key (zerc20view1…) or a 24-word recovery phrase'
      : 'no key: give a view key or a recovery phrase in --key-file, ZERC20_KEY or standard input',
  );
}

/** Thrown where Ctrl-C answers a question. */
export class Interrupted extends Error {}

/** What is typed after `question`, with nothing of it shown. */
function hidden(question: string): Promise<string> {
  return new Promise((resolve, reject) => {
    const { stdin } = process;
    let typed = '';
    const end = (settle: () => void) => {
      stdin.off('data', read);
      stdin.setRawMode(false);
      stdin.pause();
      process.stderr.write('\n');
      settle();
    };
    const read = (chunk: string) => {
      for (const ch of chunk) {
        if (ch === '\r' || ch === '\n') return end(() => resolve(typed));
        if (ch === '\u0003') return end(() => reject(new Interrupted()));
        typed = ch === '\u007f' || ch === '\b' ? typed.slice(0, -1) : typed + ch;
      }
    };
    process.stderr.write(question);
    stdin.setRawMode(true);
    stdin.setEncoding('utf8');
    stdin.on('data', read);
    stdin.resume();
  });
}

/** The key `file` holds. */
export const keyIn = (file: string) => parseKey(readFileSync(file, 'utf8'));

/** The key a command opens its account with, from anywhere but the arguments, which a shell's history and the process
 * list would keep: a file, the environment, what is piped in, or what is asked for at the terminal. */
export async function readKey(file: string | undefined): Promise<Key> {
  if (file) return keyIn(file);
  const given = process.env.ZERC20_KEY;
  if (given) return parseKey(given);
  return parseKey(process.stdin.isTTY ? await hidden('View key or recovery phrase: ') : await text(process.stdin));
}

/** `name`'s network: one that ships with this program, pinned as the release that carries it found it, or a
 * network.json of the user's own. */
export function loadNetwork(name: string): Network {
  const file = ['mainnet', 'testnet'].includes(name)
    ? fileURLToPath(new URL(`../networks/${name}.json`, import.meta.url))
    : name;
  if (!existsSync(file)) throw new Usage(`--network ${name}: mainnet, testnet, or the path of a network.json`);
  return networkFromJson(readFileSync(file, 'utf8'));
}

const alive = (pid: number) => {
  try {
    process.kill(pid, 0);
    return true;
  } catch (e) {
    return (e as NodeJS.ErrnoException).code === 'EPERM';
  }
};

/** Keeps `path` to this process until it exits. The SDK keeps two wallets of one page apart, not two processes: a
 * second command saving over the first one's state would undo what it spent. A lock whose process is gone is taken
 * over: one that names no process, as a full disk leaves it, or this process itself, as a container gives each run
 * the pid of the last. */
export function lock(path: string): void {
  const file = `${path}.lock`;
  const read = (f: string) => {
    try {
      return readFileSync(f, 'utf8');
    } catch {
      return null;
    }
  };
  for (;;) {
    try {
      writeFileSync(file, String(process.pid), { flag: 'wx' });
      break;
    } catch (e) {
      if ((e as NodeJS.ErrnoException).code !== 'EEXIST') throw e;
    }
    const left = read(file);
    const pid = Number(left);
    if (pid > 0 && pid !== process.pid && alive(pid))
      throw new Failure(`another zerc20 command (process ${pid}) has this account open: let it end first`);
    // Moved aside under a name of this process's own before it is removed: of two commands taking it over, one finds
    // it gone, and one that moved the other's new lock instead puts it back.
    const aside = `${file}.${process.pid}`;
    try {
      renameSync(file, aside);
    } catch {
      continue;
    }
    if (read(aside) === left) rmSync(aside, { force: true });
    else renameSync(aside, file);
  }
  process.on('exit', () => rmSync(file, { force: true }));
}

/** Where `key`'s account on `network` keeps its state, whose name other files of the account's start with. */
export function stateFile(network: Network, key: Key): string {
  const dir = join(home(), network.name);
  mkdirSync(dir, { recursive: true, mode: 0o700 });
  return join(dir, `${key.address.toLowerCase()}.${key.kind === 'view' ? 'view' : 'full'}.bin`);
}

/** Opens `key`'s account on `network`. Its state, sealed by the SDK under a key of `key`'s, is all that stays on this
 * machine: without the key it tells nothing, and with it the next run reads only what is new.
 *
 * A recovery phrase whose account was never used is refused unless `create`: the SDK registers an account the first
 * time it opens, so a mistyped phrase would quietly make an empty one. `prove` fetches what a payment proves with. */
export async function openAccount(network: Network, key: Key, { create = false, prove = false } = {}): Promise<Wallet> {
  const path = stateFile(network, key);
  lock(path);
  const persist = {
    load: () => Promise.resolve(existsSync(path) ? readFileSync(path) : null),
    // whole or not at all: a crash while writing leaves the state before it
    save: (bytes: Uint8Array) => {
      writeFileSync(`${path}.tmp`, bytes, { mode: 0o600 });
      renameSync(`${path}.tmp`, path);
      return Promise.resolve();
    },
  };
  if (key.kind === 'view') return Wallet.watch({ network, viewKey: key.viewKey, persist });
  if (!create && !existsSync(path)) {
    const storage = await CanisterClient.connect(network.storage.host, network.storage.canisterId);
    if (!(await storage.registration(hexToBytes(key.address))))
      throw new Failure(
        `this recovery phrase has no account on ${network.name} (it would be ${accountId(key.address)}): ` +
          'check the phrase, or make the account with `zerc20 new`',
      );
  }
  const circuits = { ...network.circuits, joinsplit: await localCircuit(network.circuits.joinsplit, prove) };
  return Wallet.open({
    network: { ...network, circuits },
    account: privateKeyToAccount(accountKey(key.seed)),
    seed: key.seed,
    persist,
  });
}
