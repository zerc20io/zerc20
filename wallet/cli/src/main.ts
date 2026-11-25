#!/usr/bin/env node
// zerc20: a zERC20 account from the terminal.

import { createRequire } from 'node:module';
import { parseArgs } from 'node:util';
import { WalletError } from '@zerc20/wallet-sdk';
import { Interrupted } from './account.js';
import * as commands from './commands.js';
import { Usage, told } from './errors.js';
import { until } from './format.js';
import { proverStart } from './prover.js';
import { installSkill, skillText } from './skill.js';
import { notices, update } from './update.js';

const HELP = `zerc20: a zERC20 account from the terminal

Usage: zerc20 <command> [options]

Look
  balance                           what the account holds, by token and chain
  history [--csv] [--tx]            what it received, paid, deposited and withdrew
  coins                             its unspent notes and deposits, which a merge joins

Receive
  receive                           its zERC20 ID, which any account pays privately
  receive <token>                   a receive code for one token
  deposit <token>                   an address that takes the token from anywhere

Pay
  send <amount> <token> <to>        privately, to a zERC20 ID or a receive code
  withdraw <amount> <token> <0x…>   in public, to any address
  merge <token>                     join the token's coins into one note

Account
  new                               make an account, and print its recovery phrase once
  view-key                          the key that shows the account and spends nothing

Run
  prover start                      a merge prover on this machine, for --prover local

Agents
  install-skill                     teach the coding agents on this machine to use zerc20
  skill                             print that skill

Update
  update                            install the newest release with npm, and its skill where one is installed

The key
  A view key (zerc20view1…) to look, or the 24-word recovery phrase to pay. It is read
  from --key-file, else ZERC20_KEY, else standard input, else asked for unseen. It is
  never an argument, which a shell keeps, and nothing of it is written to disk.

Options
  --network <mainnet|testnet|file>  default mainnet, or ZERC20_NETWORK
  --chain <name|id>                 where a token is on several chains
  --key-file <file>
  --json                            the answer as JSON
  --yes                             pay without being asked
  --max-fee <amount>                fail on a higher fee
  --wrapped                         withdraw: pay out the zERC20 token, not the asset under it
  --tx                              history: look up each transaction (slower)
  --csv                             history: as CSV
  --prover <local|url>              merge: prove on this machine, or ZERC20_PROVER
  --port <port>                     prover start: default 3006
  --version

Amounts are in the token's units (10.5), or max. A token goes by its name or its asset's:
zUSDC and USDC are the one private balance.

Once a day a command asks npm whether a newer release is out, and says so if one is.
ZERC20_NO_UPDATE_CHECK=1 asks nothing.`;

const COMMANDS: Record<string, (flags: commands.Flags, args: string[]) => Promise<void>> = {
  balance: commands.balance,
  history: commands.history,
  coins: commands.coins,
  receive: commands.receive,
  deposit: commands.deposit,
  send: commands.send,
  withdraw: commands.withdraw,
  merge: commands.merge,
  new: commands.create,
  'view-key': commands.viewKey,
};

/** What to do about an error a wallet names by code, where its message does not say. */
function hint(e: WalletError): string | null {
  switch (e.code) {
    case 'needs-consolidation':
      return 'Its coins are too scattered for one payment: `zerc20 merge <token>` first.';
    case 'funds-settling':
      return e.waitsOn?.readyBy ? `Enough of it should be spendable in ${until(e.waitsOn.readyBy)}.` : null;
    case 'recipient-not-registered':
      return 'A public address is paid with `zerc20 withdraw`.';
    case 'attester-unverified':
      return 'Where the network has moved on since this release: zerc20 update';
    default:
      return null;
  }
}

const { version } = createRequire(import.meta.url)('../package.json') as { version: string };

/** What an account's command ends with, once its own answer is out: asked for while the command runs. */
let ending: Promise<string[]> | undefined;

async function main(): Promise<void> {
  const { values, positionals } = parseArgs({
    allowPositionals: true,
    options: {
      network: { type: 'string', default: process.env.ZERC20_NETWORK ?? 'mainnet' },
      chain: { type: 'string' },
      'key-file': { type: 'string' },
      'max-fee': { type: 'string' },
      prover: { type: 'string', default: process.env.ZERC20_PROVER },
      port: { type: 'string', default: '3006' },
      json: { type: 'boolean', default: false },
      yes: { type: 'boolean', default: false },
      wrapped: { type: 'boolean', default: false },
      csv: { type: 'boolean', default: false },
      tx: { type: 'boolean', default: false },
      help: { type: 'boolean', short: 'h', default: false },
      version: { type: 'boolean', default: false },
    },
  });
  const [name, ...args] = positionals;
  if (values.version) return void console.log(version);
  if (values.help || !name) return void console.log(HELP);
  if (name === 'prover') {
    if (args[0] !== 'start') throw new Usage('zerc20 prover start [--port <port>]');
    return proverStart(values.port, commands.whenInterrupted);
  }
  if (name === 'skill') return void process.stdout.write(skillText());
  if (name === 'install-skill') {
    const files = installSkill();
    console.error('An agent that is running reads it once started again.');
    return void console.log(values.json ? JSON.stringify(files, null, 2) : files.join('\n'));
  }
  if (name === 'update') return update();
  const command = COMMANDS[name];
  if (!command) throw new Usage(`no command ${name}`);
  ending = notices(version);
  await command(values, args);
}

for (const signal of ['SIGINT', 'SIGTERM', 'SIGHUP'] as const) process.on(signal, commands.onSignal);

try {
  await main();
} catch (e) {
  // parseArgs names its errors by a string code; another library's code may be an object that cannot be read as one
  const code = (e as { code?: unknown } | null)?.code;
  if (e instanceof Interrupted) process.exitCode = 130;
  else if (e instanceof Usage || (typeof code === 'string' && code.startsWith('ERR_PARSE_ARGS'))) {
    // parseArgs goes on to explain positionals that start with a dash
    console.error(`${(e as Error).message.split('. ')[0]}\nzerc20 --help shows every command.`);
    process.exitCode = 2;
  } else {
    // the message, and what caused it where a server out of reach did; whole where ZERC20_DEBUG asks, for a defect
    if (process.env.ZERC20_DEBUG || !(e instanceof Error)) console.error(e);
    else console.error(told(e));
    const more = e instanceof WalletError ? hint(e) : null;
    if (more) console.error(more);
    process.exitCode = 1;
  }
}
for (const line of (await ending) ?? []) console.error(line);
await commands.close();
// a prover's worker threads would keep the process
process.exit();
