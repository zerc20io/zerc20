// The commands. What a command answers goes to standard output, alone, so that it pipes; what it is doing, asks or
// warns of goes to standard error.

import { existsSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { createInterface } from 'node:readline/promises';
import { entropyToMnemonic } from '@scure/bip39';
import { wordlist } from '@scure/bip39/wordlists/english.js';
import {
  type Activity,
  type FeeQuote,
  type Network,
  type Operation,
  type Token,
  type Wallet,
  WalletError,
  accountId,
} from '@zerc20/wallet-sdk';
import { type Address, isAddress } from 'viem';
import { type Key, keyIn, loadNetwork, openAccount, readKey, seedKey, stateFile } from './account.js';
import { Failure, Usage, told } from './errors.js';
import {
  amount,
  chainName,
  chainNamed,
  csv,
  minute,
  parseAmount,
  short,
  table,
  tokensNamed,
  underlyingSymbol,
  until,
} from './format.js';

export interface Flags {
  network: string;
  chain?: string;
  'key-file'?: string;
  'max-fee'?: string;
  prover?: string;
  json: boolean;
  yes: boolean;
  wrapped: boolean;
  csv: boolean;
  tx: boolean;
}

/** Where a merge prover on this machine listens, unless told otherwise. */
export const LOCAL_PROVER = 'http://127.0.0.1:3006';

const say = (line: string) => process.stderr.write(`${line}\n`);

/** A command's answer: `data` as JSON where a program reads it, `human` otherwise. */
const answer = (flags: Flags, human: string, data: unknown) =>
  process.stdout.write(`${flags.json ? JSON.stringify(data, null, 2) : human}\n`);

const quit = () => process.exit(130);
/** What Ctrl-C, or a terminal that closes, does now. */
let interrupt: () => void = quit;
export const onSignal = () => interrupt();
export const whenInterrupted = (f: () => void) => void (interrupt = f);

/** The wallet a command opened, for `close`. */
let opened: Wallet | undefined;

/** Lets the wallet go once a command is done: a burn address being recorded ahead stops, rather than being cut off by
 * the exit. It is not waited on for long, as nothing of the command's is left in it. */
export const close = () =>
  Promise.race([opened?.close().catch(() => {}), new Promise((r) => setTimeout(r, 3000).unref())]);

/** `network` with its merges proved on this machine, by the prover at `url`. */
const provedHere = (network: Network, url: string): Network => ({
  ...network,
  mergeProver: { url, trust: { local: true } },
});

/** The network a command works on, with `--prover` its merges proved on this machine. */
function networkOf(flags: Flags): Network {
  const network = loadNetwork(flags.network);
  return flags.prover ? provedHere(network, flags.prover === 'local' ? LOCAL_PROVER : flags.prover) : network;
}

/** Where an account notes the prover of this machine that its merge under way is proved by. Every command's sync
 * moves that merge on, and one that names no prover would hand the rest of it to the network's, which the merge's
 * owner chose not to show it to. */
const proverNote = (network: Network, key: Key) => `${stateFile(network, key)}.prover`;

interface Session {
  flags: Flags;
  network: Network;
  key: Key;
  wallet: Wallet;
}

const KIND = { send: 'payment', withdraw: 'withdrawal', consolidate: 'merge', deposit: 'deposit' } as const;

/** Opens the account of the key given. `seed` is for what a view key cannot do. An operation an earlier run left under
 * way is named, as this run's syncs move it on: nothing is paid without a line saying so. */
async function open(flags: Flags, need: 'any' | 'seed', prove = false): Promise<Session> {
  let network = networkOf(flags);
  const key = await readKey(flags['key-file']);
  if (need === 'seed' && key.kind === 'view')
    throw new Failure('a view key only watches its account: this takes the recovery phrase');
  const note = proverNote(network, key);
  if (!flags.prover && existsSync(note)) network = provedHere(network, readFileSync(note, 'utf8'));
  const wallet = (opened = await openAccount(network, key, { prove }));
  if (!wallet.operations().some((op) => op.kind === 'consolidate' && op.status === 'pending'))
    rmSync(note, { force: true });
  for (const op of wallet.operations()) {
    if (op.status !== 'pending') continue;
    const [what, chain] = [KIND[op.kind], chainName(op.chainId)];
    // in a block, an operation is only watched until it is final
    if (op.txHashes.length > 0 && op.kind !== 'consolidate')
      say(`An earlier ${what} on ${chain} is in a block, not final yet.`);
    else say(`Going on with a ${what} on ${chain} started earlier.`);
  }
  return { flags, network, key, wallet };
}

/** Catches up with the chains. One that cannot be read holds back only its own: the rest is still shown, with a
 * warning, and with `whole` a status that says the answer is not all of it. What keeps an earlier operation from
 * going on is said too, as nothing else of this command would show it. */
async function sync(s: Session, whole: boolean): Promise<void> {
  try {
    await s.wallet.sync();
  } catch (e) {
    say(`Not all of it could be read: ${e instanceof Error ? told(e) : String(e)}`);
    if (whole) process.exitCode = 1;
  }
  for (const op of s.wallet.operations()) {
    if (op.status === 'pending' && op.retrying)
      say(`The ${KIND[op.kind]} on ${chainName(op.chainId)} is held up: ${op.retrying.message}`);
  }
}

const spendable = (s: Session, token: Token) => s.wallet.balances().find((b) => b.token === token)?.spendable ?? 0n;

/** The token `symbol` names. On several chains with no `--chain`, the one that holds `need` of it spendable, if only
 * one does: a payment names its chain by where the funds are. */
function tokenOf(s: Session, symbol: string | undefined, need?: (t: Token) => bigint): Token {
  if (!symbol) throw new Usage('name a token');
  const chain = s.flags.chain ? chainNamed(s.network, s.flags.chain) : undefined;
  const named = tokensNamed(s.network, s.wallet.tokens(), symbol, chain);
  if (named.length === 0) {
    const known = [...new Set(s.wallet.tokens().map((t) => t.symbol))].join(', ');
    throw new Failure(`no token ${symbol}${chain ? ` on ${chainName(chain.chainId)}` : ''}: there is ${known}`);
  }
  if (named.length === 1) return named[0];
  const holding = need ? named.filter((t) => spendable(s, t) >= need(t)) : [];
  if (holding.length === 1) return holding[0];
  const rows = named.map((t) => [`  ${chainName(t.chainId)}`, `${amount(spendable(s, t), t)} spendable`]);
  throw new Usage(`${symbol} is on several chains: name one with --chain\n${table(['', ''], rows).trimStart()}`);
}

/** Asks before anything is paid. Where no one can answer, only `--yes` pays: a script never pays by accident. The
 * question is still shown there, as it tells a program what it would pay, fee included, before it passes `--yes`. */
async function confirm(flags: Flags, question: string): Promise<void> {
  if (flags.yes) return;
  if (!process.stdin.isTTY) {
    say(question);
    throw new Usage('no terminal to confirm on: pass --yes to pay without being asked');
  }
  const rl = createInterface({ input: process.stdin, output: process.stderr });
  // a terminal's Ctrl-C reaches the question, not the process
  rl.on('SIGINT', onSignal);
  const reply = await rl.question(`${question} [y/N] `);
  rl.close();
  if (!/^y(es)?$/i.test(reply.trim())) throw new Failure('Nothing was paid.');
}

/** The most the fees may come to: the quote just shown, or `--max-fee`, which a higher quote fails. */
function feeCap(flags: Flags, token: Token, quote: FeeQuote): bigint {
  if (!flags['max-fee']) return quote.fee;
  const cap = parseAmount(flags['max-fee'], token.decimals);
  if (quote.fee > cap) throw new Failure(`the fee is ${amount(quote.fee, token)} ${token.symbol}, above --max-fee`);
  return cap;
}

/** What an operation is waiting on, from the stage it reached last. */
function doing(op: Operation): string {
  if (op.kind === 'consolidate') {
    const merge = {
      planned: 'Writing its note…',
      noted: 'Asking the attester…',
      attested: 'Sending it to the merge prover…',
      proving: 'The merge prover is proving it: minutes…',
      proved: 'Relaying…',
      relayed: 'Waiting for its block…',
    };
    return op.stage ? merge[op.stage] : 'Waiting for a proved root over the last merge…';
  }
  const payment = {
    planned: 'Writing its notes…',
    noted: 'Proving…',
    proved: 'Asking the attester…',
    attested: 'Relaying…',
    proving: '',
    relayed: 'Waiting for its block…',
  };
  return op.stage ? payment[op.stage] : '';
}

/** Waits until `op` is in a block, saying what it waits on. Ctrl-C cancels it while it has paid nothing and asked the
 * relayer nothing; past that it can only finish, now or the next time the account is opened. */
async function follow(flags: Flags, op: Operation): Promise<void> {
  let told = '';
  const tell = () => {
    const now = op.retrying ? `Trying again: ${op.retrying.message}` : doing(op);
    if (now && now !== told) say((told = now));
  };
  const timer = setInterval(tell, 300);
  interrupt = () => {
    interrupt = quit;
    const left = `The ${KIND[op.kind]} is under way: it goes on whenever this account is opened.`;
    if (!op.cancellable) {
      say(left);
      return quit();
    }
    op.cancel()
      .then(
        () => say('Cancelled: nothing was paid.'),
        () => say(left),
      )
      .finally(quit);
  };
  try {
    await op.wait();
  } finally {
    clearInterval(timer);
    interrupt = quit;
  }
  say('In a block. What it left the account is spendable again in some minutes, under a proved root.');
  answer(flags, op.txHashes.join('\n'), { kind: KIND[op.kind], chainId: String(op.chainId), txHashes: op.txHashes });
}

const NOT_YET = {
  incoming: 'arriving',
  'awaiting-root': 'settling',
  'roots-halted': 'halted',
  screening: 'screening',
} as const;

export async function balance(flags: Flags): Promise<void> {
  const s = await open(flags, 'any');
  await sync(s, true);
  const held = s.wallet.balances().filter((b) => b.spendable > 0n || b.pending.length > 0 || b.blocked > 0n);
  const id = accountId(s.wallet.address);
  const rows = held.map((b) => {
    const waiting = new Map<string, bigint>();
    for (const p of b.pending) waiting.set(NOT_YET[p.reason], (waiting.get(NOT_YET[p.reason]) ?? 0n) + p.amount);
    if (b.blocked > 0n) waiting.set('blocked', b.blocked);
    const notYet = [...waiting].map(([why, v]) => `${amount(v, b.token)} ${why}`).join(', ');
    return [b.token.symbol, chainName(b.token.chainId), amount(b.spendable, b.token), notYet];
  });
  const nothing =
    s.key.kind === 'seed' ? 'Nothing yet: `zerc20 deposit <token>` gives an address to pay in.' : 'Nothing yet.';
  answer(
    flags,
    `${id}  ${s.network.name}\n\n${rows.length ? table(['TOKEN', 'CHAIN', 'SPENDABLE', 'NOT YET'], rows, [2]) : nothing}`,
    {
      id,
      address: s.wallet.address,
      network: s.network.name,
      balances: held.map((b) => ({
        token: b.token.symbol,
        chain: chainName(b.token.chainId),
        chainId: String(b.token.chainId),
        spendable: amount(b.spendable, b.token),
        pending: b.pending.map((p) => ({ amount: amount(p.amount, b.token), reason: p.reason })),
        blocked: amount(b.blocked, b.token),
      })),
    },
  );
}

/** `f` over `items`, a few at a time. */
async function each<T, R>(items: T[], f: (item: T) => Promise<R>): Promise<R[]> {
  const out = new Array<R>(items.length);
  let next = 0;
  const worker = async () => {
    while (next < items.length) {
      const i = next++;
      out[i] = await f(items[i]);
    }
  };
  await Promise.all(Array.from({ length: 4 }, worker));
  return out;
}

/** Whom an activity was with, as its owner would name them: an account by its zERC20 ID, anyone else by address. */
function counterparty(a: Activity): string {
  if (a.via && 'code' in a.via) return a.via.code;
  if (!a.counterparty) return '';
  return a.kind === 'sent' || (a.kind === 'received' && !a.burnAddress) ? accountId(a.counterparty) : a.counterparty;
}

/** What `history` tells of each activity, as a CSV's columns. */
const FIELDS = [
  'time',
  'kind',
  'status',
  'amount',
  'token',
  'chain',
  'chainId',
  'fee',
  'counterparty',
  'depositAddress',
  'coin',
  'tx',
] as const;

export async function history(flags: Flags): Promise<void> {
  const s = await open(flags, 'any');
  await sync(s, true);
  if (s.key.kind === 'view') say('A view key does not show payments to the account’s receive codes.');
  const activity = s.wallet.activity();
  // a sync reads no transaction: each is looked up, a few reads of its chain
  const txs = flags.tx ? await each(activity, (a) => s.wallet.transaction(a).catch(() => null)) : [];
  const entries: Record<(typeof FIELDS)[number], string>[] = activity.map((a, i) => ({
    time: (txs[i]?.at ?? a.at)?.toISOString() ?? '',
    kind: a.kind,
    status: a.status,
    amount: amount(a.amount, a.token),
    token: a.token.symbol,
    chain: chainName(a.token.chainId),
    chainId: String(a.token.chainId),
    fee: a.fee === null ? '' : amount(a.fee, a.token),
    counterparty: counterparty(a),
    depositAddress: a.via && 'depositAddress' in a.via ? a.via.depositAddress : '',
    coin: a.coin ?? '',
    tx: txs[i]?.hash ?? a.txHash ?? '',
  }));
  if (flags.json) return void answer(flags, '', entries);
  if (flags.csv) {
    return void process.stdout.write(`${csv([[...FIELDS], ...entries.map((e) => FIELDS.map((f) => e[f]))])}\n`);
  }
  const rows = entries.map((e) => [
    minute(e.time ? new Date(e.time) : null),
    e.status === 'failed' ? `${e.kind} (failed)` : e.kind,
    e.amount,
    e.token,
    e.chain,
    short(e.counterparty),
    e.fee,
    ...(flags.tx ? [e.tx] : []),
  ]);
  const head = ['TIME (UTC)', 'KIND', 'AMOUNT', 'TOKEN', 'CHAIN', 'WITH', 'FEE', ...(flags.tx ? ['TRANSACTION'] : [])];
  answer(flags, rows.length ? table(head, rows, [2, 6]) : 'Nothing yet.', entries);
}

export async function coins(flags: Flags): Promise<void> {
  const s = await open(flags, 'any');
  await sync(s, true);
  const all = s.wallet.coins();
  const state = (c: (typeof all)[number]) =>
    c.state === 'spendable' || c.state === 'spending' || c.state === 'blocked' ? c.state : NOT_YET[c.state];
  const rows = all.map((c) => [
    c.id,
    c.kind,
    c.token.symbol,
    chainName(c.token.chainId),
    amount(c.amount, c.token),
    c.readyBy ? `${state(c)} ${until(c.readyBy)}` : state(c),
  ]);
  answer(
    flags,
    rows.length ? table(['COIN', 'KIND', 'TOKEN', 'CHAIN', 'AMOUNT', 'STATE'], rows, [4]) : 'Nothing yet.',
    all.map((c) => ({
      id: c.id,
      kind: c.kind,
      token: c.token.symbol,
      chain: chainName(c.token.chainId),
      chainId: String(c.token.chainId),
      amount: amount(c.amount, c.token),
      state: c.state,
      readyBy: c.readyBy?.toISOString() ?? null,
    })),
  );
}

export async function receive(flags: Flags, [symbol]: string[]): Promise<void> {
  if (!symbol) {
    // the account's address under another spelling: the key alone gives it
    const key = await readKey(flags['key-file']);
    return void answer(flags, accountId(key.address), { id: accountId(key.address), address: key.address });
  }
  const s = await open(flags, 'seed');
  const token = tokenOf(s, symbol);
  const code = await s.wallet.receiveCode(token);
  say(
    `Whoever has this code pays ${token.symbol} on ${chainName(token.chainId)} into the account, and no view key shows it.`,
  );
  answer(flags, code, { code, token: token.symbol, chain: chainName(token.chainId), chainId: String(token.chainId) });
}

export async function deposit(flags: Flags, [symbol]: string[]): Promise<void> {
  const s = await open(flags, 'seed');
  const token = tokenOf(s, symbol);
  const { address, fee } = await s.wallet.depositAddress(token);
  const [asset, chain] = [underlyingSymbol(s.network, token), chainName(token.chainId)];
  const watchedUntil = new Date(Date.now() + 7 * 24 * 3600 * 1000);
  say(`Send ${asset} on ${chain} to this address, from anywhere. On ${chain} only: sent on another chain, it is lost.`);
  say(
    `Each payment pays ${amount(fee, token)} ${asset} to the deposit relayer, and has to be more than that. ` +
      `Watched until ${watchedUntil.toISOString().slice(0, 10)}.`,
  );
  answer(flags, address, {
    address,
    asset,
    chain,
    chainId: String(token.chainId),
    fee: amount(fee, token),
    watchedUntil: watchedUntil.toISOString(),
  });
}

/** Why `token` cannot pay what was asked, in its own units, where `e` is the wallet saying so in base units. */
function shortfall(s: Session, token: Token, e: unknown): unknown {
  if (!(e instanceof WalletError) || (e.code !== 'funds-settling' && e.code !== 'insufficient-funds')) return e;
  const has = `${amount(spendable(s, token), token)} ${token.symbol} on ${chainName(token.chainId)} is spendable`;
  if (e.code === 'insufficient-funds') return new Failure(`not enough to pay that and its fee: ${has}`);
  const when = e.waitsOn?.readyBy ? `, which should do in ${until(e.waitsOn.readyBy)}` : '';
  return new Failure(`not enough is spendable yet: ${has}, and the rest is settling${when}`);
}

/** A send or a withdrawal: both pay `amount` out of what is spendable, with the fees on top. */
async function pay(flags: Flags, kind: 'send' | 'withdraw', [typed, symbol, to]: string[]): Promise<void> {
  if (!typed || !symbol || !to) throw new Usage(`zerc20 ${kind} <amount|max> <token> <to>`);
  if (kind === 'withdraw' && !isAddress(to)) throw new Usage(`${to} is not an address`);
  const s = await open(flags, 'seed', true);
  await sync(s, false);
  const max = typed === 'max';
  // With --yes no one reads which chain was found to pay, and what is paid to an address on a chain its owner does
  // not watch there may be lost: a withdrawal no one confirms names its chain.
  const found =
    kind === 'withdraw' && flags.yes ? undefined : (t: Token) => (max ? 1n : parseAmount(typed, t.decimals));
  const token = tokenOf(s, symbol, found);
  const chain = chainName(token.chainId);
  let value: bigint;
  if (max) {
    const most = await s.wallet.maxAmount({ kind, token });
    if (most.merges > 0)
      throw new Failure(`its coins are too scattered to pay it all at once: \`zerc20 merge ${token.symbol}\` first`);
    if (most.amount === 0n) throw new Failure(`no ${token.symbol} on ${chain} is left to pay once the fee is taken`);
    value = most.amount;
  } else value = parseAmount(typed, token.decimals);
  const quote = await s.wallet.fees({ kind, token, amount: value }).catch((e: unknown) => {
    throw shortfall(s, token, e);
  });
  const maxFee = feeCap(flags, token, quote);
  const fee = `fee ${amount(quote.fee, token)} ${token.symbol}`;
  if (kind === 'send') {
    await confirm(flags, `Send ${amount(value, token)} ${token.symbol} on ${chain} to ${short(to)}, ${fee}?`);
    return follow(flags, await s.wallet.send({ to, token, amount: value, maxFee }));
  }
  // a public address most often expects the asset itself: the zERC20 token is paid out only when asked for
  const paid = flags.wrapped ? `${token.symbol} (the zERC20 token itself)` : underlyingSymbol(s.network, token);
  await confirm(flags, `Withdraw ${amount(value, token)} ${paid} on ${chain} to ${to}, in public, ${fee}?`);
  const address = to as Address; // checked before the wallet opened
  return follow(flags, await s.wallet.withdraw({ to: address, token, amount: value, maxFee, unwrap: !flags.wrapped }));
}

export const send = (flags: Flags, args: string[]) => pay(flags, 'send', args);
export const withdraw = (flags: Flags, args: string[]) => pay(flags, 'withdraw', args);

export async function merge(flags: Flags, [symbol]: string[]): Promise<void> {
  const s = await open(flags, 'seed');
  await sync(s, false);
  const token = tokenOf(s, symbol, () => 1n);
  const chain = chainName(token.chainId);
  const first = await s.wallet.nextMerge(token);
  if (!first) {
    say(`Nothing to merge: ${token.symbol} on ${chain} is in one note, or none of it is spendable.`);
    if (flags.json) answer(flags, '', { kind: KIND.consolidate, chainId: String(token.chainId), txHashes: [] });
    return;
  }
  const quote = await s.wallet.fees({ kind: 'consolidate', token });
  const maxFee = feeCap(flags, token, quote);
  const prover = s.network.mergeProver;
  const here = prover && 'local' in prover.trust;
  if (here) {
    const ready = await fetch(`${prover.url}/status`)
      .then((r) => r.json() as Promise<{ mergeKey?: boolean }>)
      .catch(() => null);
    if (!ready?.mergeKey)
      throw new Failure(`no merge prover is ready at ${prover.url}: run \`zerc20 prover start\` and wait for it`);
  }
  const by = here ? `the prover on this machine` : `the network's merge prover`;
  const merges = quote.steps === 1 ? 'one merge' : `${quote.steps} merges`;
  await confirm(
    flags,
    `Merge ${token.symbol} on ${chain} into one note, in ${merges} that ${by} proves, ` +
      `fee ${amount(quote.fee, token)} ${token.symbol}?`,
  );
  if (here) writeFileSync(proverNote(s.network, s.key), prover.url);
  return follow(flags, await s.wallet.consolidate({ token, maxFee }));
}

export async function viewKey(flags: Flags): Promise<void> {
  const s = await open(flags, 'seed');
  say(`Whoever has this key sees what the account holds and did on ${s.network.name}, and can spend none of it.`);
  answer(flags, s.wallet.viewKey(), { viewKey: s.wallet.viewKey(), network: s.network.name });
}

/** Makes an account: of a fresh recovery phrase, or of the one in `--key-file`, which registers an account whose
 * phrase was made elsewhere. `ZERC20_KEY` is not looked at: a shell that still exports another account's key would
 * be answered with that account, in place of a new one. The phrase is printed once the account exists, and nowhere
 * kept. */
export async function create(flags: Flags): Promise<void> {
  const network = networkOf(flags);
  const given = flags['key-file'] ? keyIn(flags['key-file']) : null;
  if (given?.kind === 'view') throw new Failure('a view key watches an account: it makes none');
  const key = given ?? seedKey(crypto.getRandomValues(new Uint8Array(32)));
  opened = await openAccount(network, key, { create: true });
  const [id, phrase] = [accountId(key.address), entropyToMnemonic(key.seed, wordlist)];
  say(`${id} is on ${network.name}.`);
  if (!given) say('These 24 words are its only key, and are shown this once: keep them where nothing else reads them.');
  answer(flags, given ? id : phrase, { id, address: key.address, network: network.name, ...(given ? {} : { phrase }) });
}
