// A browser demo of the wallet SDK against scripts/dev-stack.sh, or a deployed network (vite.config.ts). The account is
// the browser's own wallet (MetaMask, ...), or on the local stack a test key that signs only through a stand-in for one,
// which asks before every signature and transaction. Either way the page counts the requests, so it shows how often a
// user is prompted, and for what. Every action is open at once, for any token of the chain picked: try them in any
// order.

import {
  type Abi,
  type Account,
  type Address,
  type Chain,
  type EIP1193Provider,
  type Hex,
  type TransactionSerializable,
  type Transport,
  UserRejectedRequestError,
  type WalletClient,
  bytesToHex,
  createPublicClient,
  createWalletClient,
  custom,
  decodeFunctionData,
  defineChain,
  erc20Abi,
  formatEther,
  formatUnits,
  hexToBytes,
  http,
  numberToHex,
  parseAbi,
  parseUnits,
} from 'viem';
import { privateKeyToAccount, toAccount } from 'viem/accounts';
import * as viemChains from 'viem/chains';
import { decodeCode } from '@zerc20/storage-sdk';
// the SDK's own ABIs, only to name the calls the demo wallet is asked to sign
import { NATIVE, depositAddressAbi, ledgerAbi, tokenAbi, verifierAbi } from '../src/chain.js';
import {
  type DepositStep,
  type FeeQuote,
  type Operation,
  PointOfSale,
  type Token,
  Wallet,
  WalletError,
  networkFromJson,
  seedFromSignature,
} from '../src/index.js';

declare const __NETWORK__: string;
declare const __RUN__: string;
declare const __KEYS__: string;
declare global {
  interface Window {
    ethereum?: EIP1193Provider;
  }
}

const network = networkFromJson(__NETWORK__);
// a local replica: through the dev server's proxy (vite.config.ts)
if (network.storage.host.startsWith('http:')) network.storage.host = location.origin;
/** The network's chains, by the names viem knows them by, each read through its own RPC. */
const chains: Chain[] = network.chains.map((c) => {
  const id = Number(c.chainId);
  const name = Object.values(viemChains).find((k) => k.id === id)?.name ?? `Chain ${id}`;
  const nativeCurrency = { ...(c.nativeCurrency ?? { name: 'Ether', symbol: 'ETH' }), decimals: 18 };
  return defineChain({ id, name, nativeCurrency, rpcUrls: { default: { http: c.rpcUrls } } });
});
const chainOf = (chainId: bigint) => chains.find((c) => BigInt(c.id) === chainId)!;
const clients = new Map(chains.map((c) => [BigInt(c.id), createPublicClient({ chain: c, transport: http() })]));
const client = (chainId: bigint) => clients.get(chainId)!;
/** The chain the page is on: its tokens, balances and history. */
const selectedChain = () => BigInt($<HTMLSelectElement>('chain').value);
const LOCAL = chains[0].id === 31337;
// DEMO_KEYS, else on the local stack the users' accounts scripts/dev-stack.sh prints (anvil's well-known test keys
// 6-9). A deployed network needs none: the browser's wallet signs.
const TEST_KEYS: Hex[] = __KEYS__
  ? (__KEYS__.split(',') as Hex[])
  : !LOCAL
    ? []
    : [
        '0x92db14e403b83dfe3df233f83dfa3a0d7096f21ca9b0d6d6b8d88b2b4ec1564e',
        '0x4bbbf85ce3377467afe5d46f804f221813b2bb87f24d81f60f1fcdbf7cbf4356',
        '0xdbda1821b80551c9d65939329250298aa3472ba22feea921c0cf5d620ea67b97',
        '0x2a871d0798f97d79848a013d4936a73bf4cc922c825d33c1cf7073dff6d409c6',
      ];
/** A testnet's DummyUSDC: anyone may mint. */
const mintAbi = parseAbi(['function mint(address to, uint256 amount)']);
const STORAGE_PREFIX = 'zerc20-wallet-demo/';
const SYNC_MS = 5_000;

const $ = <T extends HTMLElement = HTMLElement>(id: string) => document.getElementById(id) as T;
const message = (e: unknown) =>
  e instanceof WalletError ? `${e.code}: ${e.message}` : e instanceof Error ? e.message : String(e);
const json = (v: unknown) => JSON.stringify(v, (_, x: unknown) => (typeof x === 'bigint' ? `${x}` : x));
const fmt = (amount: bigint, t: Token) => `${formatUnits(amount, t.decimals)} ${t.symbol}`;

// ── The demo wallet: asks before it signs ──

const asked = { signatures: 0, transactions: 0 };
const knownAbi = [...tokenAbi, ...erc20Abi, ...verifierAbi, ...ledgerAbi, ...depositAddressAbi, ...mintAbi] as Abi;

/** Requests waiting for the one dialog, answered one at a time as a browser wallet queues them. */
let prompting: Promise<unknown> = Promise.resolve();

/** Shows one request and waits for its answer. */
async function answer(title: string, details: string): Promise<boolean> {
  const dialog = $<HTMLDialogElement>('prompt');
  $('prompt-title').textContent = title;
  $('prompt-body').textContent = details;
  dialog.returnValue = ''; // Esc leaves it as is: rejected
  dialog.showModal();
  await new Promise((r) => dialog.addEventListener('close', r, { once: true }));
  return dialog.returnValue === 'approve';
}

/** Counts and logs one request, as the user answered it. */
function record(kind: keyof typeof asked, title: string, summary: string, answer: 'approved' | 'rejected' | 'failed') {
  $(kind).textContent = `${++asked[kind]}`;
  const item = document.createElement('li');
  item.textContent = `${new Date().toLocaleTimeString()} ${title.toLowerCase()}: ${summary}, ${answer}`;
  item.classList.toggle('error', answer !== 'approved');
  $('prompts').prepend(item);
}

/** Shows a request as a browser wallet would, after those before it, and logs the answer; a rejection throws what a
 * wallet's does. */
async function ask(kind: keyof typeof asked, title: string, summary: string, details: string): Promise<void> {
  const turn = prompting.then(() => answer(title, details));
  prompting = turn.catch(() => {});
  const approved = await turn;
  record(kind, title, summary, approved ? 'approved' : 'rejected');
  if (!approved) throw new UserRejectedRequestError(new Error('rejected in the demo wallet'));
}

function describe(tx: TransactionSerializable): { summary: string; details: string } {
  let call = tx.data?.slice(0, 10) ?? 'a plain transfer';
  let args = '';
  try {
    const decoded = decodeFunctionData({ abi: knownAbi, data: tx.data! });
    call = decoded.functionName;
    args = json(decoded.args);
  } catch {
    // not one of the SDK's calls: the selector it is
  }
  const fee =
    tx.gas !== undefined && tx.maxFeePerGas !== undefined ? `${formatEther(tx.gas * tx.maxFeePerGas)} ETH` : '-';
  const details = [
    `to: ${tx.to}`,
    `value: ${formatEther(tx.value ?? 0n)} ETH`,
    `max gas fee: ${fee}`,
    `call: ${call}`,
    args && `args: ${args.length > 600 ? `${args.slice(0, 600)}…` : args}`,
  ];
  return { summary: call, details: details.filter(Boolean).join('\n') };
}

function demoAccount(key: Hex) {
  const inner = privateKeyToAccount(key);
  return toAccount({
    address: inner.address,
    async signMessage({ message }) {
      const text =
        typeof message === 'string' ? message : typeof message.raw === 'string' ? message.raw : bytesToHex(message.raw);
      await ask('signatures', 'Signature request', text.split('\n')[0], text);
      return inner.signMessage({ message });
    },
    async signTransaction(tx, options) {
      const { summary, details } = describe(tx);
      await ask('transactions', 'Transaction request', summary, details);
      return inner.signTransaction(tx, options);
    },
    async signTypedData(typedData) {
      await ask('signatures', 'Typed data request', `${String(typedData.primaryType)}`, json(typedData));
      return inner.signTypedData(typedData);
    },
  });
}

// ── The browser's wallet: it asks, the page counts ──

/** Puts the browser's wallet on `chain`, adding the chain first if the wallet does not know it. */
async function ensureChain(eth: EIP1193Provider, chain: Chain) {
  if (Number(await eth.request({ method: 'eth_chainId' })) === chain.id) return;
  const chainId = numberToHex(chain.id);
  try {
    await eth.request({ method: 'wallet_switchEthereumChain', params: [{ chainId }] });
  } catch (e) {
    const code = (e as { code?: number; data?: { originalError?: { code?: number } } }).code;
    if (code !== 4902 && (e as { data?: { originalError?: { code?: number } } }).data?.originalError?.code !== 4902)
      throw e;
    await eth.request({
      method: 'wallet_addEthereumChain',
      params: [
        { chainId, chainName: chain.name, nativeCurrency: chain.nativeCurrency, rpcUrls: chain.rpcUrls.default.http },
      ],
    });
  }
}

/** `eth` with every signature and transaction request counted and logged. A switch to another of the network's chains,
 * the SDK's before its transactions or the page's own (onChain), adds the chain if the wallet does not know it. */
function counted(eth: EIP1193Provider) {
  return {
    async request(args: { method: string; params?: unknown }): Promise<unknown> {
      const { method } = args;
      const params = (args.params ?? []) as unknown[];
      let kind: keyof typeof asked | null = null;
      let title = '';
      let summary = method;
      if (method === 'wallet_switchEthereumChain') {
        await ensureChain(eth, chainOf(BigInt((params[0] as { chainId: Hex }).chainId)));
        return null;
      }
      if (method === 'eth_sendTransaction') {
        const tx = params[0] as { to?: Address; data?: Hex; value?: Hex };
        [kind, title] = ['transactions', 'Transaction request'];
        summary = describe({ to: tx.to, data: tx.data, value: tx.value ? BigInt(tx.value) : 0n }).summary;
      } else if (method === 'personal_sign' || method.startsWith('eth_signTypedData')) {
        [kind, title] = ['signatures', 'Signature request'];
      }
      if (!kind) return eth.request(args as never);
      try {
        const result = await eth.request(args as never);
        record(kind, title, summary, 'approved');
        return result;
      } catch (e) {
        record(kind, title, summary, (e as { code?: number }).code === 4001 ? 'rejected' : 'failed');
        throw e;
      }
    },
  };
}

// ── Actions: any of them, any time, several at once (the wallet runs them one after another) ──

let wallet: Wallet;
const running: { name: string; since: number }[] = [];

/** What runs, for how long so far: a proof of work shows nothing else for seconds. */
function showRunning() {
  const s = (since: number) => Math.round((Date.now() - since) / 1000);
  $('running').textContent = running.length
    ? `Running: ${running.map((r) => `${r.name} (${s(r.since)} s)`).join(', ')}…`
    : '';
}

/** Shows an action's result, or why it failed, next to its button. */
type Show = (text: string, failed: boolean) => void;

/** Clears the last error: it stays until the next action starts. */
let clearError = () => {};

/** Runs `task`, listed while it runs, and shows what it returns or why it failed. */
function act(name: string, task: () => Promise<string>, show: Show) {
  clearError();
  clearError = () => {};
  const entry = { name, since: Date.now() };
  running.push(entry);
  showRunning();
  const ticker = setInterval(showRunning, 1000);
  task()
    .then(
      (result) => show(result, false),
      (e: unknown) => {
        show(`${name} failed: ${message(e)}`, true);
        clearError = () => show('', false);
      },
    )
    .finally(() => {
      clearInterval(ticker);
      running.splice(running.indexOf(entry), 1);
      showRunning();
      if (wallet) render();
    });
}

/** Submits form `id` to `run` with the button that submitted it. */
function onSubmit(id: string, run: (data: FormData, button: string) => Promise<string>) {
  const form = $<HTMLFormElement>(id);
  form.onsubmit = (event) => {
    event.preventDefault();
    const button = event.submitter as HTMLButtonElement;
    const out = form.querySelector<HTMLOutputElement | HTMLTextAreaElement>('.out')!;
    act(
      `${id}: ${button.textContent}`,
      () => run(new FormData(form), button.value),
      (text, failed) => {
        out.value = text;
        out.classList.toggle('error', failed);
      },
    );
  };
}

const text = (data: FormData, name: string) => {
  const v = data.get(name);
  return typeof v === 'string' ? v.trim() : '';
};

function token(): Token {
  const t = wallet.tokens().find((t) => `${t.chainId}:${t.tokenId}` === $<HTMLSelectElement>('token').value);
  if (!t) throw new Error('no token yet: wait for the first sync');
  return t;
}

/** A positive amount in `decimals`: more digits than the token has are refused, never rounded away. */
function amountOf(data: FormData, decimals: number): bigint {
  const raw = text(data, 'amount');
  const digits = decimals > 0 ? `(\\.\\d{1,${decimals}})?` : '';
  if (!new RegExp(`^\\d+${digits}$`).test(raw))
    throw new Error(`enter an amount with at most ${decimals} decimals, such as 0.3`);
  const amount = parseUnits(raw, decimals);
  if (amount === 0n) throw new Error('enter an amount above zero');
  return amount;
}

const quote = (q: FeeQuote, t: Token) =>
  `${fmt(q.relayer, t)} to the relayer + ${fmt(q.protocol, t)} protocol, ${q.steps} transaction(s)`;
const native = (t: Token) => t.underlying.toLowerCase() === NATIVE.toLowerCase();

/** The underlying asset's symbol, read once: the chain's native currency's, or the ERC20's own. */
const symbols = new Map<string, string>();
async function underlyingSymbol(t: Token): Promise<string> {
  if (native(t)) return chainOf(t.chainId).nativeCurrency.symbol;
  const k = `${t.chainId}:${t.underlying}`;
  let s = symbols.get(k);
  if (s === undefined) {
    s = await client(t.chainId).readContract({ address: t.underlying, abi: erc20Abi, functionName: 'symbol' });
    symbols.set(k, s);
  }
  return s;
}

/** Puts the account's wallet on `chainId`, before a transaction of the page's own: the SDK switches for its own. */
async function onChain(chainId: bigint) {
  if ((await walletClient.getChainId()) !== Number(chainId)) await walletClient.switchChain({ id: Number(chainId) });
}

/** Lets `t` take `amount` of the account's underlying, for a wrap. */
async function approveFor(t: Token, amount: bigint) {
  const owner = walletClient.account.address;
  const allowance = await client(t.chainId).readContract({
    address: t.underlying,
    abi: erc20Abi,
    functionName: 'allowance',
    args: [owner, t.address],
  });
  if (allowance >= amount) return;
  const hash = await walletClient.writeContract({
    chain: null,
    address: t.underlying,
    abi: erc20Abi,
    functionName: 'approve',
    args: [t.address, amount],
  });
  await client(t.chainId).waitForTransactionReceipt({ hash });
}

// Each action reads the selected token once: the selector may change while it runs.
function wireActions() {
  onSubmit('deposit', async (data, button) => {
    const t = token();
    const symbol = await underlyingSymbol(t);
    if (button === 'address') {
      const { address, fee } = await withSteps(`Deposit address for ${t.symbol}`, symbol, (onStep) =>
        wallet.depositAddress(t, { onStep }),
      );
      return `${address}: send ${symbol} to it (the relayer takes ${formatUnits(fee, t.decimals)} ${symbol} of each)`;
    }
    const amount = amountOf(data, t.decimals);
    await withSteps(`Deposit of ${fmt(amount, t)}`, symbol, (onStep) => wallet.deposit({ token: t, amount, onStep }));
    return 'Sent';
  });

  onSubmit('send', async (data, button) => {
    const t = token();
    const to = text(data, 'to');
    const amount = amountOf(data, t.decimals);
    const fees = () => wallet.fees({ kind: 'send', token: t, amount });
    if (button === 'quote') return quoteOrMerge(t, fees);
    // the fee quoted now caps what it pays: the relayer names its own
    return payOrMerge('Send', t, async () => {
      const q = await fees();
      return wallet.send({ to, token: t, amount, maxFee: q.fee });
    });
  });

  onSubmit('withdraw', async (data, button) => {
    const t = token();
    const amount = amountOf(data, t.decimals);
    const fees = () => wallet.fees({ kind: 'withdraw', token: t, amount });
    if (button === 'quote') return quoteOrMerge(t, fees);
    return payOrMerge('Withdraw', t, async () => {
      const q = await fees();
      return wallet.withdraw({ to: text(data, 'to') as Address, token: t, amount, maxFee: q.fee });
    });
  });

  onSubmit('request', async () => {
    const t = token();
    const code = await wallet.receiveCode(t);
    const burnAddress = bytesToHex(decodeCode(code)!.burnAddress);
    return `${code}\n\nOr send ${t.symbol} to ${burnAddress}`;
  });

  onSubmit('consolidate', async (_, button) => {
    const t = token();
    // the checked coins of this token, or everything; by id, as a sync makes new token objects
    const ids = wallet
      .coins()
      .filter((c) => checked.has(c.id) && c.token.chainId === t.chainId && c.token.tokenId === t.tokenId)
      .map((c) => c.id);
    const coins = ids.length > 0 ? ids : undefined;
    const q = await wallet.fees({ kind: 'consolidate', token: t, coins });
    if (button === 'quote') return quote(q, t);
    const op = await wallet.consolidate({ token: t, coins, maxFee: q.fee });
    for (const id of ids) checked.delete(id);
    return `Started: operation ${op.id}`;
  });

  // not the SDK: a plain transfer of the selected token's underlying from the account, to fund a deposit address; or
  // the underlying wrapped into the token at an address, which is how a customer pays a merchant's burn address. A
  // token and its underlying have the same decimals.
  onSubmit('transfer', async (data, button) => {
    const t = token();
    const [to, amount] = [text(data, 'to') as Address, amountOf(data, t.decimals)];
    // more than the account holds would only revert, after the approval for a wrap
    const owner = walletClient.account.address;
    const r = client(t.chainId);
    const held = native(t)
      ? await r.getBalance({ address: owner })
      : await r.readContract({ address: t.underlying, abi: erc20Abi, functionName: 'balanceOf', args: [owner] });
    if (held < amount)
      throw new Error(
        `this account holds ${formatUnits(held, t.decimals)} ${await underlyingSymbol(t)}, less than that`,
      );
    await onChain(t.chainId);
    let hash: Hex;
    if (button === 'wrap') {
      if (!native(t)) await approveFor(t, amount);
      hash = await walletClient.writeContract({
        chain: null,
        address: t.address,
        abi: tokenAbi,
        functionName: 'wrap',
        args: [amount, to],
        value: native(t) ? amount : 0n,
      });
    } else {
      hash = native(t)
        ? await walletClient.sendTransaction({ chain: null, to, value: amount })
        : await walletClient.writeContract({
            chain: null,
            address: t.underlying,
            abi: erc20Abi,
            functionName: 'transfer',
            args: [to, amount],
          });
    }
    const receipt = await r.waitForTransactionReceipt({ hash });
    return `${receipt.status}: ${hash}`;
  });

  // a point of sale, played on this page: the wallet makes it a key, with which it records payment addresses, hands them
  // out and follows what reaches them, holding no spending key, as a shop's tablet would. Its state is kept beside the
  // wallet's.
  let pos: Promise<PointOfSale> | undefined;
  const openPos = () =>
    (pos ??= (async () => {
      const p = await PointOfSale.open({ network, persist: persist(`${wallet.address}/pos`) });
      if (!p.connected) await p.connect(wallet.address, await wallet.posKey());
      return p;
    })());
  onSubmit('pos', async (data, button) => {
    const t = token();
    const p = await openPos();
    if (button === 'status') {
      const { sales, errors } = await p.refresh(p.sales().map((s) => s.id));
      if (errors.length > 0) throw errors[0];
      const line = (s: (typeof sales)[number]) =>
        `${s.sale.burnAddress}: ${fmt(s.received, t)} final; ${s.payments.map((x) => `${fmt(x.amount, t)} ${x.state}`).join(', ') || 'nothing yet'}`;
      return sales.map(line).join('\n') || 'No sale yet';
    }
    const amount = text(data, 'amount') ? amountOf(data, t.decimals) : undefined;
    const sale = await p.next({ via: button === 'deposit' ? 'deposit' : 'burn', token: t, amount });
    if (button !== 'deposit') return `Pay ${t.symbol} to ${sale.burnAddress}`;
    const symbol = await underlyingSymbol(t);
    return `Pay ${symbol} to ${sale.depositAddress}, plus ${formatUnits(sale.depositFee!, t.decimals)} ${symbol} for the relayer`;
  });
}

// ── What a deposit waits on, in a popup while it does ──

const stepText = (step: DepositStep, symbol: string) =>
  ({
    queued: 'waiting for the previous action',
    'burn-address': 'preparing a new burn address (a few seconds)',
    approve: `approve ${symbol} in your wallet, then wait for a block`,
    wrap: 'confirm the wrap in your wallet',
  })[step];

/** Runs `task`, showing in the popup what it waits on until it is done. */
async function withSteps<T>(
  title: string,
  symbol: string,
  task: (onStep: (step: DepositStep) => void) => Promise<T>,
): Promise<T> {
  const li = Object.assign(document.createElement('li'), { textContent: `${title}: starting` });
  $('steps').append(li);
  $('steps-box').hidden = false;
  try {
    return await task((step) => (li.textContent = `${title}: ${stepText(step, symbol)}…`));
  } finally {
    li.remove();
    $('steps-box').hidden = $('steps').childElementCount === 0;
  }
}

// ── More than one JoinSplit: the SDK pays with one only, and leaves merging first, and the wait, to the app ──

const needsMerge = (e: unknown) => e instanceof WalletError && e.code === 'needs-consolidation';

/** A fee quote, or what consolidating first costs where no single JoinSplit pays it. */
async function quoteOrMerge(t: Token, get: () => Promise<FeeQuote>): Promise<string> {
  try {
    return quote(await get(), t);
  } catch (e) {
    if (!needsMerge(e)) throw e;
    const q = await wallet.fees({ kind: 'consolidate', token: t });
    return `Needs consolidating first: ${q.steps} merge(s), ${fmt(q.fee, t)} fee, then the payment`;
  }
}

/** Pays with `pay`. Where no single JoinSplit pays it, asks to consolidate first, then runs both one after the
 * other, showing each one's status and transactions. */
async function payOrMerge(what: string, t: Token, pay: () => Promise<Operation>): Promise<string> {
  try {
    const op = await pay();
    return `Started: operation ${op.id}`;
  } catch (e) {
    if (!needsMerge(e)) throw e;
  }
  const q = await wallet.fees({ kind: 'consolidate', token: t });
  const [merge, payment] = [document.createElement('li'), document.createElement('li')];
  merge.textContent = `Consolidate: ${q.steps} merge(s), ${fmt(q.fee, t)} fee`;
  payment.textContent = `${what}: one transaction`;
  $('flow-title').textContent = `${what} in ${q.steps + 1} transactions`;
  $('flow-steps').replaceChildren(merge, payment);
  const [go, close] = [$<HTMLButtonElement>('flow-go'), $<HTMLButtonElement>('flow-close')];
  [go.hidden, close.textContent] = [false, 'Cancel'];
  const dialog = $<HTMLDialogElement>('flow');
  dialog.showModal();
  const started = await new Promise<boolean>((resolve) => {
    go.onclick = (event) => {
      event.preventDefault(); // stays open, to show the progress
      resolve(true);
    };
    dialog.addEventListener('close', () => resolve(false), { once: true });
  });
  if (!started) return 'Cancelled';
  [go.hidden, close.textContent] = [true, 'Close']; // closing it stops nothing

  // the quote shown above is the cap
  const merged = await follow(merge, 'Consolidate', q.steps, () => wallet.consolidate({ token: t, maxFee: q.fee }));
  const paid = await follow(payment, what, 1, pay);
  return `${what} done after consolidating: ${merged.txHashes.length + paid.txHashes.length} transactions`;
}

/** Starts an operation and waits while the sync loop advances it, showing in `li` its status and transactions. */
async function follow(li: HTMLElement, what: string, txs: number, start: () => Promise<Operation>): Promise<Operation> {
  const show = (status: string, op?: Operation) => {
    li.className = op?.status === 'failed' || status.startsWith('failed') ? 'error' : '';
    li.textContent = `${what}: ${status}, ${op?.txHashes.length ?? 0} of ${txs} transaction(s)`;
    for (const hash of op?.txHashes ?? [])
      li.append(Object.assign(document.createElement('div'), { className: 'mono', textContent: hash }));
  };
  show('starting');
  let op: Operation;
  try {
    op = await start();
  } catch (e) {
    show(`failed: ${message(e)}`);
    throw e;
  }
  while (op.status === 'pending') {
    show('pending', op);
    await new Promise((r) => setTimeout(r, 1000));
  }
  show(op.status === 'failed' ? `failed: ${op.error}` : 'done', op);
  if (op.status === 'failed') throw new Error(`${what} failed: ${op.error}`);
  return op;
}

// ── Rendering ──

/** Coins checked, kept across renders. */
const checked = new Set<string>();

function row(cells: (string | Node)[]): HTMLTableRowElement {
  const tr = document.createElement('tr');
  for (const cell of cells) tr.insertCell().append(cell); // text goes in as text, never as HTML
  return tr;
}

function render() {
  const chainId = selectedChain();
  const here = (t: Token) => t.chainId === chainId;
  const tokens = wallet.tokens().filter(here);
  const select = $<HTMLSelectElement>('token');
  // again on another chain, or once a sync finds the tokens
  const keys = tokens.map((t) => `${t.chainId}:${t.tokenId}`).join();
  if (select.dataset.keys !== keys) {
    select.dataset.keys = keys;
    select.replaceChildren(
      ...tokens.map((t) => new Option(`${t.symbol} (token ${t.tokenId})`, `${t.chainId}:${t.tokenId}`)),
    );
    void renderMints(tokens);
  }
  for (const f of document.querySelectorAll<HTMLFieldSetElement>('fieldset.actions')) f.disabled = tokens.length === 0;
  void renderSelected();

  $('balances').replaceChildren(
    ...wallet
      .balances()
      .filter((b) => here(b.token))
      .map((b) => {
        const pending = b.pending.map((p) => `${fmt(p.amount, b.token)} ${p.reason}`).join(', ') || '-';
        return row([b.token.symbol, fmt(b.spendable, b.token), pending, fmt(b.blocked, b.token)]);
      }),
  );
  $('activity').replaceChildren(
    ...wallet
      .activity()
      .filter((a) => here(a.token))
      .map((a) =>
        row([a.at?.toLocaleString() ?? '-', a.kind, fmt(a.amount, a.token), a.counterparty ?? '-', a.status]),
      ),
  );
  const coins = wallet.coins().filter((c) => here(c.token));
  for (const id of checked) if (!coins.some((c) => c.id === id)) checked.delete(id); // spent
  $('coins').replaceChildren(
    ...coins.map((c) => {
      const box = Object.assign(document.createElement('input'), {
        type: 'checkbox',
        checked: checked.has(c.id),
        hidden: c.state === 'blocked' || c.state === 'spending',
      });
      box.onchange = () => (box.checked ? checked.add(c.id) : checked.delete(c.id));
      // a deposit can leave publicly, back to its sender: one in flight as an input cannot
      const exit = Object.assign(document.createElement('button'), {
        textContent: 'Rage exit',
        hidden: c.kind !== 'deposit' || c.state === 'spending',
      });
      exit.onclick = () =>
        act(
          `rage exit ${c.id}`,
          async () =>
            `Rage exit of ${c.id}: ${(await wallet.rageExit(c.id)).length} transaction(s), ${fmt(c.amount, c.token)} back to ${c.via ? wallet.address : c.from}`,
          (text, failed) => {
            $('exit-out').textContent = text;
            $('exit-out').classList.toggle('error', failed);
          },
        );
      return row([box, c.id, c.kind, fmt(c.amount, c.token), c.state, c.from ?? '-', exit]);
    }),
  );
  const short = (h: string) => `${h.slice(0, 10)}…`;
  $('operations').replaceChildren(
    ...wallet
      .operations()
      .filter((op) => op.chainId === chainId)
      .reverse()
      .map((op) =>
        row([op.id, op.kind, op.status, `${op.txHashes.length} ${op.txHashes.map(short).join(' ')}`, op.error ?? '']),
      ),
  );
  $('payments').replaceChildren(
    ...wallet
      .payments()
      .filter((p) => here(p.token))
      .map((p) => row([p.id, p.address, p.amount === null ? '-' : fmt(p.amount, p.token), p.sender ?? '-', p.state])),
  );
  void renderPublic(chainId, tokens);
}

/** The account's public balances on the chain, as a wallet shows them: its native currency, each ERC20 a token wraps,
 * and the zERC20 a withdrawal pays out. */
async function renderPublic(chainId: bigint, tokens: Token[]) {
  const address = wallet.address;
  const r = client(chainId);
  const balanceOf = (token: Address) =>
    r.readContract({ address: token, abi: erc20Abi, functionName: 'balanceOf', args: [address] });
  const eth = await r.getBalance({ address });
  const underlying = await Promise.all(
    tokens
      .filter((t) => !native(t))
      .map(async (t) => `${formatUnits(await balanceOf(t.underlying), t.decimals)} ${await underlyingSymbol(t)}`),
  );
  const wrapped = await Promise.all(tokens.map(async (t) => fmt(await balanceOf(t.address), t)));
  // another chain picked meanwhile: these are not its balances
  if (selectedChain() === chainId)
    $('public').textContent = [
      `${formatEther(eth)} ${chainOf(chainId).nativeCurrency.symbol}`,
      ...underlying,
      ...wrapped,
    ].join(' · ');
}

/** The aside's buttons, named after the selected token. */
async function renderSelected() {
  const t = wallet.tokens().find((t) => `${t.chainId}:${t.tokenId}` === $<HTMLSelectElement>('token').value);
  if (!t) return;
  $('send-underlying').textContent = `Send ${await underlyingSymbol(t)}`;
  $('wrap-there').textContent = `Wrap into ${t.symbol} there`;
}

const MINT = 1000n;

/** A mint button for each underlying anyone may mint: a testnet's DummyUSDC. */
async function renderMints(tokens: Token[]) {
  const account = walletClient.account.address;
  const buttons = [];
  for (const t of tokens.filter((t) => !native(t))) {
    const amount = MINT * 10n ** BigInt(t.decimals);
    const mintable = await client(t.chainId)
      .simulateContract({ account, address: t.underlying, abi: mintAbi, functionName: 'mint', args: [account, amount] })
      .then(
        () => true,
        () => false,
      );
    if (!mintable) continue;
    const symbol = await underlyingSymbol(t);
    const button = Object.assign(document.createElement('button'), {
      type: 'button',
      textContent: `Mint ${MINT} test ${symbol}`,
    });
    button.onclick = () =>
      act(
        `mint ${symbol}`,
        async () => {
          await onChain(t.chainId);
          const hash = await walletClient.writeContract({
            chain: null,
            address: t.underlying,
            abi: mintAbi,
            functionName: 'mint',
            args: [account, amount],
          });
          const receipt = await client(t.chainId).waitForTransactionReceipt({ hash });
          return `${receipt.status}: ${MINT} ${symbol}`;
        },
        (text, failed) => {
          $('mint-out').textContent = text;
          $('mint-out').classList.toggle('error', failed);
        },
      );
    buttons.push(button);
  }
  if (tokens.some((t) => t.chainId !== selectedChain())) return; // another chain picked meanwhile
  $('mints').replaceChildren(...buttons);
  $('mint-section').hidden = buttons.length === 0;
}

// ── Start ──

let walletClient: WalletClient<Transport, Chain | undefined, Account>;

/** Keeps the encrypted state in localStorage, per stack run and address (`name`). */
function persist(name: string) {
  const key = `${STORAGE_PREFIX}${__RUN__}/${name}`;
  return {
    load: async () => {
      const saved = localStorage.getItem(key);
      return saved ? hexToBytes(saved as Hex) : null;
    },
    save: async (bytes: Uint8Array) => localStorage.setItem(key, bytesToHex(bytes)),
  };
}

async function syncLoop() {
  for (;;) {
    try {
      await wallet.sync();
      $('synced').textContent = new Date().toLocaleTimeString();
      $('sync-error').textContent = '';
    } catch (e) {
      $('sync-error').textContent = `sync failed: ${message(e)}`;
    }
    render();
    await new Promise((r) => setTimeout(r, SYNC_MS));
  }
}

/** A test key, signing through the demo wallet. Like a browser wallet, it is on one chain at a time, and a switch
 * moves it: what it sends goes to that chain's RPC. */
function keyClient(key: Hex): typeof walletClient {
  let at = BigInt(chains[0].id);
  const transport = custom({
    async request({ method, params }: { method: string; params?: unknown }) {
      if (method !== 'wallet_switchEthereumChain') return client(at).request({ method, params } as never);
      at = BigInt((params as [{ chainId: Hex }])[0].chainId);
      return null;
    },
  });
  return createWalletClient({ account: demoAccount(key), transport });
}

/** The browser's wallet, from the network's first chain. Another account picked in it is another wallet: the page
 * reloads. */
async function browserClient(): Promise<typeof walletClient> {
  const eth =
    window.ethereum ??
    (() => {
      throw new Error('no browser wallet (window.ethereum) in this browser');
    })();
  const [address] = await eth.request({ method: 'eth_requestAccounts' });
  if (!address) throw new Error('the browser wallet shared no account');
  await ensureChain(eth, chains[0]);
  eth.on?.('accountsChanged', () => location.reload());
  $('wallet-title').textContent = 'Browser wallet';
  $('wallet-hint').hidden = true;
  // no retries: each would ask the user again
  return createWalletClient({ account: address, transport: custom(counted(eth), { retryCount: 0 }) });
}

async function connect(client: typeof walletClient) {
  walletClient = client;
  const { account } = walletClient;
  $('account').textContent = account.address;
  $('running').textContent = 'Sign in your wallet…';
  const { seed } = await seedFromSignature(walletClient);
  // the first time on an address, registering it takes a proof of work: well under a second here, a few on an old phone
  const started = Date.now();
  const opening = () => {
    const s = Math.round((Date.now() - started) / 1000);
    $('running').textContent = `Opening, ${s} s (the first time: one more signature)…`;
  };
  opening();
  const ticker = setInterval(opening, 1000);
  try {
    wallet = await Wallet.open({ network, walletClient, seed, persist: persist(account.address) });
  } finally {
    clearInterval(ticker);
  }
  $('running').textContent = '';
  $('connect').hidden = true;
  $('app').hidden = false;
  $('transfer').hidden = false;
  $('address').textContent = wallet.address;
  $('token').onchange = () => void renderSelected();
  $('chain').onchange = () => render();
  wireActions();
  render();
  void syncLoop();
}

// wallets saved against an earlier stack point at a chain and a canister that are gone
for (const key of Object.keys(localStorage)) {
  if (key.startsWith(STORAGE_PREFIX) && !key.startsWith(`${STORAGE_PREFIX}${__RUN__}/`)) localStorage.removeItem(key);
}
$('chain').replaceChildren(...chains.map((c) => new Option(c.name, `${c.id}`)));
$('keys').replaceChildren(
  ...TEST_KEYS.map((k) => Object.assign(new Option(), { value: k, label: privateKeyToAccount(k).address })),
);
$('test-key').hidden = TEST_KEYS.length === 0;
$('no-browser-wallet').hidden = !!window.ethereum;
// consolidate() refuses without one: say so up front rather than on the click
if (!network.mergeProver) {
  for (const b of $('consolidate').querySelectorAll('button')) b.disabled = true;
  $('consolidate').querySelector('.hint')!.textContent =
    'This network has no merge prover: start scripts/dev-stack.sh with SPEED=fast or MERGE=1 to consolidate.';
}
$<HTMLButtonElement>('connect-browser').disabled = !window.ethereum;

/** Connects with what `client` resolves to, the form disabled meanwhile. */
function start(client: () => Promise<typeof walletClient>) {
  const fieldset = $('connect').querySelector('fieldset')!;
  fieldset.disabled = true;
  $('error').textContent = '';
  client()
    .then(connect)
    .catch((e: unknown) => {
      fieldset.disabled = false;
      $('running').textContent = '';
      $('error').textContent = `Connecting failed: ${message(e)}`;
    });
}
$('connect-browser').onclick = () => start(browserClient);
$<HTMLFormElement>('connect').onsubmit = (event) => {
  event.preventDefault();
  const key = text(new FormData($<HTMLFormElement>('connect')), 'key') as Hex; // before disabling, which drops it
  start(async () => keyClient(key));
};
