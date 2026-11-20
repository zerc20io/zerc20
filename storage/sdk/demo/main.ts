// Browser demo: one MetaMask account per tab. Payments are pseudo: notes are written to the canister
// and the on-chain step is skipped.

import { HttpAgent } from '@icp-sdk/core/agent';
import { sha256 } from '@noble/hashes/sha2.js';
import { keccak_256 } from '@noble/hashes/sha3.js';
import { concat, equal, hex, randomBytes, unhex, utf8 } from '../src/crypto.js';
import {
  CanisterClient,
  type LaneRecord,
  type NewRecord,
  type SyncState,
  type ViewKey,
  codeKey,
  commit,
  decodeCode,
  emptyState,
  encodeCode,
  exportState,
  importState,
  lookupRecipient,
  registeredViewKey,
  planBurnBlock,
  planPayCode,
  planSelf,
  planSend,
  refresh,
} from '../src/index.js';

declare const __CANISTER_ID__: string;
declare const __RUN_ID__: string;

interface Ethereum {
  request(args: { method: string; params?: unknown[] }): Promise<unknown>;
  on(event: 'accountsChanged', listener: () => void): void;
}

const ethereum = (window as unknown as { ethereum?: Ethereum }).ethereum;
const CHAINS = [1n, 10n];
const POLL_MS = 3_000;
const STORAGE_PREFIX = 'zerc20-demo/';

const $ = <T extends HTMLElement>(id: string) => document.getElementById(id) as T;
const fromHex = (text: string) => unhex(text.trim().replace(/^0x/, ''));
const short = (bytes: Uint8Array) => `0x${hex(bytes.subarray(0, 4))}…${hex(bytes.subarray(-2))}`;
const toBytes32 = (value: bigint) => unhex(value.toString(16).padStart(64, '0'));
const toBigInt = (bytes: Uint8Array) => BigInt(`0x${hex(bytes)}`);
const timeOf = (ns: bigint) => new Date(Number(ns / 1_000_000n)).toLocaleString();
/** A fresh salt below `Fr`: a zero top byte keeps it in range. */
const freshSalt = () => concat(new Uint8Array(1), randomBytes(31));

let client: CanisterClient;
let view: ViewKey;
let state: SyncState;
let added: NewRecord[] = [];

function status(text: string, error = false) {
  $('status').textContent = text;
  $('status').classList.toggle('error', error);
}

// One task at a time, so every refresh and commit starts from the latest state.
let queue = Promise.resolve();
let running = 0;
function exclusive(task: () => Promise<void>): Promise<void> {
  running++;
  const run = queue.then(task).finally(() => running--);
  queue = run.catch(() => undefined);
  return run;
}

const message = (e: unknown) => (e instanceof Error ? e.message : String(e));

/** Runs the user action `name`, showing progress while it runs and any error after. */
function act(name: string, task: () => Promise<void>) {
  status(`${name}: solving proof of work…`);
  exclusive(task).then(
    () => status(''),
    (e: unknown) => status(`${name} failed: ${message(e)}`, true),
  );
}

// ── State, kept in localStorage as exportState bytes ──

const storageKey = () => `${STORAGE_PREFIX}${__RUN_ID__}/${hex(view.address)}`;

function load(): SyncState {
  try {
    // States from earlier runs point into a canister that no longer exists.
    for (const key of Object.keys(localStorage)) {
      if (key.startsWith(STORAGE_PREFIX) && !key.startsWith(`${STORAGE_PREFIX}${__RUN_ID__}/`))
        localStorage.removeItem(key);
    }
    const saved = localStorage.getItem(storageKey());
    if (saved) return importState(view, unhex(saved)) ?? emptyState(view, CHAINS);
  } catch {
    // No storage: start over every time.
  }
  return emptyState(view, CHAINS);
}

function apply(next: { state: SyncState; added: NewRecord[] }) {
  ({ state, added } = next);
  try {
    localStorage.setItem(storageKey(), hex(exportState(view, state)));
  } catch {
    // Storage full or blocked: the next load syncs from scratch.
  }
  $('updated').textContent = new Date().toLocaleTimeString();
  render();
}

// ── Rendering ──

function row(cells: (string | Node)[], highlight = false): HTMLTableRowElement {
  const tr = document.createElement('tr');
  tr.classList.toggle('new', highlight);
  for (const cell of cells) tr.insertCell().append(cell); // text is appended as text, never as HTML
  return tr;
}

function codeField(code: string): HTMLInputElement {
  const input = Object.assign(document.createElement('input'), { value: code, readOnly: true, size: 24 });
  input.onclick = () => input.select();
  return input;
}

/** A note or a deposit as table cells: its chain, token, value and, for a note to self, what it is the change or the
 * output of. */
function cellsOf(r: LaneRecord): string[] | null {
  if (r.kind === 'note')
    return [`${r.opening.chainId}`, `${r.opening.tokenId}`, `${toBigInt(r.opening.value)}`, r.receipt?.kind ?? ''];
  if (r.kind === 'deposit') return [`${r.chainId}`, `${r.tokenId}`, `${toBigInt(r.value)} (deposit)`, ''];
  return null;
}

function render() {
  const fresh = new Set(added.map((a) => a.record));
  const fromChannels = [
    ...state.incoming.map((channel) => ({ channel, direction: 'received' })),
    ...state.outgoing.lanes.map((channel) => ({ channel, direction: 'sent' })),
  ].flatMap(({ channel, direction }) => {
    const v = channel.via;
    const via =
      v.type === 'address'
        ? 'address'
        : v.type === 'pos'
          ? `point of sale #${v.n}`
          : 'index' in v
            ? `code #${v.index}`
            : `code (public_key ${short(v.code.publicKey)})`;
    // a code's notes each name their own payer
    const peerOf = (r: LaneRecord) => {
      const peer = channel.peer ?? (direction === 'received' && r.kind === 'note' ? (r.payer ?? null) : null);
      return !peer ? '(code receiver)' : equal(peer, view.address) ? 'me' : short(peer);
    };
    return channel.chains.flatMap((chain) =>
      chain.records.map((record) => ({ direction, peer: peerOf(record), via, record })),
    );
  });
  const toSelf = state.own.flatMap((chain) =>
    chain.records.map((record) => ({ direction: 'to self', peer: 'me', via: 'own lane', record })),
  );
  const records = [...fromChannels, ...toSelf].sort((a, b) => (a.record.atNs < b.record.atNs ? 1 : -1));
  $('history').replaceChildren(
    ...records.flatMap(({ direction, peer, via, record }) => {
      const cells = cellsOf(record);
      return cells ? [row([timeOf(record.atNs), direction, peer, via, ...cells], fresh.has(record))] : [];
    }),
  );

  $('codes').replaceChildren(
    ...state.incoming.flatMap(({ via, chains }) => {
      if (via.type !== 'code' || !('index' in via)) return [];
      const paid = chains.reduce((n, chain) => n + chain.records.length, 0);
      const code = encodeCode(codeOf(via.chainId, via.tokenId, via.index));
      return [row([`${via.index}`, `${via.chainId}`, `${via.tokenId}`, `${paid}`, codeField(code)])];
    }),
  );
}

// ── Actions ──

/** A made-up zERC20 public key for `address` to register (a real wallet derives it from its seed). */
const pseudoPublicKey = (address: Uint8Array) => concat(new Uint8Array(1), sha256(address).subarray(1));

/** Receive code `index`, with a made-up burn address and public key: a real wallet derives the address from its burn
 * key and the public key from its seed (`keys::derive_burn_address` and `keys::code_spend_secret`), and records the
 * burn address's salt in the burn block. */
const codeOf = (chainId: bigint, tokenId: number, index: number) => {
  const pseudo = sha256(concat(view.address, utf8(`${chainId}/${tokenId}/${index}`)));
  return {
    chainId,
    tokenId,
    burnAddress: pseudo.slice(0, 20),
    publicKey: concat(new Uint8Array(1), pseudo.subarray(1)),
    key: codeKey(view.seed, chainId, tokenId, index),
  };
};

function onSubmit(id: string, name: string, task: (form: FormData) => Promise<void>) {
  const form = $<HTMLFormElement>(id);
  form.onsubmit = (event) => {
    event.preventDefault();
    const data = new FormData(form);
    act(name, async () => {
      await task(data);
      form.reset();
    });
  };
}

function wireForms() {
  const text = (data: FormData, name: string) => String(data.get(name) ?? '');

  const opening = (data: FormData, amount: string) => ({
    chainId: BigInt(text(data, 'chain')),
    tokenId: Number(text(data, 'token')),
    value: toBytes32(BigInt(amount)),
    noteSalt: freshSalt(),
  });

  onSubmit('send', 'Send', async (data) => {
    const payment = opening(data, text(data, 'amount'));
    const to = await lookupRecipient(client, fromHex(text(data, 'to')));
    if (!to) throw new Error('the recipient has not opened the demo');
    const change = text(data, 'change');
    // The change goes to the own lane, in the same batch as the payment.
    const receipt = { kind: 'sent' as const, amount: payment.value, fee: toBytes32(0n), counterparty: to.address };
    const plan = (s: SyncState) => [
      ...planSend(view, s, to, payment),
      ...(change ? planSelf(view, s, opening(data, change), receipt) : []),
    ];
    apply(await commit(client, view, state, plan));
  });

  onSubmit('merge', 'Merge', async (data) => {
    const merged = opening(data, text(data, 'amount'));
    const receipt = {
      kind: 'merged' as const,
      amount: merged.value,
      fee: toBytes32(0n),
      counterparty: new Uint8Array(20),
    };
    apply(await commit(client, view, state, (s) => planSelf(view, s, merged, receipt)));
  });

  onSubmit('issue', 'Recording a code', async (data) => {
    // the next burn index, recorded in a burn block (a wallet records them ahead of need)
    const [chainId, tokenId] = [BigInt(text(data, 'chain')), Number(text(data, 'token'))];
    const indices = state.incoming.flatMap(({ via: v }) =>
      v.type === 'code' && 'index' in v && v.chainId === chainId && v.tokenId === tokenId ? [v.index] : [],
    );
    const block = { chainId, tokenId, first: Math.max(-1, ...indices) + 1, salts: [randomBytes(32)] };
    apply(await commit(client, view, state, (s) => planBurnBlock(view, s, block)));
  });

  onSubmit('pay', 'Paying the code', async (data) => {
    const code = decodeCode(text(data, 'code'));
    if (!code) throw new Error('not a receive code');
    const payment = {
      chainId: code.chainId,
      tokenId: code.tokenId,
      value: toBytes32(BigInt(text(data, 'amount'))),
      noteSalt: freshSalt(),
    };
    apply(await commit(client, view, state, (s) => planPayCode(client, view, s, code, payment)));
  });
}

// ── Start ──

async function connect(eth: Ethereum) {
  const [account] = (await eth.request({ method: 'eth_requestAccounts' })) as string[];
  if (!account) throw new Error('no account');
  const address = fromHex(account);
  const signer = async (message: string) =>
    fromHex((await eth.request({ method: 'personal_sign', params: [`0x${hex(utf8(message))}`, account] })) as string);

  const agent = await HttpAgent.create({ host: location.origin, shouldFetchRootKey: true });
  client = new CanisterClient(agent, __CANISTER_ID__);
  status('Sign in MetaMask to unlock your private identity…');
  // Stands in for the root seed a zERC20-v2 wallet already holds: keccak256 of a canonical
  // personal_sign signature (MetaMask's are canonical: low s, v = 27 or 28).
  const rootSeed = keccak_256(await signer(`zerc20-storage demo root seed\naddress: 0x${hex(address)}`));
  status('Registering (the first time: one more signature and a few seconds of proof of work)…');
  view = await registeredViewKey(client, rootSeed, signer, address, pseudoPublicKey(address));
  state = load();

  $<HTMLInputElement>('address').value = `0x${hex(address)}`;
  $('connect').hidden = true;
  $('app').hidden = false;
  wireForms();
  render();
  status('Syncing…');
  await exclusive(async () => apply(await refresh(client, view, state)));
  status('');

  let pollFailed = false;
  setInterval(() => {
    if (running > 0) return; // a refresh or a payment is still running
    exclusive(async () => apply(await refresh(client, view, state))).then(
      () => {
        if (pollFailed) status('');
        pollFailed = false;
      },
      (e: unknown) => {
        pollFailed = true;
        status(`Refresh failed: ${message(e)}`, true);
      },
    );
  }, POLL_MS);
}

if (!ethereum) {
  $('connect').hidden = true;
  status('MetaMask not found. Open this page in a browser with MetaMask.', true);
} else {
  // A different account is a different user: start over.
  ethereum.on('accountsChanged', () => location.reload());
  $<HTMLButtonElement>('connect').onclick = () => {
    $<HTMLButtonElement>('connect').disabled = true;
    connect(ethereum).catch((e: unknown) => {
      $<HTMLButtonElement>('connect').disabled = false;
      status(`Connection failed: ${message(e)}`, true);
    });
  };
}
