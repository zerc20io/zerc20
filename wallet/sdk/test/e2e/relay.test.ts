// A withdrawal whose relay answer is lost, as when the page closes right after the request leaves, resumed by the
// wallet opened again from what the first one saved. Its own request lands meanwhile, so relaying it again reverts on a
// nullifier spent already. The wallet relays it again until the indexer shows that spend, rather than proving and
// attesting again, which spends the notes' screenings at the attester and fails, once tried enough, a withdrawal that
// landed. Its input is the change of a withdrawal just before, not final yet, as a second withdrawal soon after a
// first spends, and the indexer's status trails the chain by seconds, as a polled one behind a cache does: the spend
// counts though sync watches no input before it is final. Run through scripts/e2e.sh. It replaces `fetch` for the
// whole file.

import { readFileSync } from 'node:fs';
import { type Hex, createTestClient, defineChain, http, keccak256 } from 'viem';
import { generatePrivateKey, privateKeyToAccount } from 'viem/accounts';
import { expect, test } from 'vitest';
import { Wallet, networkFromJson } from '../../src/index.js';

const network = networkFromJson(readFileSync(process.env.NETWORK!, 'utf8'));
const config = network.chains[0]!;
const anvil = defineChain({
  id: 31337,
  name: 'anvil',
  nativeCurrency: { name: 'ETH', symbol: 'ETH', decimals: 18 },
  rpcUrls: { default: { http: [config.rpcUrls[0]!] } },
});
const testClient = createTestClient({ mode: 'anvil', chain: anvil, transport: http() });
const ETH = 10n ** 18n;
const FEE = ETH / 1000n; // the relayer's, set in scripts/dev-stack.sh
/** How far the indexer's status trails the chain. */
const LAG_MS = 8_000;

type Status = { commitments_final: number; nullifiers_final: number; indexer: { final_block: number } };
const realFetch = globalThis.fetch;
const statuses: { at: number; body: string }[] = [];
/** The final counts the status keeps showing while set: nothing newer is final. */
let finalAt: Status | null = null;
let attested = 0;
/** Set to lose the next relay's answer: the request goes, and the page is gone before the answer comes. */
let losing = false;
globalThis.fetch = (async (input: RequestInfo | URL, init?: RequestInit) => {
  const url = String(input);
  if (url === `${config.indexer}/status`) {
    statuses.push({ at: Date.now(), body: await (await realFetch(input, init)).text() });
    const behind = statuses.filter((s) => s.at <= Date.now() - LAG_MS).at(-1) ?? statuses[0]!;
    const status = JSON.parse(behind.body) as Status;
    if (finalAt) {
      status.commitments_final = finalAt.commitments_final;
      status.nullifiers_final = finalAt.nullifiers_final;
      status.indexer.final_block = finalAt.indexer.final_block;
    }
    return Response.json(status);
  }
  if (url === `${config.attester}/transact`) attested++;
  if (url === `${config.transactRelayer}/transact` && losing) {
    losing = false;
    void realFetch(input, init).catch(() => {});
    await new Promise((r) => setTimeout(r, 300));
    throw new TypeError('fetch failed');
  }
  return realFetch(input, init);
}) as typeof fetch;

/** Syncs until `done` holds. */
async function until(w: Wallet, what: string, done: () => boolean, ms = 120_000): Promise<void> {
  const end = Date.now() + ms;
  for (;;) {
    await w.sync().catch(() => {});
    if (done()) return;
    if (Date.now() > end) throw new Error(`timed out: ${what}`);
    await new Promise((r) => setTimeout(r, 1000));
  }
}

test('a withdrawal whose relay answer was lost is relayed again, not proved again, until the indexer shows it spent', async () => {
  const key: Hex = generatePrivateKey();
  await testClient.setBalance({ address: privateKeyToAccount(key).address, value: 100n * ETH });
  let saved: Uint8Array | null = null;
  const open = () =>
    Wallet.open({
      network,
      account: privateKeyToAccount(key),
      seed: Uint8Array.from(Buffer.from(keccak256(key).slice(2), 'hex')),
      persist: { load: async () => saved, save: async (b) => void (saved = b) },
    });
  const page = await open();
  await page.sync();
  const zeth = page.tokens().find((t) => t.tokenId === 1)!;
  const spendable = (w: Wallet) => w.balances().find((b) => b.token.tokenId === 1)?.spendable;
  await (await page.deposit({ token: zeth, amount: ETH })).wait();
  await until(page, 'the deposit becomes spendable', () => spendable(page) === ETH);

  // nothing newer becomes final: the first withdrawal's change stays tentative, and is spent as such
  finalAt = JSON.parse(statuses.at(-1)!.body) as Status;
  const carol = privateKeyToAccount(generatePrivateKey()).address;
  const first = await page.withdraw({ to: carol, token: zeth, amount: ETH / 10n, maxFee: FEE });
  const change = ETH - ETH / 10n - FEE;
  await until(page, 'the change becomes spendable', () => spendable(page) === change);
  expect(first.stage).toBe('relayed');

  attested = 0;
  const { id } = await page.withdraw({ to: carol, token: zeth, amount: ETH / 10n, maxFee: FEE });
  losing = true;
  while (losing) await page.sync().catch(() => {});
  expect(attested).toBe(1);
  await page.close();

  const again = await open();
  const second = () => again.operations().find((o) => o.id === id)!;
  await until(again, 'the second withdrawal is seen in a block', () => second().stage === 'relayed');
  expect(attested).toBe(1);

  finalAt = null;
  await until(again, 'both are done', () => again.operations().every((o) => o.status === 'done'));
  await until(again, 'the second change becomes spendable', () => spendable(again) === change - ETH / 10n - FEE);
});
