import { type Server, type ServerResponse, createServer } from 'node:http';
import type { AddressInfo } from 'node:net';
import { createPublicClient } from 'viem';
import { afterEach, expect, test, vi } from 'vitest';
import { rpcTransport } from '../src/index.js';

const servers: Server[] = [];

afterEach(() => {
  vi.useRealTimers();
  for (const server of servers.splice(0)) server.close();
});

/** A local server of RPCs, each path one, answering as `answer` says; `asked` lists the paths asked, in order. */
async function rpcs(answer: (path: string, res: ServerResponse, id: number) => void) {
  const asked: string[] = [];
  const server = createServer((req, res) => {
    let body = '';
    req.on('data', (chunk: Buffer) => (body += chunk.toString()));
    req.on('end', () => {
      asked.push(req.url!);
      answer(req.url!, res, (JSON.parse(body) as { id: number }).id);
    });
  });
  servers.push(server);
  await new Promise<void>((resolve) => server.listen(0, '127.0.0.1', resolve));
  return { at: `http://127.0.0.1:${(server.address() as AddressInfo).port}`, asked };
}

const reply = (res: ServerResponse, id: number, answer: object) =>
  res.writeHead(200, { 'content-type': 'application/json' }).end(JSON.stringify({ jsonrpc: '2.0', id, ...answer }));

// port 1 refuses the connection, as a host a resolver blanks fails the fetch
const UNREACHABLE = 'http://127.0.0.1:1';

test('an RPC that fails a call without answering is tried after the others for five minutes, then in its place again', async () => {
  const s = await rpcs((path, res, id) =>
    path === '/busy' ? res.writeHead(429).end() : reply(res, id, { result: '0x1' }),
  );
  const client = createPublicClient({ transport: rpcTransport([UNREACHABLE, `${s.at}/busy`, `${s.at}/ok`]) });
  expect(await client.getChainId()).toBe(1);
  expect(s.asked).toEqual(['/busy', '/ok']);
  expect(await client.getChainId()).toBe(1);
  expect(s.asked).toEqual(['/busy', '/ok', '/ok']);
  vi.useFakeTimers({ toFake: ['Date'], now: Date.now() + 5 * 60_000 });
  expect(await client.getChainId()).toBe(1);
  expect(s.asked).toEqual(['/busy', '/ok', '/ok', '/busy', '/ok']);
});

test("a node's answer is what the call fails with, over an RPC tried after it that could not be reached", async () => {
  const s = await rpcs((_, res, id) =>
    reply(res, id, { error: { code: -32000, message: 'insufficient funds for gas * price + value' } }),
  );
  const client = createPublicClient({ transport: rpcTransport([`${s.at}/poor`, UNREACHABLE]) });
  await expect(client.request({ method: 'eth_chainId' })).rejects.toThrow('insufficient funds');
  // the node's word stands: it is not asked again
  expect(s.asked).toEqual(['/poor']);
});

test('a call every RPC turns away is tried again, though one of them is gone', async () => {
  let turned = false;
  const s = await rpcs((path, res, id) => {
    if (path === '/gone') return void res.writeHead(404).end();
    if (!turned) return void ((turned = true), res.writeHead(429).end());
    reply(res, id, { result: '0x1' });
  });
  const client = createPublicClient({ transport: rpcTransport([`${s.at}/gone`, `${s.at}/busy`]) });
  expect(await client.getChainId()).toBe(1);
  expect(s.asked).toEqual(['/gone', '/busy', '/gone', '/busy']);
});
