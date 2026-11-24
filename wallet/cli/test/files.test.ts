import { createHash } from 'node:crypto';
import { existsSync, mkdtempSync, readFileSync, writeFileSync } from 'node:fs';
import { type Server, createServer } from 'node:http';
import type { AddressInfo } from 'node:net';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { afterAll, beforeAll, expect, test } from 'vitest';
import { download } from '../src/files.js';

const file = Buffer.from(Array.from({ length: 100_000 }, (_, i) => i % 251));
const sha256 = createHash('sha256').update(file).digest('hex');
/** The `range` header of each request the server answered. */
const asked: (string | undefined)[] = [];
let server: Server;
let url: string;

beforeAll(async () => {
  server = createServer((req, res) => {
    asked.push(req.headers.range);
    const from = Number(/bytes=(\d+)-/.exec(req.headers.range ?? '')?.[1] ?? 0);
    if (from >= file.length) return void res.writeHead(416).end();
    res.writeHead(from ? 206 : 200, { 'content-length': file.length - from }).end(file.subarray(from));
  });
  await new Promise<void>((r) => server.listen(0, '127.0.0.1', r));
  url = `http://127.0.0.1:${(server.address() as AddressInfo).port}/key.bin`;
});
afterAll(() => server.close());

const fresh = () => join(mkdtempSync(join(tmpdir(), 'zerc20-files-')), 'key.bin');

test('a download gets its name once whole, and one already there is not asked for again', async () => {
  const path = fresh();
  await download(url, path, sha256);
  expect(readFileSync(path).equals(file)).toBe(true);
  const before = asked.length;
  await download(url, path, sha256);
  expect(asked.length).toBe(before);
});

test('a download that stopped goes on from where it did', async () => {
  const path = fresh();
  writeFileSync(`${path}.part`, file.subarray(0, 60_000));
  await download(url, path, sha256);
  expect(asked.at(-1)).toBe('bytes=60000-');
  expect(readFileSync(path).equals(file)).toBe(true);
  // all of it was there, and only its name was missing
  const whole = fresh();
  writeFileSync(`${whole}.part`, file);
  await download(url, whole, sha256);
  expect(readFileSync(whole).equals(file)).toBe(true);
});

test('a file that is not the one pinned is thrown away, never named', async () => {
  const path = fresh();
  await expect(download(url, path, '00'.repeat(32))).rejects.toThrow('not the file expected');
  expect(existsSync(path) || existsSync(`${path}.part`)).toBe(false);
});
