// Files this machine keeps between runs, under one directory: each account's state as the SDK seals it, and the
// public files proving needs, fetched once and checked against a pinned SHA-256.

import { createHash } from 'node:crypto';
import { createReadStream, createWriteStream, existsSync, mkdirSync, renameSync, rmSync, statSync } from 'node:fs';
import { homedir } from 'node:os';
import { dirname, join } from 'node:path';
import { Readable } from 'node:stream';
import { pipeline } from 'node:stream/promises';
import { pathToFileURL } from 'node:url';
import type { Circuit } from '@zerc20/wallet-sdk';
import { Failure } from './errors.js';

/** Where everything is kept. */
export const home = () => process.env.ZERC20_HOME ?? join(homedir(), '.zerc20');

async function sha256Of(path: string): Promise<string> {
  const hash = createHash('sha256');
  await pipeline(createReadStream(path), hash);
  return hash.digest('hex');
}

/** Fetches `url` to `path`, unless it is there already. A download that stopped goes on from where it did, as a file
 * of gigabytes is not started over; it gets its name only once its SHA-256 is `sha256`, so what is at `path` is
 * whole and the file expected. `progress` hears the bytes so far and their total. */
export async function download(
  url: string,
  path: string,
  sha256: string,
  progress: (done: number, total: number) => void = () => {},
): Promise<void> {
  if (existsSync(path)) return;
  mkdirSync(dirname(path), { recursive: true });
  const part = `${path}.part`;
  const have = existsSync(part) ? statSync(part).size : 0;
  // as it is stored: a range and a length count the bytes of the file only where the server sends it unpacked
  const r = await fetch(url, {
    headers: { 'accept-encoding': 'identity', ...(have ? { range: `bytes=${have}-` } : {}) },
  });
  // 416: nothing past what is here, so it is whole and only its check is left
  if (r.status !== 416) {
    if (!r.ok || !r.body) throw new Failure(`${url}: HTTP ${r.status}`);
    // a server that ignores the range sends it all again
    const resumed = r.status === 206;
    let done = resumed ? have : 0;
    const total = done + Number(r.headers.get('content-length') ?? 0);
    const body = Readable.fromWeb(r.body);
    body.on('data', (chunk: Buffer) => progress((done += chunk.length), total));
    await pipeline(body, createWriteStream(part, { flags: resumed ? 'a' : 'w' }));
  }
  const got = await sha256Of(part);
  if (got !== sha256.toLowerCase()) {
    rmSync(part);
    throw new Failure(`${url} is not the file expected (its SHA-256 is ${got}): try again`);
  }
  renameSync(part, path);
}

/** A line on the terminal that follows a download, and nothing where no one watches. */
export function showProgress(label: string): (done: number, total: number) => void {
  if (!process.stderr.isTTY) return () => {};
  const mb = (n: number) => (n / 1e6).toFixed(n < 1e9 ? 1 : 0);
  let shown = 0;
  return (done, total) => {
    if (done < total && Date.now() - shown < 200) return;
    shown = Date.now();
    process.stderr.write(`\r${label} ${mb(done)} / ${mb(total)} MB${done >= total ? '\n' : ''}`);
  };
}

/** `circuit` read from this machine where its files are kept, and with `fetchMissing`, fetched first. The SDK keeps a
 * circuit only in memory, and a command is a process of its own: without this each payment downloads its 25 MB again.
 * The SDK checks the files against the same hashes whenever it reads them. */
export async function localCircuit(circuit: Circuit, fetchMissing: boolean): Promise<Circuit> {
  const local = async (url: string, sha256: string, ext: string) => {
    const path = join(home(), 'circuits', `${sha256}.${ext}`);
    if (fetchMissing && !url.startsWith('file:'))
      await download(url, path, sha256, showProgress(`Fetching the proving ${ext}`));
    return existsSync(path) ? pathToFileURL(path).href : url;
  };
  return {
    ...circuit,
    wasm: await local(circuit.wasm, circuit.wasmSha256, 'wasm'),
    zkey: await local(circuit.zkey, circuit.zkeySha256, 'zkey'),
  };
}
