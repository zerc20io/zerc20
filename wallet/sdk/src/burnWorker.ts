// Runs blocks of burn address searches off the main thread, one at a time: core.ts keeps a pool of these, Web Workers
// in a browser and worker threads in Node.

import { type BurnAnswer, type BurnBlock, initCore, runBlock } from './core.js';

async function answer(b: BurnBlock): Promise<BurnAnswer> {
  try {
    await initCore();
    return { burn: runBlock(b) };
  } catch (e) {
    return { error: e instanceof Error ? e.message : String(e) };
  }
}

if (typeof self !== 'undefined') {
  self.onmessage = async ({ data }: MessageEvent<BurnBlock>) => postMessage(await answer(data));
} else {
  // a variable, so that bundlers for the browser leave Node's module alone
  const threads = 'node:worker_threads';
  type Port = { on(event: 'message', f: (b: BurnBlock) => void): void; postMessage(a: BurnAnswer): void };
  void import(/* @vite-ignore */ threads).then(({ parentPort }: { parentPort: Port }) =>
    parentPort.on('message', (b) => void answer(b).then((a) => parentPort.postMessage(a))),
  );
}
