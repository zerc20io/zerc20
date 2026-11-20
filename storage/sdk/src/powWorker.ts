// solvePow's search, in a Web Worker: off the page's thread, it never needs to yield.

import { findNonce } from './wire.js';

onmessage = async ({ data }: MessageEvent<{ digest: Uint8Array; bits: number }>) =>
  postMessage(await findNonce(data.digest, data.bits, Infinity));
