// `npm run demo`, with scripts/dev-stack.sh running: the page opens wallets on the network the stack wrote. After
// restarting the stack, restart this too. NETWORK=<network.json> opens a deployed network instead, with the browser's
// wallet, or test keys in DEMO_KEYS=<0x…,…>; either needs gas.

import { existsSync, readFileSync, statSync } from 'node:fs';
import { defineConfig } from 'vite';

const path = process.env.NETWORK ?? new URL('../../../target/dev-stack/network.json', import.meta.url);
if (!existsSync(path)) throw new Error(`no ${path}: start scripts/dev-stack.sh first, or set NETWORK`);
const network = readFileSync(path, 'utf8');
const storage: string = JSON.parse(network).storage.host;

export default defineConfig({
  define: {
    __NETWORK__: JSON.stringify(network),
    // each stack is a new chain and canister, so wallets saved against an earlier one are dropped
    __RUN__: JSON.stringify(String(statSync(path).mtimeMs)),
    __KEYS__: JSON.stringify(process.env.DEMO_KEYS ?? ''),
  },
  server: {
    // the PocketIC gateway sends no CORS headers: the page reaches the storage canister through this server
    proxy: storage.startsWith('http:') ? { '/api': storage } : undefined,
    // the SDK's source and wasm, and the storage SDK it links to
    fs: { allow: ['../../..'] },
  },
});
