// `npm run demo`: a fresh zerc20_storage canister in PocketIC, behind a Vite dev server for the
// browser demo. Build the wasm first (see the README).

import { randomUUID } from 'node:crypto';
import { existsSync } from 'node:fs';
import { IDL } from '@icp-sdk/core/candid';
import { Principal } from '@icp-sdk/core/principal';
import { createServer } from 'vite';
import { createPic, startServer } from '../test/pocket-ic.ts';

const wasm = new URL('../../target/wasm32-unknown-unknown/release/zerc20_storage.wasm', import.meta.url).pathname;
if (!existsSync(wasm)) {
  console.error('Build the canister first: cargo build --release --target wasm32-unknown-unknown -p zerc20_storage');
  process.exit(1);
}

// Calls through the gateway do not count as server activity, so keep it up until Ctrl+C.
const server = await startServer(7 * 24 * 3600);
const pic = await createPic(server.getUrl());
const [subnet] = await pic.getApplicationSubnets();
const canisterId = await pic.createCanister({ targetSubnetId: subnet!.id });
const InitArgs = IDL.Record({ auditor: IDL.Principal, vetkd_key_name: IDL.Text });
// No audits in the demo: no one calls as the management canister.
const arg = IDL.encode([InitArgs], [{ auditor: Principal.managementCanister(), vetkd_key_name: 'test_key_1' }]);
await pic.installCode({ canisterId, wasm, arg });
// Live, so the clock follows wall time and signed expiries check against it.
const gateway = `http://127.0.0.1:${await pic.makeLive()}`;

const vite = await createServer({
  configFile: false,
  root: new URL('.', import.meta.url).pathname,
  // The page and the gateway share an origin, so the gateway needs no CORS.
  server: { proxy: { '/api': gateway } },
  define: {
    __CANISTER_ID__: JSON.stringify(canisterId.toText()),
    // Every run starts from an empty canister, so states stored by earlier runs must not be reused.
    __RUN_ID__: JSON.stringify(randomUUID()),
  },
});
await vite.listen();
vite.printUrls();
console.log(`  canister ${canisterId.toText()}, PocketIC gateway ${gateway}`);

process.on('SIGINT', async () => {
  await vite.close();
  await pic.tearDown();
  await server.stop();
  process.exit(0);
});
