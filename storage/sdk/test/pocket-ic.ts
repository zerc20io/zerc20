// The PocketIC the e2e tests and the demo run the canister in: the server @dfinity/pic installed with itself, never the
// one POCKET_IC_BIN names. A shell may set that for another project, to an older server that speaks another version of
// the protocol and holds no vetKD test key, so that every registration fails at vetkd_public_key.

import { createRequire } from 'node:module';
import { dirname, resolve } from 'node:path';
import { PocketIc, PocketIcServer, SubnetStateType } from '@dfinity/pic';

/** Where @dfinity/pic puts its server: next to its `dist`, as its own default past POCKET_IC_BIN. */
const SERVER = resolve(dirname(createRequire(import.meta.url).resolve('@dfinity/pic')), '..', 'pocket-ic');

/** A PocketIC server, the one @dfinity/pic installed; `ttl` keeps it up that many seconds without calls. */
export const startServer = (ttl?: number): Promise<PocketIcServer> =>
  PocketIcServer.start({ binPath: SERVER, ...(ttl !== undefined && { ttl }) });

/** A PocketIC instance on `server`: an application subnet for the canister, and the subnet that holds the threshold
 * keys, `test_key_1` among them, which the canister's vetKD calls name. */
export const createPic = (server: string): Promise<PocketIc> =>
  PocketIc.create(server, {
    application: [{ state: { type: SubnetStateType.New } }],
    testThresholdKeys: { state: { type: SubnetStateType.New } },
  });
