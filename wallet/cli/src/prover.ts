// A merge prover on this machine: the node's own binary, with the keys it proves with fetched and checked first. A
// wallet here that merges with `--prover local` seals its witness to it rather than to the network's.

import { spawn } from 'node:child_process';
import { createRequire } from 'node:module';
import { totalmem } from 'node:os';
import { join } from 'node:path';
import { Failure, Usage } from './errors.js';
import { download, home, showProgress } from './files.js';
import { MERGE_KEYS, mergeKeyUrl } from './mergeKeys.js';

/** The machines a release brings a prover for, each as a package of its own that npm installs where it fits. */
const SHIPPED = ['darwin-arm64', 'linux-x64', 'linux-arm64'];

/** The prover's binary: one named, else the one this install brought for this machine. */
function binary(): string {
  if (process.env.ZERC20_MERGE_PROVER_BIN) return process.env.ZERC20_MERGE_PROVER_BIN;
  const target = `${process.platform}-${process.arch}`;
  try {
    return createRequire(import.meta.url).resolve(`@zerc20/merge-prover-${target}/zerc20-merge-prover`);
  } catch {
    const own = 'name a `zerc20-merge-prover` built from the source in ZERC20_MERGE_PROVER_BIN';
    throw new Failure(
      SHIPPED.includes(target)
        ? `the merge prover for ${target} is not in this install, as after --omit=optional or in a checkout of the ` +
            `source: install @zerc20/cli again, or ${own}`
        : `no merge prover ships for ${target}, only for ${SHIPPED.join(', ')}: ${own}`,
    );
  }
}

/** Runs the prover on `port` of this machine until it stops or is stopped. `interrupted` is told how to stop it. */
export async function proverStart(port: string, interrupted: (stop: () => void) => void): Promise<void> {
  if (!/^\d+$/.test(port)) throw new Usage(`--port ${port} is not a port`);
  const bin = binary();
  const dir = join(home(), 'merge', MERGE_KEYS.setup);
  for (const key of [MERGE_KEYS.vk, MERGE_KEYS.pk]) {
    await download(mergeKeyUrl(key.file), join(dir, key.file), key.sha256, showProgress(`Fetching ${key.file}`));
  }
  const gb = totalmem() / 2 ** 30;
  if (gb < 16) console.error(`This machine has ${gb.toFixed(0)} GB of memory: proving takes about 16 GB.`);
  // only what the prover reads: nothing of this shell's can switch it to a development mode
  const env = {
    SELF_HOSTED: '1',
    MERGE_PK_SHA256: MERGE_KEYS.pk.sha256,
    MERGE_VK_SHA256: MERGE_KEYS.vk.sha256,
    ARTIFACTS_DIR: dir,
    LISTEN: `127.0.0.1:${port}`,
    ...(process.env.RUST_LOG ? { RUST_LOG: process.env.RUST_LOG } : {}),
  };
  const child = spawn(bin, [], { env, stdio: 'inherit' });
  interrupted(() => child.kill());
  const ended = new Promise<number>((resolve, reject) => {
    child.on('error', reject);
    child.on('exit', (code) => resolve(code ?? 1));
  });
  const url = `http://127.0.0.1:${port}`;
  const ready = async () => {
    for (;;) {
      await new Promise((r) => setTimeout(r, 2000));
      const status = await fetch(`${url}/status`)
        .then((r) => r.json() as Promise<{ mergeKey?: boolean }>)
        .catch(() => null);
      if (status?.mergeKey) break;
    }
    const flag = port === '3006' ? 'local' : url;
    console.error(`Ready. Merge through it with: zerc20 merge <token> --prover ${flag}`);
    return ended;
  };
  process.exitCode = await Promise.race([ended, ready()]);
}
