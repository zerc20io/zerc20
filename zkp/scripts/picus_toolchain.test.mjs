import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { chmod, mkdtemp, readFile, rm, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import test from 'node:test';

const SCRIPT_DIR = dirname(fileURLToPath(import.meta.url));
const TOOLCHAIN = resolve(SCRIPT_DIR, 'picus_toolchain.mjs');
const CONFIG_PATH = resolve(SCRIPT_DIR, '..', 'picus-toolchain.json');

function run(args) {
  return spawnSync(process.execPath, [TOOLCHAIN, ...args], {
    encoding: 'utf8',
  });
}

test('Picus toolchain config uses an immutable full revision', () => {
  const result = run(['check-config']);
  assert.equal(result.status, 0, result.stderr);
  const config = JSON.parse(result.stdout);
  assert.match(config.revision, /^[0-9a-f]{40}$/);
  assert.match(config.configSha256, /^[0-9a-f]{64}$/);
  assert.equal(config.repository, 'https://github.com/chyanju/picus.git');
  assert.equal(config.version, '1.8.22');
});

test('Picus runtime verification binds provenance to the binary hash', async (t) => {
  const directory = await mkdtemp(join(tmpdir(), 'zerc20-picus-toolchain-'));
  t.after(() => rm(directory, { recursive: true, force: true }));

  const binary = join(directory, 'picus');
  await writeFile(binary, '#!/bin/sh\nprintf "picus 1.8.22\\\\n"\n');
  await chmod(binary, 0o755);

  const config = JSON.parse(await readFile(CONFIG_PATH, 'utf8'));
  const configSha256 = createHash('sha256')
    .update(await readFile(CONFIG_PATH))
    .digest('hex');
  const binarySha256 = createHash('sha256')
    .update(await readFile(binary))
    .digest('hex');
  const provenance = join(directory, 'provenance.json');
  await writeFile(
    provenance,
    `${JSON.stringify({
      schema: 'zerc20-picus-install-provenance/v1',
      repository: config.repository,
      revision: config.revision,
      version: config.version,
      cargoPackage: config.cargoPackage,
      configSha256,
      binarySha256,
      rustcVersion: 'rustc test',
      cargoVersion: 'cargo test',
      installedAt: new Date().toISOString(),
    })}\n`,
  );

  const evidence = join(directory, 'evidence.json');
  const valid = run(['verify-install', '--binary', binary, '--evidence', evidence, '--provenance', provenance]);
  assert.equal(valid.status, 0, valid.stderr);
  assert.match(valid.stdout, new RegExp(config.revision));
  assert.deepEqual(
    {
      ...JSON.parse(await readFile(evidence, 'utf8')),
      verifiedAt: '<redacted>',
    },
    {
      schema: 'zerc20-picus-runtime-evidence/v1',
      repository: config.repository,
      revision: config.revision,
      version: config.version,
      configSha256,
      binarySha256,
      verifiedAt: '<redacted>',
    },
  );

  await writeFile(binary, '# tampered\n', { flag: 'a' });
  const tampered = run(['verify-install', '--binary', binary, '--evidence', evidence, '--provenance', provenance]);
  assert.notEqual(tampered.status, 0);
  assert.match(tampered.stderr, /binary SHA-256 mismatch/);
});

test('Picus runtime verification rejects a different source revision', async (t) => {
  const directory = await mkdtemp(join(tmpdir(), 'zerc20-picus-revision-'));
  t.after(() => rm(directory, { recursive: true, force: true }));

  const binary = join(directory, 'picus');
  await writeFile(binary, '#!/bin/sh\nprintf "picus 1.8.22\\\\n"\n');
  await chmod(binary, 0o755);
  const config = JSON.parse(await readFile(CONFIG_PATH, 'utf8'));
  const provenance = join(directory, 'provenance.json');
  await writeFile(
    provenance,
    `${JSON.stringify({
      schema: 'zerc20-picus-install-provenance/v1',
      repository: config.repository,
      revision: '0'.repeat(40),
      version: config.version,
      cargoPackage: config.cargoPackage,
      configSha256: createHash('sha256')
        .update(await readFile(CONFIG_PATH))
        .digest('hex'),
      binarySha256: createHash('sha256')
        .update(await readFile(binary))
        .digest('hex'),
    })}\n`,
  );

  const result = run([
    'verify-install',
    '--binary',
    binary,
    '--evidence',
    join(directory, 'evidence.json'),
    '--provenance',
    provenance,
  ]);
  assert.notEqual(result.status, 0);
  assert.match(result.stderr, /provenance revision mismatch/);
});
