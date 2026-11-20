#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { chmod, mkdir, readFile, rename, writeFile } from 'node:fs/promises';
import { dirname, resolve } from 'node:path';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';

const SCRIPT_DIR = dirname(fileURLToPath(import.meta.url));
const CONFIG_PATH = resolve(SCRIPT_DIR, '..', 'picus-toolchain.json');
const CONFIG_SCHEMA = 'zerc20-picus-toolchain/v1';
const PROVENANCE_SCHEMA = 'zerc20-picus-install-provenance/v1';
const EVIDENCE_SCHEMA = 'zerc20-picus-runtime-evidence/v1';

function fail(message) {
  throw new Error(message);
}

function isRecord(value) {
  return value !== null && typeof value === 'object' && !Array.isArray(value);
}

async function sha256File(path) {
  return createHash('sha256')
    .update(await readFile(path))
    .digest('hex');
}

async function loadJson(path, label) {
  let parsed;
  try {
    parsed = JSON.parse(await readFile(path, 'utf8'));
  } catch (error) {
    fail(`${label} is not valid JSON: ${error.message}`);
  }
  if (!isRecord(parsed)) {
    fail(`${label} must be a JSON object`);
  }
  return parsed;
}

async function loadConfig() {
  const config = await loadJson(CONFIG_PATH, 'Picus toolchain config');
  const expectedKeys = ['cargoPackage', 'cargoPath', 'repository', 'revision', 'schema', 'version'];
  const actualKeys = Object.keys(config).sort();
  if (JSON.stringify(actualKeys) !== JSON.stringify(expectedKeys)) {
    fail('Picus toolchain config has unexpected or missing fields');
  }
  if (config.schema !== CONFIG_SCHEMA) {
    fail(`unsupported Picus toolchain schema: ${String(config.schema)}`);
  }
  if (typeof config.repository !== 'string' || !/^https:\/\/github\.com\/[^/]+\/[^/]+\.git$/.test(config.repository)) {
    fail('Picus repository must be an HTTPS GitHub .git URL');
  }
  if (typeof config.revision !== 'string' || !/^[0-9a-f]{40}$/.test(config.revision)) {
    fail('Picus revision must be a lowercase full commit SHA');
  }
  if (typeof config.version !== 'string' || !/^[0-9]+\.[0-9]+\.[0-9]+$/.test(config.version)) {
    fail('Picus version must be an exact semantic version');
  }
  if (config.cargoPackage !== 'picus-cli') {
    fail('Picus cargo package must be picus-cli');
  }
  if (
    typeof config.cargoPath !== 'string' ||
    !/^[a-zA-Z0-9._/-]+$/.test(config.cargoPath) ||
    config.cargoPath.startsWith('/') ||
    config.cargoPath.split('/').includes('..')
  ) {
    fail('Picus cargo path must be a safe repository-relative path');
  }
  return {
    ...config,
    configSha256: await sha256File(CONFIG_PATH),
  };
}

function parseOptions(args, requiredNames) {
  const result = {};
  for (let index = 0; index < args.length; index += 2) {
    const name = args[index];
    const value = args[index + 1];
    if (!name?.startsWith('--') || value === undefined) {
      fail(`invalid option list near ${String(name)}`);
    }
    const key = name.slice(2);
    if (!requiredNames.includes(key) || key in result) {
      fail(`unknown or duplicate option: ${name}`);
    }
    result[key] = value;
  }
  for (const name of requiredNames) {
    if (!result[name]) {
      fail(`missing required option: --${name}`);
    }
  }
  return result;
}

function checkedCommand(command, args) {
  const result = spawnSync(command, args, {
    encoding: 'utf8',
    stdio: ['ignore', 'pipe', 'pipe'],
  });
  if (result.error) {
    fail(`failed to run ${command}: ${result.error.message}`);
  }
  if (result.status !== 0) {
    fail(`${command} ${args.join(' ')} failed: ${result.stderr.trim() || `exit ${result.status}`}`);
  }
  return result.stdout.trim();
}

async function writeJsonAtomic(path, value) {
  const absolute = resolve(path);
  await mkdir(dirname(absolute), { recursive: true });
  const temporary = `${absolute}.tmp-${process.pid}`;
  await writeFile(temporary, `${JSON.stringify(value, null, 2)}\n`, {
    encoding: 'utf8',
    flag: 'wx',
    mode: 0o644,
  });
  await rename(temporary, absolute);
  await chmod(absolute, 0o644);
}

async function verifyBinary(binaryPath, expectedVersion) {
  const absolute = resolve(binaryPath);
  const version = checkedCommand(absolute, ['--version']);
  if (version !== `picus ${expectedVersion}`) {
    fail(`Picus version mismatch: expected "picus ${expectedVersion}", got ${JSON.stringify(version)}`);
  }
  return {
    binarySha256: await sha256File(absolute),
    version,
  };
}

async function writeProvenance(args) {
  const options = parseOptions(args, ['binary', 'output', 'source-dir']);
  const config = await loadConfig();
  const sourceDir = resolve(options['source-dir']);
  const repository = checkedCommand('git', ['-C', sourceDir, 'remote', 'get-url', 'origin']);
  const revision = checkedCommand('git', ['-C', sourceDir, 'rev-parse', 'HEAD^{commit}']);
  if (repository !== config.repository) {
    fail(`Picus source remote mismatch: ${repository}`);
  }
  if (revision !== config.revision) {
    fail(`Picus source revision mismatch: ${revision}`);
  }
  if (checkedCommand('git', ['-C', sourceDir, 'status', '--porcelain']) !== '') {
    fail('Picus source checkout is dirty');
  }

  const binary = await verifyBinary(options.binary, config.version);
  const provenance = {
    schema: PROVENANCE_SCHEMA,
    repository: config.repository,
    revision: config.revision,
    version: config.version,
    cargoPackage: config.cargoPackage,
    configSha256: config.configSha256,
    binarySha256: binary.binarySha256,
    rustcVersion: checkedCommand('rustc', ['--version']),
    cargoVersion: checkedCommand('cargo', ['--version']),
    installedAt: new Date().toISOString(),
  };
  await writeJsonAtomic(options.output, provenance);
  process.stdout.write(
    `Picus ${config.version} installed from ${config.revision}; ` +
      `binary sha256 ${binary.binarySha256}; provenance ${resolve(options.output)}\n`,
  );
}

async function verifyInstall(args) {
  const options = parseOptions(args, ['binary', 'evidence', 'provenance']);
  const config = await loadConfig();
  const provenance = await loadJson(resolve(options.provenance), 'Picus install provenance');
  const requiredMatches = {
    schema: PROVENANCE_SCHEMA,
    repository: config.repository,
    revision: config.revision,
    version: config.version,
    cargoPackage: config.cargoPackage,
    configSha256: config.configSha256,
  };
  for (const [name, expected] of Object.entries(requiredMatches)) {
    if (provenance[name] !== expected) {
      fail(`Picus provenance ${name} mismatch: expected ${expected}, got ${String(provenance[name])}`);
    }
  }
  if (typeof provenance.binarySha256 !== 'string' || !/^[0-9a-f]{64}$/.test(provenance.binarySha256)) {
    fail('Picus provenance contains an invalid binary SHA-256');
  }

  const binary = await verifyBinary(options.binary, config.version);
  if (binary.binarySha256 !== provenance.binarySha256) {
    fail(`Picus binary SHA-256 mismatch: expected ${provenance.binarySha256}, ` + `got ${binary.binarySha256}`);
  }

  const evidence = {
    schema: EVIDENCE_SCHEMA,
    repository: config.repository,
    revision: config.revision,
    version: config.version,
    configSha256: config.configSha256,
    binarySha256: binary.binarySha256,
    verifiedAt: new Date().toISOString(),
  };
  await writeJsonAtomic(options.evidence, evidence);
  process.stdout.write(
    `Picus toolchain verified: revision=${config.revision} ` +
      `version=${config.version} binary_sha256=${binary.binarySha256} ` +
      `evidence=${resolve(options.evidence)}\n`,
  );
}

async function main() {
  const [command, ...args] = process.argv.slice(2);
  if (command === 'config-field') {
    if (args.length !== 1) {
      fail('usage: picus_toolchain.mjs config-field <field>');
    }
    const config = await loadConfig();
    const allowed = new Set(['cargoPackage', 'cargoPath', 'repository', 'revision', 'version']);
    if (!allowed.has(args[0])) {
      fail(`unsupported Picus config field: ${String(args[0])}`);
    }
    process.stdout.write(`${config[args[0]]}\n`);
    return;
  }
  if (command === 'check-config') {
    const config = await loadConfig();
    process.stdout.write(`${JSON.stringify(config)}\n`);
    return;
  }
  if (command === 'write-provenance') {
    await writeProvenance(args);
    return;
  }
  if (command === 'verify-install') {
    await verifyInstall(args);
    return;
  }
  fail('usage: picus_toolchain.mjs ' + '<check-config|config-field|write-provenance|verify-install>');
}

main().catch((error) => {
  console.error(`Picus toolchain check failed: ${error.message}`);
  process.exitCode = 1;
});
