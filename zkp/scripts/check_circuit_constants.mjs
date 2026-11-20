#!/usr/bin/env node

import { readFile } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const scriptPath = fileURLToPath(import.meta.url);
const zkpDir = path.resolve(path.dirname(scriptPath), '..');
const constantsPath = path.join(zkpDir, 'circom', 'lib', 'constants.circom');

export function readNumericConstant(source, name) {
  const escaped = name.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
  const match = source.match(new RegExp(`function\\s+${escaped}\\(\\)\\s*\\{\\s*return\\s+([0-9]+)\\s*;\\s*\\}`, 'm'));
  if (!match) {
    throw new Error(`unable to read numeric Circom constant ${name}`);
  }
  return Number(match[1]);
}

export function validateAddressPowWindows(source) {
  const addressBits = readNumericConstant(source, 'ADDRESS_BITS');
  const powBits = readNumericConstant(source, 'BURN_POW_BITS');
  const fieldBits = readNumericConstant(source, 'FIELD_BIT_LENGTH');

  if (!Number.isSafeInteger(addressBits) || addressBits <= 0 || addressBits > fieldBits) {
    throw new Error(`ADDRESS_BITS must be in [1, ${fieldBits}], got ${addressBits}`);
  }
  if (!Number.isSafeInteger(powBits) || powBits <= 0 || powBits > fieldBits) {
    throw new Error(`BURN_POW_BITS must be in [1, ${fieldBits}], got ${powBits}`);
  }
  if (addressBits + powBits > fieldBits) {
    throw new Error(
      `burn address projection overlaps the canonical-digest PoW window: ` +
        `${addressBits} + ${powBits} > ${fieldBits}`,
    );
  }

  return { addressBits, powBits, fieldBits };
}

if (process.argv[1] && path.resolve(process.argv[1]) === scriptPath) {
  try {
    const result = validateAddressPowWindows(await readFile(constantsPath, 'utf8'));
    console.log(
      `burn address/PoW windows are disjoint: address=${result.addressBits}, ` +
        `pow=${result.powBits}, field=${result.fieldBits}`,
    );
  } catch (error) {
    console.error(error instanceof Error ? error.message : String(error));
    process.exitCode = 1;
  }
}
