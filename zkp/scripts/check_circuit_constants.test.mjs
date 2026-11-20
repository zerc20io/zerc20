import assert from 'node:assert/strict';
import { test } from 'node:test';

import { readNumericConstant, validateAddressPowWindows } from './check_circuit_constants.mjs';

function constants(addressBits, powBits, fieldBits = 254) {
  return `
function ADDRESS_BITS() { return ${addressBits}; }
function BURN_POW_BITS() { return ${powBits}; }
function FIELD_BIT_LENGTH() { return ${fieldBits}; }
`;
}

test('accepts disjoint address and canonical-digest PoW windows', () => {
  assert.deepEqual(validateAddressPowWindows(constants(160, 16)), {
    addressBits: 160,
    powBits: 16,
    fieldBits: 254,
  });
});

test('rejects overlapping address and canonical-digest PoW windows', () => {
  assert.throws(() => validateAddressPowWindows(constants(240, 16)), /overlaps the canonical-digest PoW window/);
});

test('fails closed when a required constant is not a numeric literal', () => {
  assert.throws(
    () => readNumericConstant('function ADDRESS_BITS() { return OTHER(); }', 'ADDRESS_BITS'),
    /unable to read numeric Circom constant ADDRESS_BITS/,
  );
});
