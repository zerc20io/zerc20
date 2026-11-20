// The same fixtures as the canister's `wire_fixtures` test (canister/src/lib.rs).

import { Principal } from '@icp-sdk/core/principal';
import { sha256 } from '@noble/hashes/sha2.js';
import { expect, test } from 'vitest';
import type { Action } from '../src/candid.js';
import { hex, utf8 } from '../src/crypto.js';
import { actionsDigest, powOk, registerDigest, registerMessage, solvePow, vetkdInput } from '../src/wire.js';

test('wire bytes match the canister', () => {
  const canister = Principal.fromText('rrkah-fqaaa-aaaaa-aaaaq-cai');
  const fill = (n: number, len: number) => new Uint8Array(len).fill(n);
  const [address, notifyKey, expiry] = [fill(0x11, 20), fill(0x44, 32), 1_760_000_000_123_456_792n];
  const registration = {
    address,
    public_key: fill(0x33, 32),
    notify_key: notifyKey,
    escrow: fill(0x55, 5),
    expiry_ns: expiry,
    signature: new Uint8Array(),
  };
  const actions: Action[] = [
    {
      OpenChannel: {
        inbox: fill(1, 32),
        enc_announcement: fill(2, 3),
        outgoing_id: fill(3, 32),
        enc_outgoing: fill(4, 5),
      },
    },
    { Put: { kind: { Lane: null }, id: fill(5, 32), data: fill(6, 7) } },
  ];
  const sha = (text: string) => hex(sha256(utf8(text)));
  expect([
    hex(vetkdInput(address, notifyKey)),
    sha(registerMessage(canister, registration)),
    hex(registerDigest(registration)),
    hex(actionsDigest(actions)),
  ]).toEqual([
    '11111111111111111111111111111111111111114444444444444444444444444444444444444444444444444444444444444444',
    'bfee87e253dcdf86a0c0de307c8c6963bf0b444f3e013f60f338ad774a843ebb',
    '1a20c636defbfa95a28b75ffd3fdbbd0f751382619c202ddea752e2f77be6050',
    'b1042d9cf44b92781350c9175b5abfd916b1744a051ee78905a272d8b0d92f1b',
  ]);
  // This nonce's PoW hash has exactly one leading zero bit.
  const digest = registerDigest(registration);
  expect([powOk(digest, 0n, 1), powOk(digest, 0n, 2)]).toEqual([true, false]);
});

test('the solver finds the first nonce that passes', async () => {
  const digest = new Uint8Array(32).fill(9);
  const nonce = await solvePow(digest, 12);
  expect(powOk(digest, nonce, 12)).toBe(true);
  for (let n = 0n; n < nonce; n++) expect(powOk(digest, n, 12)).toBe(false);
});
