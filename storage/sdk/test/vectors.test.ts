// What another implementation of the owner's writes must reproduce byte for byte: notes to self, burn blocks and
// points of sale sealed into the own lane, a point of sale's lane key, a passkey's seed slots, and a submission's
// proof of work. Values that use a random nonce are checked by opening them. UPDATE=1 rewrites the file.

import { existsSync, readFileSync, writeFileSync } from 'node:fs';
import { Principal } from '@icp-sdk/core/principal';
import { expect, test } from 'vitest';
import type { Action } from '../src/candid.js';
import { hex, open, seal, unhex } from '../src/crypto.js';
import {
  burnBlockPlaintext,
  notePlaintext,
  ownKey,
  ownReceiptPlaintext,
  passkeySeedId,
  passkeySeedKey,
  passkeySeedPlaintext,
  posKey,
  posLanePlaintext,
  readLaneRecord,
  sealKey,
  slotId,
} from '../src/formats.js';
import { viewKey } from '../src/viewKey.js';
import { actionsDigest, powOk, solvePow } from '../src/wire.js';

const FILE = new URL('./vectors.json', import.meta.url);
const fill = (n: number, len: number) => new Uint8Array(len).fill(n);

test('the owner-only formats match test/vectors.json', async () => {
  const rootSeed = fill(7, 32);
  const address = fill(0x11, 20);
  const canister = Principal.fromText('rrkah-fqaaa-aaaaa-aaaaq-cai');
  const view = viewKey(rootSeed, address, canister);
  const prf = fill(0x66, 32);
  const own = ownKey(view.seed);
  const opening = { chainId: 31337n, tokenId: 2, value: unhex(`00${'0'.repeat(60)}2a`), noteSalt: fill(5, 32) };
  const value = (n: number) => fill(0, 32).fill(n, 31);
  const note = notePlaintext(opening, {
    receipt: { kind: 'merged', amount: opening.value, fee: value(3), counterparty: fill(0, 20) },
  })!;
  const block = burnBlockPlaintext({ chainId: 31337n, tokenId: 2, first: 2 ** 31, salts: [fill(8, 32), fill(9, 32)] });
  // a later version's block, with a field after its body that this one passes over: both sides must still read it
  const extended = block.slice();
  extended.set([0xab, 0xcd], 10 + 2 * 32);
  // a payment's zero-value change with its receipt, a rage exit's own receipt, and a deposit address's
  const receipt = { kind: 'withdrawn' as const, amount: value(40), fee: value(2), counterparty: fill(0x22, 20) };
  const change = notePlaintext({ ...opening, value: fill(0, 32) }, { receipt })!;
  const returned = ownReceiptPlaintext({
    kind: 'returned',
    chainId: 31337n,
    tokenId: 2,
    burnAddress: fill(0x33, 20),
    index: 4097,
    recipient: fill(0x44, 20),
    amount: value(9),
    txHash: fill(0x55, 32),
  });
  const registered = ownReceiptPlaintext({
    kind: 'deposit-address',
    chainId: 31337n,
    tokenId: 2,
    burnAddress: fill(0x33, 20),
    depositAddress: fill(0x66, 20),
    args: {
      fee: value(7),
      feeRecipient: fill(0x77, 20),
      refundSigner: fill(0x88, 20),
      referrer: fill(0x99, 20),
      referralBps: 300,
    },
  });
  const [noteId, blockId] = [slotId(own, 31337n, 4), slotId(own, 31337n, 6)];
  const fixed = {
    rootSeed: hex(rootSeed),
    address: hex(address),
    canister: canister.toText(),
    viewSeed: hex(view.seed),
    ownKey: hex(own),
    noteId: hex(noteId),
    sealKey: hex(sealKey(own)),
    notePlaintext: hex(note),
    blockId: hex(blockId),
    burnBlockPlaintext: hex(block),
    extendedBurnBlockPlaintext: hex(extended),
    receiptChangePlaintext: hex(change),
    returnedPlaintext: hex(returned),
    depositAddressPlaintext: hex(registered),
    posKey: hex(posKey(view.seed, 3)),
    posLanePlaintext: hex(posLanePlaintext(3)),
    passkeyPrf: hex(prf),
    passkeySeedId: hex(passkeySeedId(prf, canister, 1)),
    passkeySeedKey: hex(passkeySeedKey(prf, canister)),
    passkeySeedPlaintext: hex(passkeySeedPlaintext(rootSeed)),
  };
  expect(readLaneRecord('own', 31337n, 6, 0n, extended)).toEqual(readLaneRecord('own', 31337n, 6, 0n, block));

  if (process.env.UPDATE === '1' || !existsSync(FILE)) {
    const sealedBlock = seal(sealKey(own), blockId, block);
    const actions: Action[] = [{ Put: { kind: { Lane: null }, id: blockId, data: sealedBlock } }];
    const digest = actionsDigest(actions);
    const vectors = {
      ...fixed,
      sealedNote: hex(seal(sealKey(own), noteId, note)),
      sealedBurnBlock: hex(sealedBlock),
      putBurnDigest: hex(digest),
      pow16Nonce: (await solvePow(digest, 16)).toString(),
    };
    writeFileSync(FILE, `${JSON.stringify(vectors, null, 2)}\n`);
  }
  const v = JSON.parse(readFileSync(FILE, 'utf8')) as Record<string, string>;
  expect(Object.fromEntries(Object.keys(fixed).map((k) => [k, v[k]]))).toEqual(fixed);
  expect(hex(open(sealKey(own), noteId, unhex(v.sealedNote!))!)).toBe(fixed.notePlaintext);
  expect(hex(open(sealKey(own), blockId, unhex(v.sealedBurnBlock!))!)).toBe(fixed.burnBlockPlaintext);
  const actions: Action[] = [{ Put: { kind: { Lane: null }, id: blockId, data: unhex(v.sealedBurnBlock!) } }];
  expect(hex(actionsDigest(actions))).toBe(v.putBurnDigest);
  expect(powOk(unhex(v.putBurnDigest!), BigInt(v.pow16Nonce!), 16)).toBe(true);
});
