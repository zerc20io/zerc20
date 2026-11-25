import { Principal } from '@icp-sdk/core/principal';
import { DerivedPublicKey, TransportSecretKey } from '@icp-sdk/vetkeys';
import { expect, test } from 'vitest';
import { randomBytes, seal, sealTo, unhex } from '../src/crypto.js';
import {
  BURN_BLOCK,
  FR_BE,
  burnBlockPlaintext,
  channelKey,
  channelPlaintext,
  codeKey,
  decodeCode,
  depositPlaintext,
  encodeCode,
  notePlaintext,
  ownReceiptPlaintext,
  passkeySeedId,
  passkeySeedPlaintext,
  posKey,
  posLanePlaintext,
  readChannel,
  readLaneRecord,
  readPasskeySeed,
  readTarget,
  targetPlaintext,
} from '../src/formats.js';
import { emptyState, exportState, importState } from '../src/sync.js';
import { type ViewKey, openEscrow, viewKey } from '../src/viewKey.js';
import { BLOB_LEN } from '../src/wire.js';

const fill = (n: number, len: number) => new Uint8Array(len).fill(n);
const opening = { chainId: 1n, tokenId: 7, value: fill(0, 32), noteSalt: fill(1, 32) };
opening.value[31] = 42;
const read = (lane: 'channel' | 'code' | 'own' | 'pos', plain: Uint8Array) => readLaneRecord(lane, 1n, 3, 5n, plain);

test('channel keys bind the inbox and the claimed payer', () => {
  // A seed copied into another inbox, or claimed by another payer, opens nothing.
  const key = channelKey(fill(7, 32), fill(1, 32), fill(2, 20));
  expect(channelKey(fill(7, 32), fill(3, 32), fill(2, 20))).not.toEqual(key);
  expect(channelKey(fill(7, 32), fill(1, 32), fill(4, 20))).not.toEqual(key);
});

test('every record fills exactly one blob', () => {
  const key = fill(0, 32);
  const slot = (plain: Uint8Array) => seal(key, new Uint8Array(), plain).length;
  const code = { chainId: 1n, tokenId: 3, burnAddress: fill(4, 20), publicKey: fill(5, 32), key: fill(6, 32) };
  for (const plain of [
    notePlaintext(opening)!,
    notePlaintext(opening, { payer: fill(2, 20) })!,
    notePlaintext(opening, {
      receipt: { kind: 'sent', amount: opening.value, fee: opening.value, counterparty: fill(2, 20) },
    })!,
    depositPlaintext(1, opening.value, fill(1, 32), fill(8, 20))!,
    burnBlockPlaintext({ chainId: 1n, tokenId: 1, first: 0, salts: [fill(1, 32)] }),
    posLanePlaintext(3),
    targetPlaintext({ address: fill(5, 20), notifyKey: fill(6, 32) }),
    targetPlaintext(code),
    passkeySeedPlaintext(fill(9, 32)),
  ]) {
    expect(slot(plain)).toBe(BLOB_LEN);
  }
  expect(sealTo(randomBytes(32), 'announce', fill(1, 32), channelPlaintext(fill(2, 20), fill(3, 32)))!.length).toBe(
    BLOB_LEN,
  );
});

test('notes round trip in each lane, with what only that lane holds', () => {
  const receipt = { kind: 'merged' as const, amount: opening.value, fee: fill(0, 32), counterparty: fill(0, 20) };
  const sent = notePlaintext(opening)!;
  expect(read('channel', sent)).toEqual({ kind: 'note', slotIndex: 3, atNs: 5n, opening });
  const paid = notePlaintext(opening, { payer: fill(2, 20) })!;
  expect(read('code', paid)).toEqual({ kind: 'note', slotIndex: 3, atNs: 5n, opening, payer: fill(2, 20) });
  const merged = notePlaintext(opening, { receipt })!;
  expect(read('own', merged)).toEqual({ kind: 'note', slotIndex: 3, atNs: 5n, opening, receipt });

  // a code's note names its payer, a note to self says what it is; each is read in its own lane only
  for (const [plain, lane] of [
    [sent, 'channel'],
    [paid, 'code'],
    [merged, 'own'],
  ] as const) {
    for (const other of ['channel', 'code', 'own', 'pos'] as const)
      if (other !== lane) expect(read(other, plain)).toBeNull();
  }
});

test('values and salts stay in range', () => {
  expect(notePlaintext({ ...opening, value: fill(1, 32) })).toBeNull(); // value ≥ 2^248
  expect(notePlaintext({ ...opening, noteSalt: FR_BE })).toBeNull(); // salt = p
  expect(notePlaintext(opening, { payer: fill(2, 19) })).toBeNull();
  const salted = notePlaintext(opening)!;
  salted.set(FR_BE, 36);
  expect(read('channel', salted)).toBeNull();
});

test('deposits are told in channels only, and burn blocks kept in the own and point of sale lanes only', () => {
  const deposit = depositPlaintext(1, opening.value, fill(1, 32), fill(8, 20))!;
  expect(read('channel', deposit)).toEqual({
    kind: 'deposit',
    slotIndex: 3,
    atNs: 5n,
    chainId: 1n,
    tokenId: 1,
    value: opening.value,
    burnSalt: fill(1, 32),
    burnAddress: fill(8, 20),
  });
  expect(depositPlaintext(1, opening.value, fill(1, 32), fill(8, 19))).toBeNull();
  expect(read('code', deposit)).toBeNull();
  expect(read('own', deposit)).toBeNull();
  expect(read('pos', deposit)).toBeNull();

  for (let n = 1; n <= BURN_BLOCK; n++) {
    const block = { chainId: 1n, tokenId: 2, first: 6, salts: Array.from({ length: n }, (_, i) => fill(i + 1, 32)) };
    expect(read('own', burnBlockPlaintext(block))).toEqual({ kind: 'burn-block', slotIndex: 3, atNs: 5n, ...block });
  }
  const block = burnBlockPlaintext({ chainId: 1n, tokenId: 2, first: 0, salts: [fill(1, 32)] });
  expect(read('pos', block)).toMatchObject({ kind: 'burn-block', first: 0, salts: [fill(1, 32)] });
  expect(read('channel', block)).toBeNull();
  expect(read('code', block)).toBeNull();
  expect(() => burnBlockPlaintext({ chainId: 1n, tokenId: 2, first: 0, salts: [] })).toThrow();
  expect(() =>
    burnBlockPlaintext({ chainId: 1n, tokenId: 2, first: 0, salts: Array(BURN_BLOCK + 1).fill(fill(1, 32)) }),
  ).toThrow();
  const counted = block.slice();
  counted[9] = 0; // no salts
  expect(read('own', counted)).toBeNull();
});

test('points of sale are recorded in the own lane only, each with a lane of its own', () => {
  expect(read('own', posLanePlaintext(3))).toEqual({ kind: 'pos-lane', slotIndex: 3, atNs: 5n, n: 3 });
  for (const lane of ['channel', 'code', 'pos'] as const) expect(read(lane, posLanePlaintext(3))).toBeNull();
  const seed = fill(7, 32);
  expect(posKey(seed, 0)).not.toEqual(posKey(seed, 1));
  expect(posKey(seed, 0)).not.toEqual(codeKey(seed, 0n, 0, 0));
});

test('receipts: on a note to self, and of their own, each where it belongs', () => {
  const value = (n: number) => fill(0, 32).fill(n, 31);
  const receipt = { kind: 'sent-to-code' as const, amount: value(40), fee: value(2), counterparty: fill(9, 20) };
  const change = notePlaintext({ ...opening, value: fill(0, 32) }, { receipt })!;
  expect(read('own', change)).toMatchObject({ kind: 'note', receipt });
  expect(notePlaintext(opening, { receipt: { ...receipt, fee: fill(1, 32) } })).toBeNull(); // ≥ 2^248
  // a later version's kind: the receipt is passed over, the note, perhaps spendable change, kept
  const later = change.slice();
  later[68] = 9;
  expect(read('own', later)).toMatchObject({ kind: 'note' });
  expect(read('own', later)).not.toHaveProperty('receipt');

  const head = { chainId: 1n, tokenId: 2, burnAddress: fill(3, 20) };
  const returned = {
    ...head,
    kind: 'returned' as const,
    index: 2 ** 40,
    recipient: fill(4, 20),
    amount: value(7),
    txHash: fill(5, 32),
  };
  const untold = { ...head, kind: 'deposit-address' as const, depositAddress: fill(6, 20) };
  const args = { fee: value(8), feeRecipient: fill(9, 20), refundSigner: fill(10, 20), referrer: fill(11, 20) };
  const registered = { ...untold, args: { ...args, referralBps: 0xfffe } };
  for (const r of [returned, registered, untold]) {
    expect(read('own', ownReceiptPlaintext(r))).toEqual({ ...r, slotIndex: 3, atNs: 5n });
    expect(read('channel', ownReceiptPlaintext(r))).toBeNull();
  }
  // a fee of zero is told, as the byte before it says
  const free = { ...registered, args: { ...registered.args, fee: fill(0, 32) } };
  expect(read('own', ownReceiptPlaintext(free))).toMatchObject({ args: { fee: fill(0, 32) } });
  expect(() => ownReceiptPlaintext({ ...registered, depositAddress: fill(6, 19) })).toThrow();
  for (const wrong of [{ fee: fill(1, 32) }, { referrer: fill(11, 19) }, { referralBps: 0x10000 }]) {
    expect(() => ownReceiptPlaintext({ ...registered, args: { ...registered.args, ...wrong } })).toThrow();
  }
});

test('what follows a body is passed over, and a type this version does not know drops the record', () => {
  const later = posLanePlaintext(3);
  later.set([9, 9], 5); // a later version's field
  expect(read('own', later)).toEqual({ kind: 'pos-lane', slotIndex: 3, atNs: 5n, n: 3 });
  const unknown = notePlaintext(opening)!;
  unknown[0] = 0x7f;
  expect(read('channel', unknown)).toBeNull();
  expect(read('channel', notePlaintext(opening)!.subarray(1))).toBeNull();
});

test('codes are checksummed text, and targets and announcements round trip', () => {
  const code = { chainId: 1n, tokenId: 3, burnAddress: fill(4, 20), publicKey: fill(5, 32), key: fill(6, 32) };
  const text = encodeCode(code);
  expect(text.startsWith('zerc201')).toBe(true);
  expect(decodeCode(text)).toEqual(code);
  expect(decodeCode(` ${text.toUpperCase()}\n`)).toEqual(code);
  const typo = text.slice(0, 20) + (text[20] === 'q' ? 'p' : 'q') + text.slice(21);
  expect(decodeCode(typo)).toBeNull();
  expect(decodeCode(`0x${'11'.repeat(96)}`)).toBeNull();
  expect(decodeCode('')).toBeNull();
  expect(() => encodeCode({ ...code, burnAddress: fill(4, 32) })).toThrow();

  for (const target of [{ address: fill(5, 20), notifyKey: fill(6, 32) }, code]) {
    expect(readTarget(targetPlaintext(target))).toEqual(target);
  }
  expect(readChannel(channelPlaintext(fill(2, 20), fill(3, 32)))).toEqual({ payer: fill(2, 20), seed: fill(3, 32) });
  expect(readTarget(channelPlaintext(fill(2, 20), fill(3, 32)))).toBeNull();
});

test('passkey seeds round trip, in slots of their own for each passkey, index and canister', () => {
  const [prf, canister] = [fill(1, 32), Principal.fromText('rrkah-fqaaa-aaaaa-aaaaq-cai')];
  expect(readPasskeySeed(passkeySeedPlaintext(fill(2, 32)))).toEqual(fill(2, 32));
  expect(readPasskeySeed(targetPlaintext({ address: fill(5, 20), notifyKey: fill(6, 32) }))).toBeNull();
  expect(() => passkeySeedPlaintext(fill(2, 31))).toThrow();
  const id = passkeySeedId(prf, canister, 0);
  expect(passkeySeedId(prf, canister, 1)).not.toEqual(id);
  expect(passkeySeedId(fill(3, 32), canister, 0)).not.toEqual(id);
  expect(passkeySeedId(prf, Principal.fromText('ryjl3-tyaaa-aaaaa-aaaba-cai'), 0)).not.toEqual(id);
});

test('every code of an owner gets its own key', () => {
  const seed = randomBytes(32);
  const key = codeKey(seed, 1n, 1, 0);
  expect(codeKey(seed, 1n, 1, 1)).not.toEqual(key);
  expect(codeKey(seed, 1n, 2, 0)).not.toEqual(key);
  expect(codeKey(seed, 2n, 1, 0)).not.toEqual(key);
  expect(codeKey(randomBytes(32), 1n, 1, 0)).not.toEqual(key);
});

test('low-order keys are refused', () => {
  expect(sealTo(new Uint8Array(32), 'label', new Uint8Array(), fill(1, 8))).toBeNull();
});

test('every root seed, address and canister has its own view key', () => {
  const [seed, address, canister] = [fill(1, 32), fill(2, 20), Principal.fromText('rrkah-fqaaa-aaaaa-aaaaq-cai')];
  const view = viewKey(seed, address, canister).seed;
  expect(viewKey(seed, address, canister).seed).toEqual(view);
  expect(viewKey(fill(3, 32), address, canister).seed).not.toEqual(view);
  expect(viewKey(seed, fill(4, 20), canister).seed).not.toEqual(view);
  expect(viewKey(seed, address, Principal.fromText('ryjl3-tyaaa-aaaaa-aaaba-cai')).seed).not.toEqual(view);
});

test('a state comes back only for its own view key', () => {
  const view: ViewKey = { address: fill(1, 20), seed: randomBytes(32) };
  const state = emptyState(view, [1n, 2n ** 60n]);
  state.incoming.push({
    peer: null,
    via: { type: 'code', chainId: 1n, tokenId: 3, index: 4 },
    seed: null,
    inbox: null,
    key: codeKey(view.seed, 1n, 3, 4),
    chains: [{ chainId: 1n, nextSlotIndex: 2, records: [] }],
  });
  const bytes = exportState(view, state);
  expect(importState(view, bytes)).toEqual(state);
  expect(importState({ ...view, address: fill(2, 20) }, bytes)).toBeNull();
  expect(importState({ ...view, seed: randomBytes(32) }, bytes)).toBeNull();
});

test('an escrow opens to its view key by the vetKey encrypted to the auditor, in the bytes the canisters hold', () => {
  // The escrow public key of a known secret, the vetKey it gives for one registration encrypted to a transport key,
  // and a view seed sealed to that registration: fixed bytes, as every registration in a canister keeps its escrow
  // for as long as it stands, and a vetKD library that read them otherwise would lock the auditor out of them all.
  const escrowPublicKey = DerivedPublicKey.deserialize(
    unhex(
      'a1d6ff62c0ecab6c144a940fb8f87469ebfc81bac7dfd534ccf5c9805138f17b4d25d21e0b3ace6e29eb339a44f497230424c44efb3532f5b075e61f43fae55ea23df5f7bcad61c9b991e60509a3808770d4332d1a1519668b1c9a42d0dc8039',
    ),
  );
  const transport = (key: string) => TransportSecretKey.deserialize(unhex(key));
  const encrypted = unhex(
    '90c4db413ef0b21e6fbbb2ed99a40b666f3fee305371b058c10f196645ec868a6ea9bbc59f16eec4a3399d7c5dea680cac6fff52796c18250877489805e6b7b5cc4b19dcdfa98762ef792c4f388b68bccbd755caa2c3ffc50f20cae95a57163c0d5807380e0247d81f1d136a6ee42b9518df694c5791cae37ccdef69dc0cb6424b32e7c0adeed7448650d9ce3449befab7b70abcc9f9f844e08d6c2ea60b39c6f6d5cd02224fc7766038a17eb452859b4117efe5e746836f3db15650702c479d',
  );
  const registration = {
    address: unhex('5d646b727980878e959ca3aab1b8bfc6cdd4dbe2'),
    public_key: fill(1, 32),
    notify_key: unhex('e9f0f7fe050c131a21282f363d444b525960676e757c838a91989fa6adb4bbc2'),
    escrow: unhex(
      '494320494245000196da7614a3943e051c25752e7b5e91c61ec8d74a0c252af6971eba8a2ddfe08d042bbefe4eaa4d682077366b2a6b14d4084f8a54e705a23645957b10a120579ac158235f316d884e74b316306e0be5db3632f00e7aa94364b551555ec734e1ffdf0888a972a7aab12dad0c4d8850da014c0bd0b7daaec835d97f3dcb4e56dd728683b69836ffdbe22775821edfe23ef2a8e401d3f986797bde76325d488e30e7',
    ),
    expiry_ns: 0n,
    signature: new Uint8Array(),
  };
  const mine = transport('1f262d343b424950575e656c737a81888f969da4abb2b9c0c7ced5dce3eaf1f8');
  expect(openEscrow(encrypted, mine, escrowPublicKey, registration)).toEqual({
    address: registration.address,
    seed: unhex('171e252c333a41484f565d646b727980878e959ca3aab1b8bfc6cdd4dbe2e9f0'),
  });
  // another transport key reads another point, which is no vetKey of this registration
  const other = transport('2f262d343b424950575e656c737a81888f969da4abb2b9c0c7ced5dce3eaf1f8');
  expect(openEscrow(encrypted, other, escrowPublicKey, registration)).toBeNull();
  // nor does the vetKey open the escrow of a registration with another notify key
  expect(openEscrow(encrypted, mine, escrowPublicKey, { ...registration, notify_key: fill(2, 32) })).toBeNull();
});
