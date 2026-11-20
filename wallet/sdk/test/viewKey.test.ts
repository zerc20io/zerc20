import { encodeCode } from '@zerc20/storage-sdk';
import { bytesToHex, getAddress } from 'viem';
import { expect, test } from 'vitest';
import { type Ctx, spendKey } from '../src/context.js';
import { initCore } from '../src/core.js';
import { decodeViewKey, encodeViewKey, viewKeyAccount } from '../src/viewKey.js';

const keyOf = (fill: number) => spendKey({ seed: new Uint8Array(32).fill(fill), owners: new Map() } as unknown as Ctx);
const view = { address: new Uint8Array(20).fill(0xaa), seed: new Uint8Array(32).fill(0xbb) };

test("a view key gives back the account's view key and owner, its public key made from the parts", async () => {
  await initCore();
  const { authKeyHash, publicKey, nullifyingKey } = keyOf(7);
  const text = encodeViewKey(view, { authKeyHash, publicKey, nullifyingKey });
  expect(text).toMatch(/^zerc20view1/);
  expect(decodeViewKey(text)).toEqual({ view, owner: { authKeyHash, publicKey, nullifyingKey } });
  expect(decodeViewKey(` ${text.toUpperCase()}\n`)?.owner.publicKey).toBe(publicKey);
  expect(viewKeyAccount(text)).toBe(getAddress(bytesToHex(view.address)));
});

test("another key's nullifying key makes another public key, which the account's registration then refuses", async () => {
  await initCore();
  const own = keyOf(7);
  const text = encodeViewKey(view, { ...own, nullifyingKey: keyOf(8).nullifyingKey });
  expect(decodeViewKey(text)?.owner.publicKey).not.toBe(own.publicKey);
});

test('a receive code, a cut or mistyped key, and a field too large are not view keys', async () => {
  await initCore();
  const text = encodeViewKey(view, keyOf(7));
  const code = encodeCode({
    chainId: 1n,
    tokenId: 1,
    burnAddress: new Uint8Array(20),
    publicKey: new Uint8Array(32),
    key: new Uint8Array(32),
  });
  expect(decodeViewKey(code)).toBeNull();
  expect(viewKeyAccount(code)).toBeNull();
  expect(decodeViewKey(text.slice(0, -1))).toBeNull();
  expect(decodeViewKey(text.slice(0, 20) + (text[20] === 'q' ? 'p' : 'q') + text.slice(21))).toBeNull();
  expect(decodeViewKey(encodeViewKey(view, { ...keyOf(7), nullifyingKey: `0x${'ff'.repeat(32)}` }))).toBeNull();
});
