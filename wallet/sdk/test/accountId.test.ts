import { encodeCode } from '@zerc20/storage-sdk';
import { getAddress } from 'viem';
import { expect, test } from 'vitest';
import { accountId, idAccount } from '../src/accountId.js';

const address = getAddress('0x00112233445566778899aabbccddeeff00112233');

test('a zERC20 ID gives back its account, checksummed, however it is cased or padded', () => {
  const id = accountId(address);
  expect(id).toMatch(/^zerc20id1[02-9ac-hj-np-z]{38}$/);
  expect(idAccount(id)).toBe(address);
  expect(idAccount(` ${id.toUpperCase()}\n`)).toBe(address);
});

test('an address, a receive code, and a cut or mistyped ID are not zERC20 IDs', () => {
  const id = accountId(address);
  const code = encodeCode({
    chainId: 1n,
    tokenId: 1,
    burnAddress: new Uint8Array(20),
    publicKey: new Uint8Array(32),
    key: new Uint8Array(32),
  });
  expect(idAccount(address)).toBeNull();
  expect(idAccount(code)).toBeNull();
  expect(idAccount(id.slice(0, -1))).toBeNull();
  expect(idAccount(id.slice(0, 12) + (id[12] === 'q' ? 'p' : 'q') + id.slice(13))).toBeNull();
});
