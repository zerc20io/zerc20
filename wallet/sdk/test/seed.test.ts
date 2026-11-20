import { bytesToHex, createWalletClient, hexToBytes, http } from 'viem';
import { privateKeyToAccount } from 'viem/accounts';
import { expect, test } from 'vitest';
import vector from '../../../zkp/test-vectors/wallet-seed.json' with { type: 'json' };
import { core, initCore } from '../src/core.js';
import { accountKey, seedFromSignature } from '../src/seed.js';

// The treasurer derives its wallet's key the same way (`zerc20-treasurer wallet-key`), from the same vector.
test('the seed is keccak256 of the canonical seed signature, pinned', async () => {
  // anvil's account 1: a local account signs without a node
  const account = privateKeyToAccount(vector.privateKey as `0x${string}`);
  const { seed, signature } = await seedFromSignature(
    createWalletClient({ account, transport: http('http://127.0.0.1:1') }),
  );
  expect(signature).toBe(vector.signature);
  expect(bytesToHex(seed)).toBe(vector.seed);
  await initCore();
  expect((core.spendKey(seed) as { publicKey: string }).publicKey).toBe(vector.publicKey);
});

// a seed's public account is its users' address, and the one any wallet opens from its recovery phrase: the
// derivation never changes
test("a seed's account is its recovery phrase's first BIP-44 account, as any wallet derives it, pinned", () => {
  // the phrase of the all-zero seed, abandon ×23 then art, whose first account every BIP-44 wallet shows
  expect(privateKeyToAccount(accountKey(new Uint8Array(32))).address).toBe(
    '0xF278cF59F82eDcf871d630F28EcC8056f25C1cdb',
  );
  const key = accountKey(hexToBytes(vector.seed as `0x${string}`));
  expect(key).toBe('0xcf8ba77d14b6e4681779ce3903c9f51487c3ed3f003e5d187091859d47801dc5');
  expect(privateKeyToAccount(key).address).toBe('0xE8E11c878d9A9a0EFD2b145Dd3C24A0EBCb4Da19');
});
