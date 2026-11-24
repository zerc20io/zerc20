import { bytesToHex, createWalletClient, hexToBytes, http } from 'viem';
import { generatePrivateKey, privateKeyToAccount, toAccount } from 'viem/accounts';
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

// a contract account's wallet answers with bytes its contract checks, which wrap a signature after a head that is the
// same for every account of its kind: a seed from their first 64 bytes would be one seed for all of them
test("a seed comes only from a signature of the account's own key: a wrapped or foreign one is refused", async () => {
  const key = privateKeyToAccount(generatePrivateKey());
  const answering = (answer: (signed: `0x${string}`) => `0x${string}`) =>
    createWalletClient({
      account: toAccount({
        address: key.address,
        signMessage: async ({ message }) => answer(await key.signMessage({ message })),
        signTransaction: () => Promise.reject(new Error('the test sends nothing')),
        signTypedData: () => Promise.reject(new Error('the test signs no typed data')),
      }),
      transport: http('http://127.0.0.1:1'),
    });
  await expect(seedFromSignature(answering((s) => s))).resolves.toBeDefined();
  // wrapped: a constant head of two words, then the signature
  const head = bytesToHex(new Uint8Array(64).fill(1));
  await expect(seedFromSignature(answering((s) => `${head}${s.slice(2)}`))).rejects.toMatchObject({
    code: 'unsupported-account',
  });
  // 65 bytes, of another key
  const other = privateKeyToAccount(generatePrivateKey());
  const foreign = await other.signMessage({ message: 'anything' });
  await expect(seedFromSignature(answering(() => foreign))).rejects.toMatchObject({ code: 'unsupported-account' });
});
