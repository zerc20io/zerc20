# @zerc20/wallet-sdk

A zERC20 wallet for browsers and Node: deposits, private payments, merges, withdrawals and rage exits. Proofs are made
on the device, and what the attester and the merge prover need reaches them sealed to an enclave the SDK has checked.

```sh
npm install @zerc20/wallet-sdk viem
```

Node 22.12 or later. viem is a peer dependency: the SDK tells a declined wallet prompt by viem's error classes, so it
must be the app's own copy.

```ts
import { Wallet, networkFromJson, seedFromSignature } from '@zerc20/wallet-sdk';

const network = networkFromJson(networkJson);
const { seed } = await seedFromSignature(walletClient); // a viem WalletClient with its account
const wallet = await Wallet.open({ network, walletClient, seed, persist: { load, save } });
await wallet.sync();
wallet.balances();
const q = await wallet.fees({ kind: 'send', token, amount });
await (await wallet.send({ to: 'zerc20id1…', token, amount, maxFee: q.fee })).wait();
```

## License

[AGPL-3.0](LICENSE)
