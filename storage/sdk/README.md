# @zerc20/storage-sdk

Private note delivery for zERC20 on the Internet Computer. A payer leaves a note's opening, encrypted, in the storage
canister, and the receiver finds it with its view key. The canister holds only ciphertext under unlinkable ids, so it
cannot tell who paid whom. Every secret stays in this SDK.

```sh
npm install @zerc20/storage-sdk
```

Node 22.12 or later. Apps that hold a wallet use it through `@zerc20/wallet-sdk`.

## License

[MIT](LICENSE)
