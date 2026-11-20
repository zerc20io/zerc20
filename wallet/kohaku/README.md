# @zerc20/kohaku-plugin

zERC20 as a [Kohaku](https://github.com/ethereum/kohaku) privacy plugin: a wallet built on `@kohaku-eth/plugins` shields
into zERC20, pays privately and unshields, through the `Host` it already has.

```sh
npm install @zerc20/kohaku-plugin @kohaku-eth/plugins viem
```

```ts
import { createZerc20Broadcaster, createZerc20Plugin } from '@zerc20/kohaku-plugin';
import { networkFromJson } from '@zerc20/wallet-sdk';

const network = networkFromJson(await (await fetch('https://v2.zerc20.io/network.json')).text());
const plugin = await createZerc20Plugin(host, { network, accountIndex: 0 });
const usdc = { __type: 'erc20', contract: '0xA0b8…eB48' } as const;

const { txns } = await plugin.prepareShield({ asset: usdc, amount }); // sent in order, before the next shield's
await plugin.balance([usdc]); // spendable, then `pending` (screening, or awaiting a root)
const op = await plugin.prepareTransfer({ asset: usdc, amount }, 'zerc20id1…');
await createZerc20Broadcaster(plugin).broadcast(op);
```

Assets are named by their underlying ERC20 (ETH as `0xeeee…eeee`): a shield wraps it, an unshield pays it out. Named
by the zERC20 token itself, they move as they are.

## Why it looks like this

- **One plugin per chain.** Kohaku gives a plugin one provider, and a zERC20 account keeps a state of its own on each
  chain, so a host opens a plugin per chain, side by side.
- **The host's network covers everything.** Chain reads go through `host.provider`, and every server request (the
  relayer, the attester, the storage canister, the circuits) through `host.network.fetch`: a host's proxy or Tor
  covers them all.
- **Keys come from the host's keystore**, below `m/31333'/1'/{accountIndex}'` only, so the host's mnemonic restores
  the account. It is not the account wallet.zerc20.io opens with a passkey.
- **Preparing spends nothing.** `prepareTransfer` and `prepareUnshield` quote the fee and check that one JoinSplit pays
  it; the broadcaster proves on the device, has the relayer submit, and returns once mined, not the minutes later it
  is final. Syncs see it through to final, and send it again should a reorg drop it; an interrupted broadcast resumes
  at the next `sync()`.
- **The wallet underneath is `plugin.wallet`** (`@zerc20/wallet-sdk`), for receive codes, consolidation, rage exits,
  history and view keys. `plugin.wallet.close()` lets the account go.

## License

[AGPL-3.0](LICENSE)
