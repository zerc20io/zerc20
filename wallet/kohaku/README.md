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

## License

[AGPL-3.0](LICENSE)
