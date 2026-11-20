# deposit-relayer

When funds reach a registered deposit address, this node calls `DepositAddressFactory.flush`. That
call deploys the clone if needed and wraps its balance into the burn address, less a fee paid to
`FEE_RECIPIENT`. The relayer pays the gas. One instance serves every chain in `CHAINS` (`backend/README.md`).

## Why it looks like this

**Wallets register addresses.** A deposit address is counterfactual. Until its first flush, nothing
on chain mentions it, so the relayer cannot find it on its own. Registering costs the user little
privacy: `flush` puts the same `(token, burnAddress, refund, referrer)` on chain anyway. All a
registration adds is the client's IP and the time before the deposit. A wallet's refund is a signer
of its own, which names no account.

**It is trusted with nothing.** `flush` is permissionless, and a clone can only send funds to its
burn address, its fee recipient (the fee alone), its referrer (its share alone) or back as a refund. A relayer that is down or
malicious can only delay a deposit, since the user can call `flush` themselves. So anyone can run
one, and registration needs no auth.

**Every registration goes through `predict`.** The deposit address comes from the factory, not from
the client. An unregistered token or a zero address is rejected before it is stored. The wallet
checks the answer against `predict` too, with the fee and recipient the relayer named.

**It reads balances, not logs.** A native deposit, such as an exchange's ETH withdrawal, emits no
log. Balances also catch funds that arrived before registration or while the relayer was down.
Multicall3 batches 500 reads into one call.

**It keeps no in-flight state.** Each tick decides from balances, so a failed or timed-out flush
is simply retried on the next tick. A flush that would revert, for example for a blocked address,
fails at gas estimation and spends no gas. An unmined flush has its fees raised every 30 s, and one
left pending, even by an earlier run, is outbid by the next flush; its address is then just flushed
again on a later tick.

**A native flush that reverts on chain and leaves its funds stops its address for good.** Paying a
referrer in the native asset calls it, and a referrer can pass gas estimation yet revert on chain,
which would cost gas on every tick. Such an address is flushed no more, registered again or not;
the user can still flush or refund it. An ERC-20 referral calls no referrer, so its reverts pass.
So does a flush that lost a race to another, which finds the funds gone at its block, and one whose
balance there cannot be read: the next tick decides.

**The fee is per token, and fixed in the address.** The clone's args hold the fee and its recipient,
so the user agrees to both when handed the address, and a later change leaves existing addresses as
they were. Gas does not depend on the amount, so neither does the fee. It follows the gas price as
the transact-relayer's does, with a flush priced at `FEE_GAS`, and a flush may take no more gas than
that with the margin: paying a referrer in the native asset calls it, which could otherwise burn gas
the fee does not pay for, and an address whose flush needs more is not flushed. A registration takes
the fee of the moment, so it needs no grace period. A balance that does not exceed the fee is never flushed: a
flush of it reverts, so dust costs the relayer nothing. A token with no fee is refused at
registration. Fees in an ERC-20, such as USDC, pile up at `FEE_RECIPIENT` until someone moves them.

**An app's share passes straight through.** An app that hands out addresses names itself as their
referrer and its rate, which the clone pays on top of the relayer's fee.
The relayer takes whatever the factory accepts: the share comes out of what is left after the fee,
so it never changes which balances are worth flushing.

**Registrations expire after 7 days.** Polling cost grows with the watched set. Seven days bounds
that set and still covers slow exchange withdrawals. Funds that arrive later are not stuck: a wallet
has the address watched again with `/rewatch`, which keeps the fee it was registered with. A new
registration would take the fee of the moment, and with it another address.

**It uses a JSONL file, not a database.** Polling keeps every registration in memory anyway, and a
volunteer should not have to run Postgres. Each line is fsynced before the API answers. A line
torn by a crash was never acknowledged, so loading skips it.

## API

`POST /register {token, burnAddress, refundAddress | refundSigner, referrer?, referralBps?}` returns
`{depositAddress, feeRecipient, fee}`, or 400 if the token has no fee or `predict` reverts. Without a
referrer, both are zero. `fee` is a hex string, in the underlying's base
units.

`POST /rewatch {depositAddress}` watches a registered address for another 7 days and returns the same
fields, or 404 if it was never registered here.

## Run

| env                                                                     |                                                                                                                      |
| ----------------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------------------- |
| `RPC_URL`, `DEPOSIT_ADDRESS_FACTORY`                                    |                                                                                                                      |
| `PRIVATE_KEY`                                                           | pays the gas; used by nothing else (see `backend/README.md`)                                                         |
| `FEE_RECIPIENT`                                                         | where the fees of new registrations go; default the relayer's key                                                    |
| `FEES`                                                                  | `name=fee,...` in the underlying's base units: the fees until the gas price is read, and of tokens it does not price |
| `TOKENS`, `FEE_GAS`, `NATIVE_USD_FEED`, `PRICE_FEEDS`, `FEE_MARGIN_PCT` | as for `backend/transact-relayer`, with `FEE_GAS` the gas of a flush                                                 |
| `LISTEN`, `STORE`                                                       | default `127.0.0.1:8080`, `registrations.jsonl`                                                                      |
| `POLL_SECS`                                                             | pause between balance polls, default 15                                                                              |

The register API has no rate limit. If registrations get spammed, rate-limit them in a proxy in front.

```sh
cargo test -p zerc20-deposit-relayer
```

anvil has no Multicall3. To test locally, copy its code from a public chain with `anvil_setCode`.
