# treasurer

Keeps every node's key in gas, so that no one has to. The relayers' fees go to it (their `FEE_RECIPIENT`). Each
minute, on each chain, it:

1. once an hour, unwraps the zETH it holds into ETH (zBNB, zPOL: the native token's zERC20);
2. tops up a node account below half of `TOP_UP_TO` back to `TOP_UP_TO`;
3. sends what it holds above `KEEP` to `SWEEP_TO`, once it holds twice `KEEP`.

One instance serves every chain in `CHAINS` (`backend/README.md`).

## Why it looks like this

**Fees go to one key, and gas comes from it.** Before, each relayer's fees piled up at its own key, and a person
topped up the root-prover and the ASP, which earn nothing. Now a node's key holds only gas. A top-up is a transfer to
it, not from it, so every key is still sent from by one process alone, which `Sender` needs.

**No contract changes.** A deposit address names its fee recipient in its clone args, and a transact's withdrawal
and a merge's fee go wherever the proof says. The wallet pays the address `/fee` names.

**It moves funds in lumps.** zETH is unwrapped once an hour, in one transaction for every fee of that hour, and a
sweep waits for twice `KEEP`. So a relay's fee does not cost gas of its own.

**A key that holds more than gas holds a bounded amount.** With `SWEEP_TO` set, it holds at most about twice `KEEP`
in ETH and an hour's fees in zETH, plus the ERC-20 fees below. Without it, as on testnets, everything stays.

**What it cannot pay, it leaves.** A top-up larger than its balance fails at gas estimation, costs nothing, and is
logged. The watcher reports the treasurer below a quarter of `TOP_UP_TO`, and the node account once it gets there.

**It keeps no state** but when it next unwraps. Each tick decides from balances alone, and a start unwraps at once.

## Not yet done

- **ERC-20 fees pile up**: USDC from deposit fees, zUSDC from relayed transfers. Swapping them into ETH (through CoW
  Swap, say) waits for mainnet, since a testnet's DummyUSDC has no market.
- **The transact-relayer's fee notes** are collected by no one yet. They are this account's wallet's: the relayer keeps
  their openings in `fee-notes.jsonl`, and the wallet SDK's `seedFromSignature` opens that wallet from this account.
- **The protocol's withdrawal fees** accrue in the Verifier to `feeRecipient`, and anyone may `claimFees` them there.
- **Chains do not fund each other.** A chain whose nodes spend more than its relayers earn drains its treasurer. Then
  bridge to it by hand.

## Run

| env                   |                                                                  |
| --------------------- | ---------------------------------------------------------------- |
| `RPC_URL`, `VERIFIER` | the native token's zERC20 is read through the Verifier's factory |
| `PRIVATE_KEY`         | the treasurer's; used by nothing else (see `backend/README.md`)  |
| `ACCOUNTS`            | `name=0x…,…`: the node accounts to keep in gas                   |
| `TOP_UP_TO`, `KEEP`   | wei                                                              |
| `SWEEP_TO`            | the cold wallet; unset, nothing is swept                         |
| `TICK_SECS`           | default 60                                                       |
| `UNWRAP_SECS`         | default 3600                                                     |

`zerc20-treasurer wallet-key` prints the public key of the wallet `seedFromSignature` opens for `PRIVATE_KEY`'s account:
the transact-relayer's `FEE_PUBLIC_KEY`. Its test holds it to the wallet SDK's, on `zkp/test-vectors/wallet-seed.json`.

```sh
cargo test -p zerc20-treasurer
```

`scripts/dev-stack.sh` runs it with a short `UNWRAP_SECS`, so it unwraps the relayers' zETH fees as they come,
logging to `target/dev-stack/treasurer.log`.
