# watcher

Watches each chain's protocol and posts to Slack when something needs a person. It holds no key and
sends nothing on chain: acting is the nodes' job (the root-prover enters an emergency itself), or a
person's. One instance watches every chain in `CHAINS` (`backend/README.md`), each through
its own indexer and ASP. A deployment runs it on the sentinel, a host apart from the nodes it
watches. `--once` checks each of them once.

## What it reports

| alert         | level    | when                                                                                                                         |
| ------------- | -------- | ---------------------------------------------------------------------------------------------------------------------------- |
| a forged root | critical | the indexer's `/status.mismatch`: a proved root it does not derive. Ended by the admin's `recover` (`contracts/README.md`)   |
| an emergency  | critical | the ledger's `bound()` is set: no root above it is accepted, none is proved. Resolved by a recovery                          |
| the indexer   | critical | `/status` does not answer, or the indexer says it is stalled                                                                 |
| roots stop    | warning  | no root proved for `ROOT_STALE_SECS` while commitments wait (not in an emergency, which says so already)                     |
| the ASP stops | warning  | no decision for `ASP_STALE_SECS` while final commitments wait, or its latest root not on chain for that long                 |
| Chainalysis   | warning  | the ASP finds Chainalysis down for 5 min, so the Blocklist alone screens. Once per network, by the first chain in `CHAINS`   |
| low balance   | warning  | a node account (`WATCH_ADDRESSES`) holds less than a quarter of `TOP_UP_TO`                                                  |
| a failed read | warning  | the ledger, the ASP, a balance or the governance events cannot be read: never taken as healthy                               |
| governance    | critical | once per event: a call scheduled on the AccessManager, a role granted, or a protocol contract or the tokens' beacon upgraded |

## Why it looks like this

**An alert opens, repeats and resolves.**

- A critical alert goes out when it first appears. A warning goes out once it is there two rounds in a row, so that
  one failed read, such as a blip of the network, posts nothing.
- Either goes out again every `REPEAT_SECS` while it lasts.
- When it clears, a `RESOLVED` message goes out once.
- The state lives in memory, so after a restart every open alert is reported again.

**Silence must mean a healthy chain, not a dead watcher.**

- It posts a summary line when it starts, and again every `HEARTBEAT_SECS`.
- A read that fails is an alert, never a pass. Every read times out after 20 s.

**Staleness is time spent behind.**

- "Roots stop" counts only the time with commitments waiting, and the same goes for the ASP.
- So a quiet chain is never stale, and the first transfer after a quiet spell does not alert.

**A low balance is one the treasurer is not keeping up.**

- The treasurer tops a node account up to `TOP_UP_TO` once it holds less than half of that, and each chain's gas
  differs, so the threshold follows that chain's `TOP_UP_TO`.
- Between half and a quarter is the treasurer's time to act: an account it tops up never alerts, and one it does not
  still has gas for some sends when the alert comes.

**What Slack does not take is sent again.**

- A post that fails keeps its messages, and they go out with the next round's.
- At most 100 are kept, oldest dropped first.

**A governance event is reported once, and none is skipped.**

- Upgrades, verifier swaps and `recover` wait out the admin's delay so that people can look first: a scheduled call is
  reported with when it can run, and a grant or an upgrade with who or what.
- Logs are read up to the final block, so a reorg cannot add one behind the cursor.
- The cursor, one file per deployment in `DATA_DIR` (named by the chain id and the ledger, whose address is the same
  on every chain), is saved once Slack has taken what was read: a restart reads again from there, and at worst
  reports an event twice.
- Without a cursor, it reads from `START_BLOCK`, so its first start reports the deployment's own grants and upgrades.

**Each check is a pure function** (`src/checks.rs`, `src/notify.rs`), so it is tested without a chain.

## Run

| env                                           |                                                                                             |
| --------------------------------------------- | ------------------------------------------------------------------------------------------- |
| `CHAIN`                                       | its name in messages                                                                        |
| `RPC_URL`, `VERIFIER`                         | the ledger, the AccessManager and the factory from the Verifier                             |
| `DEPOSIT_ADDRESS_FACTORY`, `START_BLOCK`      | the deployment's, for its governance events                                                 |
| `DATA_DIR`                                    | where the governance cursor is kept                                                         |
| `INDEXER_URL`, `ASP_URL`                      | the origins, not the CDN                                                                    |
| `SLACK_WEBHOOK_URL`                           | an incoming webhook; without one, messages only go to the log                               |
| `WATCH_ADDRESSES`                             | `name=0x…,…`: the node accounts that pay gas                                                |
| `TOP_UP_TO`                                   | wei: the treasurer's, on this chain; needed with `WATCH_ADDRESSES`                          |
| `CHECK_SECS`, `REPEAT_SECS`, `HEARTBEAT_SECS` | default 60, 3600, 86400                                                                     |
| `ROOT_STALE_SECS`, `ASP_STALE_SECS`           | default 1800, 1800                                                                          |
| `LOG_BLOCKS`, `REORG_DEPTH`                   | default 1000, 64: blocks per getLogs, and how deep is final where a chain has no `safe` tag |

`zerc20-watcher --once` checks once, prints what it finds and exits 1 if anything is wrong. It reads no governance
events.

```sh
cargo test -p zerc20-watcher
```

`scripts/dev-stack.sh` runs it without Slack, logging to `target/dev-stack/watcher.log`.
`wallet/sdk/test/e2e/emergency.test.ts` checks that it reports a forged root and resolves it.
