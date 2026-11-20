# asp

Screens the sender of every deposit with Chainalysis, appends the decisions to the ASP tree in
commitment index order, serves that tree to wallets, and publishes its root with
`Verifier.publishAspRoot`. One instance serves every chain in `CHAINS` (`backend/README.md`),
each from its own indexer.

## Why it looks like this

**It acts on final positions only.** Approvals are keyed by position. If a reorg replaced a screened
deposit, the replacement would be approved without screening. So it reads up to the indexer's
`commitments_final` and nothing past it.

**It waits on block time.** A sender is screened once its deposit's block is `SCREEN_DELAY_SECS`
old (10 minutes), so freshly stolen funds have time to get labeled. Blocks come from the indexer's
`/blocks/{p}`, and their timestamps from the chain.

**Decisions are final, and ambiguity is never a rejection.** `Low` and `Medium` pass; `High` and
`Severe` fail. Anything else, such as an unknown `risk`, a `status` other than `COMPLETE`, a 429 or a
timeout, is retried, and it holds back every later position meanwhile. A rejection could not be
undone, and an approval could only be undone by replacing the publisher.

**A sender Chainalysis keeps failing on is decided by the Blocklist alone.** After 5 failed attempts
in a row (one per 5 s tick), the sender passes unless the protocol's `Blocklist` lists it. That is
the same list every zERC20 transfer already checks, so it catches only senders added since the
deposit. This trades screening for liveness, so that one sender or an outage cannot hold back every
later deposit for long. Each fallback is logged, and `/status` says how long Chainalysis has been
down, as a probe of a fixed address every 30 s finds it, so that the watcher can tell people. A
429 is not a failure here: anyone can bring it about with deposits, and with withdrawals through
the attester, which a deployment gives the same key, and so time a fallback for a deposit of their
own. The attester keeps to its own share of the key.

**Only transfers are approved.** The ASP cannot tell a deposit to a burn address from any other
transfer, since burn addresses are hash-derived, so it screens every transfer. A note, or any tag
that is not a transfer, gets 0.

**Two append-only files, no database.** Each position is one byte, `1` or `0`, fsynced per batch.
Each root is recorded (104 bytes) and fsynced before it is published, so a wallet that reads a root
on chain always finds its size here. A tail torn by a crash was never acknowledged, so loading cuts
it.

- The files are named after the chain id and the Verifier. CREATE3 gives the Verifier one address on
  every chain, so a `DATA_DIR` reused elsewhere starts empty instead of applying another chain's
  decisions.
- The indexer must serve the same chain: before the first screening, its latest root must be one
  this chain's ledger proved (`provedIn`, which an emergency's bound does not hide).

**It publishes whenever the chain's root differs from its own.** That one rule covers a first start,
new decisions, a dropped transaction and a new publisher, which `setAspPublisher` leaves at root 0
and so blocks every transact and merge until something is published. Even the empty tree's root
unblocks them.

## API

Shaped like the indexer's, for a CDN in front: the same bytes for everyone, in pages of 4096
entries numbered like the indexer's, so `{c}` is `index / 4096`. A page is immutable once full,
since decisions never change.

| path               |                                                                                                                     |
| ------------------ | ------------------------------------------------------------------------------------------------------------------- |
| `/bitmap/{c}`      | 512 bytes: position `c * 4096 + j` is bit `j % 8` (least significant first) of byte `j / 8`, set if approved        |
| `/chunk-roots/{p}` | roots of full chunks `p * 4096 ..`, 32 bytes each                                                                   |
| `/page-roots`      | roots of full pages (2^24 positions), 32 bytes each                                                                 |
| `/roots/{p}`       | recorded roots in order, 104 bytes each: size (8), root, partial chunk root, partial page root (zero where none)    |
| `/status`          | `decided`, `roots`, `latest_root`, `delay_secs` (`SCREEN_DELAY_SECS`), `chainalysis_down_secs` (0 while it answers) |

To prove a deposit at position `i`, a wallet:

1. reads `Verifier.latestAspRoot` from the chain, never a root the ASP hands it, since a root picked
   for one wallet would mark its spend;
2. finds that root's size `n` in `/status` or `/roots/{p}`;
3. fetches `/bitmap/{i / 4096}`, the same number as its commitment chunk, so the ASP learns nothing
   the indexer does not;
4. clears every bit at or past `n`, since later positions may have been decided since;
5. builds the path from the bitmap, its page of `chunk-roots`, `page-roots` and the root's partial
   roots, the same way `zerc20_zkp::tree::sized` builds the tree.

The leaf of an approved position is `asp_leaf(i)` (`zkp/src/commitments.rs`), and 0 otherwise.

## Run

| env                                       |                                                                                                                                                                          |
| ----------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| `RPC_URL`, `VERIFIER`                     |                                                                                                                                                                          |
| `INDEXER_URL`                             | the indexer's origin, not the CDN                                                                                                                                        |
| `PRIVATE_KEY`                             | `Verifier.aspPublisher`, used by nothing else (see `backend/README.md`)                                                                                                  |
| `CHAINALYSIS_API_KEY` or `DEV_PASS_ALL=1` | exactly one. `DEV_PASS_ALL` passes every sender, for development. The API takes no chain: on a testnet it screens an address by its mainnet record, which a testnet uses |
| `DEV_REJECT`                              | with `DEV_PASS_ALL=1` only: comma-separated senders that fail, to test rejections                                                                                        |
| `CHAINALYSIS_API_BASE_URL`                | default `https://api.chainalysis.com`                                                                                                                                    |
| `SCREEN_DELAY_SECS`, `PUBLISH_SECS`       | default 600, 300                                                                                                                                                         |
| `DATA_DIR`, `LISTEN`                      | default `asp-data`, `0.0.0.0:3001`                                                                                                                                       |

```sh
cargo test -p zerc20-asp
backend/asp/scripts/e2e.sh  # anvil + Postgres + indexer: delay, approvals, publishing, restart, Blocklist fallback, new publisher
```

The e2e script needs what the indexer's does, and has to run outside the Claude Code sandbox for the
same reason.

**If `DATA_DIR` is lost,** replace the publisher with `setAspPublisher` and start empty. Screening
again could decide a position differently, and a root that withdraws an approval breaks the rule
that older roots approve a subset of newer ones. Also purge the CDN, which caches full pages
forever. The ASP refuses to start if a recorded root covers more positions than it has decided.
