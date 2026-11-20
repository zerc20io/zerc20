# backend

The off-chain nodes of zERC20, one Rust binary each; `scripts/dev-stack.sh` runs them all locally. None of them holds
user funds. Most can at worst delay a user, and the ones trusted with more say what for. Each node's README has the
details.

## What every node shares, and why

- **One process serves every chain** in `CHAINS`, so a new chain is configuration, not another deployment. A setting is
  read for the chain first (`BASE_SEPOLIA_RPC_URL`), then shared (`RPC_URL`), so what every chain has in common is
  given once. Each chain runs and restarts on its own, so one chain's RPC going down stops no other.
- **A node's key is its alone.** It sends one transaction at a time, raising the fee until it is mined, and takes the
  nonce from the chain. A transaction stuck from earlier, even from an earlier run, is then outbid instead of holding
  everything behind it, which only works if nothing else sends from the key.
- **The nodes trust the indexer, not the roots the contract accepts.** A circuit soundness bug could put a forged root
  on chain. The indexer derives the tree itself and flags the first root that differs. Everything downstream keeps
  working against the last honest root.
- **Nothing acknowledged is lost to a crash.** Append-only files drop only the torn tail a crash leaves.

## Nodes

- **indexer**: wallets download the commitments, roots and nullifiers in bulk and match locally, never asking about
  one of them, so the indexer and the CDN in front of it learn nothing about who is looking. It stores only what it
  has checked is complete, rolls back reorgs, and says what is final.
- **root-prover**: wallets can spend only against a root proved on chain. It proves up to a checkpoint it reserves on
  the ledger, so it need not wait for finality: a reorg costs one round. It is also the ledger's guardian: once the
  indexer finds a forged root, it puts the ledger in an emergency at the last honest one.
- **asp**: approves deposits, not addresses. It screens each deposit's sender after a delay, so that freshly stolen
  funds have time to get labeled. Decisions are final, so an older root approves a subset of a newer one. Its tree is
  fetched the way the indexer's is, so fetching it reveals nothing new. Wallets prove against the root on chain, never
  one the ASP hands out, which could single a wallet out.
- **attester**: insurance against a circuit soundness bug, and the AML check on withdrawals. An enclave re-checks each
  witness, sealed so that the host never sees it, and holds a key that is released only to the enclave's image. A
  compromised host defeats everything but that witness check, which does not cover the root circuit: catching a
  forged root is the indexer's job. If screening keeps failing, the on-chain blocklist decides, so an outage only
  delays withdrawals.
- **transact-relayer**: lets a user spend and merge without gas from an account linked to them. Its fee is the same for
  everyone at a time, and follows the gas price in steps: a fee paid in public that scaled with the amount, or
  differed per user, would reveal the amount or the user.
- **deposit-relayer**: moves funds out of deposit addresses, so that a depositor never has to, for a fee. It is
  trusted with nothing: flushing is permissionless, and its destination and fee are fixed in the address, so a relayer
  can only delay a deposit.
- **merge-prover**: proving a merge takes the inputs' openings, so it proves inside an enclave and keeps nothing. It
  never holds a private key: each input's owner signs the merge, so it can prove that merge only. Only the proof
  leaves, and the relayer sends it.
- **treasurer**: keeps every node's key in gas, so that no one has to. The relayers' fees go to it. It unwraps the
  zETH among them, tops up a node account that runs low, and sends what it does not keep to a cold wallet. It is the
  one key that holds more than gas, and how much more is bounded.
- **watcher**: holds no key and acts on nothing. It tells people when something needs them, such as a forged root, an
  emergency, a stalled node or low gas, and a heartbeat shows the watcher itself is alive.
