# wallet

A zERC20 wallet for browsers and Node.

- **`sdk/`** (`@zerc20/wallet-sdk`): the TypeScript SDK apps use. It does all I/O.
- **`kohaku/`** (`@zerc20/kohaku-plugin`): the SDK as a [Kohaku](https://github.com/ethereum/kohaku) privacy plugin, so
  that wallets built on Kohaku offer zERC20 beside its other protocols.
- **`cli/`** (`@zerc20/cli`): the SDK from a terminal, as the `zerc20` command: an account watched by its view key or
  paid from by its recovery phrase, and a merge prover run on the machine itself.
- **`core/`**: the protocol's computations (keys, tags, paths, the attester's witness check, sealing), in the same
  Rust as the circuits and the attester, compiled to wasm. One implementation means the wallet cannot drift from
  what the attester accepts. It is its own workspace, so the attester's image never builds wallet code.

How an app uses the SDK is at [docs.zerc20.io](https://docs.zerc20.io/developers/wallet-sdk).

## Why it looks like this

**Nothing secret leaves the device unencrypted.**

- JoinSplit proofs are made here.
- The attester and the merge prover get a witness sealed to their enclave. The wallet takes the enclave's key only
  from an attestation document that chains to the AWS Nitro root and measures the published PCR0.
- `Wallet.open` refuses a network that would weaken this: plain HTTP, or a development enclave, off the local chain.
  A merge prover with no enclave passes at a loopback address alone: one the wallet's own machine runs, which holds
  the witness already.

**Servers are not trusted with what they serve.**

- Paths built from indexer and ASP pages must fold to a root the chain accepts (`provedRoots`, `latestAspRoot`).
- A deposit address from the deposit relayer is checked against the factory's `predict`, with the fee it names.
- The attester's own check runs on each witness first, so a witness it would refuse never leaves.

**Operations survive a crash.** Each saves its progress before every step that leaves the device: storage notes,
proof, attestation, relay. A sync after a reload resumes it where it stopped.

**An operation is done only once it is final on chain.**

- A JoinSplit or a merge counts as landed when its own new note (a payment's change, a merge's note) is final, not
  when the relayer says so or an input is spent: a reorg could still drop it, the relayer's answer could be a lie,
  and another device of the same wallet may spend an input first, as each device locks its inputs in its own state.
- An unresponsive server only delays an operation. It fails only on what trying again cannot change.

**The seed can stay away.** Opened with a function that gives the seed, a wallet keeps only what spends nothing: the
view key, the state's key, and each key's public and nullifying keys. Burn addresses derive from the view key, as a
salt spends nothing, so deposits never ask for the seed. Payments, withdrawals, merges and rage exits do, and the
wallet lets it go once nothing in flight signs again: a JoinSplit that reverts is proved again, and each merge round
is signed. A receive code has a key of its own, derived for the next few while the seed is held. A note paid to a
code another device made meanwhile waits for the seed's return, since storage tells of a note only once.

**A view key shows the account and spends nothing.** It holds the address, the view key and the wallet's own
nullifying key and signing key hash, so another device finds what the account holds and sees what it spends. `watch`
makes the public key from the last two and checks it against the account's signed registration. A key that does not
match does not open, so a forged nullifying key cannot show spent coins as unspent. Private payments to receive codes
do not show: each code has a key of its own, which only the seed derives.

**A payment never waits.** `send` and `withdraw` use one JoinSplit from what is spendable now, or fail at once and
say why: `needs-consolidation`, `funds-settling` (still screening, or awaiting a root) or `insufficient-funds`.
Waiting or merging first is the app's call, since the user should see it.

**A forged root changes nothing here.** If a soundness bug ever proves one, the protocol enters an emergency. The
indexer stays on the last honest root, so what it covered stays spendable. What came after shows as `roots-halted`,
and deposits can still be rage-exited.

## Paying someone

A note is owned by its recipient's public key, which only the recipient's seed derives. So a payer needs the key: the
one an address registered in the storage canister when its wallet first opened, or the one in a receive code. `send`
checks the registration's signature, so the canister can withhold a key but not swap one. An app shows the account as
its zERC20 ID (`zerc20id1…`), the address in a form other wallets refuse, so that no one pays it publicly, where the
wallet does not look.

## Finding what is yours

A wallet asks servers only for what every wallet downloads, and matches it locally, so no server learns what it
holds.

- It scans the indexer's pages for the 4-byte tags of what it expects and the nullifier prefixes of what it holds.
- Each key remembers how far it has been looked for, so nothing is read twice. Final pages never change, so a CDN
  serves them.
- A 4-byte tag sometimes matches someone else's, so a hit counts only once its commitment is read and is the one
  expected.

**Burn addresses are recorded in storage before they are handed out.** A payment to one writes nothing to storage, so
otherwise another device or a restore could not find it, or could hand the address out again. One is kept recorded
ahead, because recording it at handout time would date the payment that follows.

**A restore needs only the seed and the account.** An address that registered before is looked for from the chain's
start, unless a `birthday` (a block or a date) bounds how far back it scans.

## Merging

Notes pile up: a merchant's sales, or many small payments. `consolidate` folds up to 100 of them into one note with a
Nova merge, for one relayer fee.

- **Why a prover:** the merge decider key is 6.3 GB, too large for a device. The network's merge prover, shared by all
  its chains, proves it in an enclave. It sees that one merge's witness while it proves it, and nothing else.
- **Why through the relayer:** a merge sent from the user's account would name them as its caller. The relayer's fee
  is part of the merge itself (`fee`, `feeRecipient`).
- **Why a merged note is in storage first:** another device or a restore then finds it.

## Point of sale

A merchant's point of sale holds no key that spends, so a stolen one reveals which addresses are the merchant's and
nothing else.

- `posKey` gives the point of sale a lane of its own in storage, recorded in the wallet's own lane. The point of sale
  makes the wallet's addresses with it (`keys::derive_burn_address`, about 2^16 hashes each, off its event loop) under the public
  key the merchant registered, which `connect` looks up itself.
- It makes them ahead, twice what the token sold in the last 10 minutes and at least six: making one shows nobody
  anything. It records them in its lane, up to 16 blocks of six in one write, once few are left: right away when none
  is, otherwise at a random time within 10 minutes of running low, so that the time of a write does not mark a sale. So
  every device of the wallet watches them, and a sale writes nothing. A token's first sale waits for its first six.
- An address a sale or a payer waits for is searched first, and each point of sale in turn, so that none holds up
  another's. A server can run the search natively (`runBurnsOn`, wallet/core's `zerc20-burn-blocks`).
- One key, one point of sale: two would hand out the same addresses. A new key starts a new lane.
- The point of sale follows payments from the same pages every wallet reads, every sale's in one pass, and reads each
  payment's transaction.

## Limits

- **Scale:** `test/scale.test.ts` keeps 200k watched keys, 50k notes and 10k hits fast.

## Run

`scripts/dev-stack.sh` runs the whole protocol locally and writes `target/dev-stack/network.json`.

- `SPEED=fast` lands roots and merges unproved, in seconds: its merge prover checks each merge and proves none.
- `MERGE=1` proves merges: 6.3 GB of keys and about 16 GB of memory.

```sh
cd sdk && npm ci --ignore-scripts && npm run build   # needs storage/sdk built
npm test                                             # unit tests
npm run test:e2e                                     # every flow on the local stack
npm run demo                                         # a page over the SDK, against the local stack
```
