# transact-relayer

Submits a user's `Verifier.transact` or `Verifier.merge` and pays its gas, so the user needs no gas from an account
linked to them: a merchant that merged its sales from its own account, say, would be named as the merge's `caller`.
In return the request pays the relayer a fee. One instance serves every chain in `CHAINS` (`backend/README.md`).

## Why it looks like this

**The fee goes in whichever slot the user leaves free.** A request can pay in two ways, and the
relayer adds up both:

- **A withdrawal to the relayer's `FEE_RECIPIENT`.** It pays `withdrawAmount` minus the protocol's withdrawal fee, as
  zERC20 or, with the unwrap intent, the underlying: the same amount either way. That fee is read with
  `withdrawFee` at submission, since the schedule applies at execution, not when the proof was made.
- **An output note to the relayer.** The wallet sends the note's opening `{value, salt}` with the
  request. The relayer recomputes `noteHash(chainId, its public key, value, tokenId, salt)` and
  requires it to equal `noteHash1` or `noteHash2`.

Both destinations sit in the proven and attested signals, and `msg.sender` is bound to neither. So
anyone may submit the same request and the relayer is still paid.

**The fee is per token, and the same for every request at a time.** A fee paid as a withdrawal is
public, and one that scaled with the transfer would reveal its amount. One that differed per user
would single out who paid it. A token with no fee is not relayed, since it would cost the relayer gas
for nothing.

**It relays the tokens `TOKENS` lists, each found by its underlying.** The settings name a token, not its id, which
each chain's factory gives in the order the tokens are made. A token made after the relayer starts is relayed within a
minute, so its settings can go out before it is made.

**It follows the gas price, and changes seldom** (`backend/common/src/fees.rs`).

- Each minute the relayer prices a relay at `FEE_GAS` of the highest gas price of the past hour. That
  is the fee in the native token, and another token's goes through Chainlink's USD feeds
  (`NATIVE_USD_FEED`, `PRICE_FEEDS`).
- The gas price is what `Sender` pays: the base fee and the tip it bids, not `eth_gasPrice`, whose tip
  can be far lower. Those tips swing by orders of magnitude (on Sepolia from 2 wei to 1 gwei), so the
  hour's highest covers them, and changes seldom.
- It aims at that cost with `FEE_MARGIN_PCT` on top, rounded up to two significant digits.
- The fee rises to the aim at once when the cost passes it, so no relay costs more than it pays. It
  falls only once it is over twice the aim.
- So a fee takes few values. The one a request pays says little more about when its proof was made
  than its transaction says already.
- A fee it replaced is still accepted for `FEE_GRACE_SECS`. A proof made before a rise, such as a
  merge waiting for the merge prover, then still goes through. For that long, a spike costs the
  relayer the difference.
- A stale or failing feed leaves its token's fee where it is.
- Without `FEE_GAS` the fees stay as `FEES` sets them, as does the fee of a token with no feed. A token whose fee
  follows the gas price needs no `FEES`: it is relayed from the first price read.
- A merge pays what a transact does, though it takes about twice the gas, and more with many inputs:
  price `FEE_GAS` by the mix.
- Only gas is priced: on an L2 the L1 data fee is left to the margin.

**Fee notes are a wallet's, and the relayer holds only its public key** (`FEE_PUBLIC_KEY`). The relayer serves the
public, so it holds nothing that spends what it earns: a relayer broken into can redirect the fees still to come, not
take those it was paid. In a deployment the key is the treasurer's wallet's, the one the wallet SDK's `seedFromSignature`
derives from the treasurer's account (`zerc20-treasurer wallet-key`). Anyone running a relayer of their own sets their
own wallet's.

**Openings are on disk before the transaction is sent.** A fee note that reaches the chain without
its opening could never be spent. So each opening is appended to `FEE_NOTES` and fsynced first. Once
the transaction is mined, the opening is appended again with the note's commitment index from
`Transacted`, and the later line wins. If the send gives up, or the relayer stops before that second
line, find the index by the note's tag in the indexer. The relayer never reads the file back:
spending fee notes needs the openings, the indexes and the wallet's key. Nothing collects them yet:
the wallet that owns them is to take them in from the file.

**Nothing is sent that would revert.** `estimate_gas` runs the whole call first. A bad proof,
attestation or root, or a spent nullifier, fails there and costs no gas. While a request is in
flight its nullifiers are claimed, and a second request with either nullifier gets 409. Otherwise,
sending one valid request many times at once would pass estimation every time, and the relayer
would pay for every copy that then reverts. Estimation cannot see a transaction from elsewhere that
spends one of the nullifiers first: the relayer's then reverts on chain. The Verifier checks
nullifiers before the proof, so that costs little gas. Nor can it see a recipient that takes the
native asset in estimation and refuses it on chain, after the proof; a revert spends no note, so the
same notes could do that again and again. Notes whose unwrap reverted on chain are not unwrapped
again, so each further try first pays to move them.

**A transact takes no more gas than its fee pays for**: `FEE_GAS` with the margin. A withdrawal of
the native asset calls its recipient, which could otherwise burn gas the fee does not pay for, in
estimation and on chain alike. One that needs more is refused; the node estimates under that limit,
and the transaction goes out with the estimate. A merge calls no address a request names, so its gas
follows its inputs alone and is not capped. Without `FEE_GAS` no gas is capped.

**A merge pays in its own slot.** Its `fee` is minted publicly to its `feeRecipient` out of the merged value
(`zkp/src/merge.rs`). The relayer takes it when the recipient is its `FEE_RECIPIENT`, less the protocol's withdrawal
fee as for a withdrawal. There is no note to record.

**Transactions go through the shared `Sender`** (see `backend/README.md`): one at a time,
each until mined, with fees raised every 30 s it stays unmined. A send runs on its own task, so a
client that hangs up does not cancel a transaction already in the pool.

## API

`GET /fee` returns `{chainId, relayer, sender, publicKey, fees: {"<tokenId>": {fee}}}`. `relayer` is
the address a withdrawal fee goes to, `sender` the account that sends the transactions, and
`publicKey` the owner of a fee note, whatever its token. The fees may differ from one call to the
next.

`POST /transact {request, feeNote?}`:

- `request` is the `TransactRequest` that `Verifier.transact` takes: `{rootIndex, proof: {pA, pB,
pC}, publicSignals: {tokenId, ...}, attestation}`. Numbers may be decimal or `0x` strings, so
  snarkjs output can be passed as is, once `pB` is put in the verifier's order.
- `feeNote` is `{value, salt}`.

It returns `{txHash, block, noteIndex1, noteIndex2}` once the transaction is mined and succeeded: its block, so a
wallet takes it for dropped only once the indexer is past that block, and the commitment indices of the two output
notes, so a wallet finds its outputs without looking up its own transaction.

`POST /merge {request}`: `request` is the `MergeRequest` that `Verifier.merge` takes, `{rootIndex, tokenId,
commitmentRoot, aspRoot, noteHash, fee, feeRecipient, nullifiers, proof: {challenge, runningCmE, cmT, runningCmW,
incomingCmW, proof}, attestation}`, with `proof` decoded from what the merge prover returns. It returns `{txHash,
block, noteIndex}`: its block and the merged note's index.

Otherwise both return:

| status | meaning                                                                                                                          |
| ------ | -------------------------------------------------------------------------------------------------------------------------------- |
| 400    | the request does not pay the fee, takes more gas than it pays for, unwraps notes whose unwrap reverted, or reverts at estimation |
| 409    | a request with one of these nullifiers is being relayed                                                                          |
| 502    | RPC failure, or the transaction reverted on chain                                                                                |
| 504    | no receipt within 120 s; the message has the transaction hash                                                                    |

## Run

| env                                |                                                                                                                        |
| ---------------------------------- | ---------------------------------------------------------------------------------------------------------------------- |
| `RPC_URL`, `VERIFIER`              |                                                                                                                        |
| `PRIVATE_KEY`                      | pays the gas; used by nothing else                                                                                     |
| `FEE_RECIPIENT`                    | where fees paid as withdrawals, and merges' fees, go; default the relayer's key                                        |
| `FEE_PUBLIC_KEY`                   | the public key of the wallet that owns the fee notes, as `/fee` publishes it                                           |
| `TOKENS`                           | `name=underlying,...`: the tokens relayed, the native asset's as `0xEeee…EEeE`, under the names the settings below use |
| `FEES`                             | `name=amount,...` in the token's base units: the fees until the gas price is read, and of tokens it does not price     |
| `FEE_GAS`                          | the gas a relay is priced at, and with the margin the most a transact may take; unset, no fee follows the gas price    |
| `NATIVE_USD_FEED`, `PRICE_FEEDS`   | Chainlink's native asset / USD feed, and `name=feed,...` of token / USD feeds                                          |
| `FEE_MARGIN_PCT`, `FEE_GRACE_SECS` | default 150, 3600                                                                                                      |
| `LISTEN`, `FEE_NOTES`              | default `127.0.0.1:8080`, `fee-notes.jsonl`                                                                            |

Back up `FEE_NOTES`. A fee note whose opening is lost is lost with it. Put TLS, CORS and rate
limits in a proxy in front.

```sh
cargo test -p zerc20-transact-relayer
```
