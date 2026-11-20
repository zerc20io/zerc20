#!/usr/bin/env bash
# A local zERC20 stack until Ctrl-C: anvil with the real verifiers, every backend node, the storage canister in
# PocketIC and the proving artifacts over HTTP. Writes target/dev-stack/network.json and prints the test accounts.
# Development settings, never for real funds: everyone passes screening, the attester's key is local, roots every second.
#   SPEED=fast     roots and merges land unproved, in seconds (JoinSplit and rage exit proofs stay real): the merge
#                  prover checks each witness and proves nothing, and the verifier takes merges without a proof
#   SPEED=mainnet  the nodes' own timings, as a deployment runs them: screening takes 10 min, roots 5
#   MERGE=1        the merge prover proves merges (6.3 GB of merge keys, about 16 GB of memory). Without it or
#                  SPEED=fast there is no merge prover, and wallets cannot consolidate
#   CHECKOUT=0     leaves out the checkout server, which runs otherwise once checkout/ is installed
#   FUND=0x…,0x…   gives these addresses 10000 ETH each, as anvil's own accounts have: a browser wallet's, say
# Needs anvil, forge, cast, jq, psql, docker, zkp/artifacts, the storage wasm and wallet/sdk's node_modules; forge and
# PocketIC do not run in the Claude Code sandbox. Sourced (wallet/sdk/scripts/e2e.sh), it returns once up.
source "$(dirname "${BASH_SOURCE[0]}")/../backend/indexer/scripts/common.sh"

LOGS=$ROOT/target/dev-stack
mkdir -p "$LOGS"
# anvil accounts: 0 deploys (PRIVATE_KEY, from common.sh), 1-5 run the nodes (one key per node), 6-9 are for users,
# 10 is the treasurer and 11 is a sender the ASP rejects, for rage exits
ASP_KEY=0x59c6995e998f97a5a0044966f0945389dc9e86dae88c7a8412f4603b6b78690d
PROVER_KEY=0x5de4111afa1a4b94908f83103eb1f1706367c2e68ca870fc3fb9a804cdab365a
ATTESTER_KEY=0x7c852118294e51e653712a81e05800f419141751be58f605c371e15141b007a6
RELAYER_KEY=0x47e179ec197488593b187f80a00eb0da91f1b9d0b13f8733639f19c30a34926a
DEPOSITOR_KEY=0x8b3a350cf5c34c9194ca85829a2df0ec3153be0318b5e2d3348e872092edffba
TREASURER_KEY=0xf214f2b2cd398c806f84e317254e0f0b801d0643303237d97a22a48e01628897
USER_KEYS=(
  0x92db14e403b83dfe3df233f83dfa3a0d7096f21ca9b0d6d6b8d88b2b4ec1564e
  0x4bbbf85ce3377467afe5d46f804f221813b2bb87f24d81f60f1fcdbf7cbf4356
  0xdbda1821b80551c9d65939329250298aa3472ba22feea921c0cf5d620ea67b97
  0x2a871d0798f97d79848a013d4936a73bf4cc922c825d33c1cf7073dff6d409c6
)
REJECTED_KEY=0x701b615bbdfb9de65240bc28bd21bbc0d996645a3dd57e7b12bc2bdf6f192c82
MERGE=${MERGE:-0}
SPEED=${SPEED:-}
case $SPEED in '' | fast | mainnet) ;; *) fail "SPEED is fast, mainnet or unset, not $SPEED" ;; esac
fast() { [ "$SPEED" = fast ] && echo "$1" || echo "$2"; } # YES NO
# a merge prover: proving with MERGE=1, or with SPEED=fast proving nothing
MERGE_PROVER=$([ "$MERGE" = 1 ] || [ "$SPEED" = fast ] && echo 1 || echo 0)
SKIP_MERGE_PROOF=$([ "$MERGE" != 1 ] && [ "$SPEED" = fast ] && echo 1 || echo 0)
dev() { [ "$SPEED" = mainnet ] || echo "$1"; } # VALUE: a development timing, or empty (the node's default)
# the relayers' fees: zETH (token 1) in wei, and zUSDC (token 2, over a DummyUSDC anyone may mint) in 6 decimals. Without
# FEE_GAS they do not follow the gas price, so that the e2e tests know them.
RELAYER_FEE=1000000000000000
USDC_FEE=10000
addr() { cast wallet address --private-key "$1"; }

for c in root joinsplit rageexit $([ "$MERGE" = 1 ] && echo merge); do
  [ -f "zkp/artifacts/$c/setup.json" ] || fail "no keys in zkp/artifacts/$c: npm run artifacts:setup -- $c (in zkp/)"
done
WASM=storage/target/wasm32-unknown-unknown/release/zerc20_storage.wasm
[ -f $WASM ] || fail "no storage wasm: cargo build --release --target wasm32-unknown-unknown -p zerc20_storage (in storage/)"
export POCKET_IC_BIN=${POCKET_IC_BIN_16:-$ROOT/wallet/sdk/node_modules/@dfinity/pic/pocket-ic}
[ -x "$POCKET_IC_BIN" ] || fail "no PocketIC server 16 at $POCKET_IC_BIN: npm ci in wallet/sdk, or set POCKET_IC_BIN_16"

# shellcheck disable=SC2046 # the merge prover's -p and name, or nothing
cargo build -q --release -p zerc20-indexer -p zerc20-root-prover -p zerc20-asp -p zerc20-attester \
  -p zerc20-transact-relayer -p zerc20-deposit-relayer -p zerc20-watcher -p zerc20-treasurer \
  $([ "$MERGE_PROVER" = 1 ] && echo -p zerc20-merge-prover)
# the checkout server's proof of work, run natively (its BURN_BLOCKS)
cargo build -q --release --manifest-path "$ROOT/wallet/core/Cargo.toml" --bin zerc20-burn-blocks
BURN_BLOCKS=$ROOT/wallet/core/target/release/zerc20-burn-blocks
start_postgres
# a block a second, safe a block behind, so final counts move along in seconds
anvil --silent --accounts 12 --gas-limit 100000000 --block-time 1 --slots-in-an-epoch 1 >/dev/null 2>&1 &
pids+=($!)
for _ in $(seq 50); do
  rpc eth_blockNumber '[]' >/dev/null 2>&1 && break
  sleep 0.2
done

# deposit-relayer reads balances through Multicall3, which public chains have at a fixed address and a bare anvil
# lacks: deploy viem's copy and move its code there
MULTICALL3=0xcA11bde05977b3631167028862bE2a173976CA11
code=$(cd wallet/sdk && node -e "import('./node_modules/viem/_esm/constants/contracts.js').then((m) => process.stdout.write(m.multicall3Bytecode))")
tx=$(rpc eth_sendTransaction "[{\"from\":\"$(addr "$PRIVATE_KEY")\",\"data\":\"$code\",\"gas\":\"0x1000000\"}]")
for _ in $(seq 50); do
  created=$(rpc eth_getTransactionReceipt "[\"$tx\"]" | jq -r '.contractAddress // empty' || true)
  [ -n "$created" ] && break
  sleep 0.2
done
rpc anvil_setCode "[\"$MULTICALL3\",\"$(rpc eth_getCode "[\"$created\",\"latest\"]")\"]" >/dev/null || true
[ "$(rpc eth_getCode "[\"$MULTICALL3\",\"latest\"]")" != 0x ] || fail "Multicall3 is not deployed"

TEN_THOUSAND_ETH=0x21e19e0c9bab2400000
FUND=${FUND:-}
for a in ${FUND//,/ }; do
  [[ $a =~ ^0x[0-9a-fA-F]{40}$ ]] || fail "FUND is addresses, comma-separated: not $a"
  rpc anvil_setBalance "[\"$a\",\"$TEN_THOUSAND_ETH\"]" >/dev/null || true # its result is null
  [ "$(rpc eth_getBalance "[\"$a\",\"latest\"]")" = $TEN_THOUSAND_ETH ] || fail "could not fund $a"
done

forge_deploy() {
  (cd contracts && forge script script/Deploy.s.sol --rpc-url "$ANVIL" "$@") >>"$LOGS/forge.log" 2>&1 ||
    fail "forge script Deploy.s.sol $*: $(tail -5 "$LOGS/forge.log")"
}
: >"$LOGS/forge.log"
forge_deploy --sig "bootstrapAnvil()"
ASP_PUBLISHER=$(addr $ASP_KEY) ATTESTERS=$(addr $ATTESTER_KEY) GUARDIANS=$(addr $PROVER_KEY) DEPLOY_SALT="dev-stack" \
DEV_ACCEPT_ALL_ROOTS=$(fast true false) DEV_ACCEPT_ALL_MERGES=$([ "$SKIP_MERGE_PROOF" = 1 ] && echo true || echo false) \
DUMMY_USDC=true forge_deploy --broadcast --private-key "$PRIVATE_KEY"
D=contracts/deployments/31337.json
LEDGER=$(jq -r .ledger $D) VERIFIER=$(jq -r .verifier $D)
# what the relayers relay, by underlying: the native asset's stand-in and the DummyUSDC
TOKENS=ETH=0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE,USDC=$(jq -r .usdc $D)
# what the treasurer tops a node account up to, and the watcher warns below a quarter of
TOP_UP_TO=1000000000000000000

IDX=127.0.0.1:3500
fresh_db dev_stack
env DATABASE_URL="$PG/dev_stack" RPC_URLS="$ANVIL" LEDGER="$LEDGER" VERIFIER="$VERIFIER" START_BLOCK=0 REORG_DEPTH=2 \
  POLL_SECS="$(dev 1)" LISTEN=$IDX target/release/zerc20-indexer >"$LOGS/indexer.log" 2>&1 &
pids+=($!)
env RPC_URL="$ANVIL" LEDGER="$LEDGER" INDEXER_URL="http://$IDX" PRIVATE_KEY=$PROVER_KEY PROVE_SECS="$(dev 1)" DEV_SKIP_PROOF="$(fast 1 0)" \
  target/release/zerc20-root-prover >"$LOGS/root-prover.log" 2>&1 &
pids+=($!)
rm -rf "$LOGS/asp-data"
env RPC_URL="$ANVIL" VERIFIER="$VERIFIER" INDEXER_URL="http://$IDX" PRIVATE_KEY=$ASP_KEY DEV_PASS_ALL=1 \
  DEV_REJECT="$(addr "$REJECTED_KEY")" SCREEN_DELAY_SECS="$(dev 0)" PUBLISH_SECS="$(dev 1)" DATA_DIR="$LOGS/asp-data" LISTEN=127.0.0.1:3501 target/release/zerc20-asp >"$LOGS/asp.log" 2>&1 &
pids+=($!)
env RPC_URL="$ANVIL" VERIFIER="$VERIFIER" INDEXER_URL="http://$IDX" DEV_SIGNING_KEY=$ATTESTER_KEY DEV_PASS_ALL=1 \
  LISTEN=127.0.0.1:3502 target/release/zerc20-attester >"$LOGS/attester.log" 2>&1 &
pids+=($!)
rm -f "$LOGS/fee-notes.jsonl" "$LOGS/registrations.jsonl"
env RPC_URL="$ANVIL" VERIFIER="$VERIFIER" PRIVATE_KEY=$RELAYER_KEY TOKENS="$TOKENS" FEES="ETH=$RELAYER_FEE,USDC=$USDC_FEE" FEE_RECIPIENT="$(addr "$TREASURER_KEY")" \
  FEE_PUBLIC_KEY="$(PRIVATE_KEY=$TREASURER_KEY target/release/zerc20-treasurer wallet-key)" FEE_NOTES="$LOGS/fee-notes.jsonl" \
  LISTEN=127.0.0.1:3503 target/release/zerc20-transact-relayer >"$LOGS/transact-relayer.log" 2>&1 &
pids+=($!)
env RPC_URL="$ANVIL" DEPOSIT_ADDRESS_FACTORY="$(jq -r .depositAddressFactory $D)" PRIVATE_KEY=$DEPOSITOR_KEY TOKENS="$TOKENS" FEES="ETH=$RELAYER_FEE,USDC=$USDC_FEE" POLL_SECS="$(dev 1)" \
  FEE_RECIPIENT="$(addr "$TREASURER_KEY")" STORE="$LOGS/registrations.jsonl" LISTEN=127.0.0.1:3504 \
  target/release/zerc20-deposit-relayer >"$LOGS/deposit-relayer.log" 2>&1 &
pids+=($!)
# the relayers' zETH fees unwrapped at each tick; no SWEEP_TO
env RPC_URL="$ANVIL" VERIFIER="$VERIFIER" PRIVATE_KEY=$TREASURER_KEY TOP_UP_TO=$TOP_UP_TO \
  KEEP=100000000000000000000000 TICK_SECS="$(dev 2)" UNWRAP_SECS="$(dev 2)" \
  ACCOUNTS="root-prover=$(addr $PROVER_KEY),asp=$(addr $ASP_KEY),transact-relayer=$(addr $RELAYER_KEY),deposit-relayer=$(addr $DEPOSITOR_KEY)" \
  target/release/zerc20-treasurer >"$LOGS/treasurer.log" 2>&1 &
pids+=($!)
# no Slack: what it would post goes to its log
rm -rf "$LOGS/watcher-data" && mkdir "$LOGS/watcher-data"
env CHAIN=local RPC_URL="$ANVIL" VERIFIER="$VERIFIER" INDEXER_URL="http://$IDX" ASP_URL=http://127.0.0.1:3501 \
  DEPOSIT_ADDRESS_FACTORY="$(jq -r .depositAddressFactory $D)" START_BLOCK=0 REORG_DEPTH=2 DATA_DIR="$LOGS/watcher-data" \
  CHECK_SECS="$(dev 2)" WATCH_ADDRESSES="root-prover=$(addr $PROVER_KEY),asp=$(addr $ASP_KEY)" TOP_UP_TO=$TOP_UP_TO \
  target/release/zerc20-watcher >"$LOGS/watcher.log" 2>&1 &
pids+=($!)

# storage in PocketIC (live, behind an HTTP gateway) and the artifacts over HTTP, from one Node process
rm -f "$LOGS/storage.json"
# exec, so the pid recorded below is node's own and stopping it stops PocketIC
# shellcheck disable=SC2016 # the script is JavaScript: its $ are its own
(cd wallet/sdk && WASM="$ROOT/$WASM" ARTIFACTS="$ROOT/zkp/artifacts" OUT="$LOGS/storage.json" exec node --input-type=module -e '
import { createServer } from "node:http";
import { readFile, writeFile } from "node:fs/promises";
import { PocketIc, PocketIcServer, SubnetStateType } from "@dfinity/pic";
import { IDL } from "@icp-sdk/core/candid";
import { Principal } from "@icp-sdk/core/principal";
const server = await PocketIcServer.start({ ttl: 7 * 86400 });
const pic = await PocketIc.create(server.getUrl(), {
  application: [{ state: { type: SubnetStateType.New } }],
  testThresholdKeys: { state: { type: SubnetStateType.New } },
});
const port = await pic.makeLive();
const [subnet] = await pic.getApplicationSubnets();
const canisterId = await pic.createCanister({ targetSubnetId: subnet.id });
const InitArgs = IDL.Record({ auditor: IDL.Principal, vetkd_key_name: IDL.Text });
// no one calls as the management canister, so nothing is audited here
const arg = IDL.encode([InitArgs], [{ auditor: Principal.managementCanister(), vetkd_key_name: "test_key_1" }]);
await pic.installCode({ canisterId, wasm: process.env.WASM, arg });
createServer(async (req, res) => {
  res.setHeader("access-control-allow-origin", "*");
  const path = new URL(req.url, "http://x").pathname;
  if (!/^\/(joinsplit|rageexit)\/[a-z_]+\.(wasm|zkey)$/.test(path)) return res.writeHead(404).end();
  res.end(await readFile(process.env.ARTIFACTS + path).catch(() => ""));
}).listen(3505, "127.0.0.1");
await writeFile(process.env.OUT, JSON.stringify({ host: `http://127.0.0.1:${port}`, canisterId: canisterId.toText() }));
// the server is a child process: stop it with this one
process.on("SIGTERM", async () => {
  await pic.tearDown().catch(() => {});
  await server.stop().catch(() => {});
  process.exit(0);
});
await new Promise(() => {});
') >"$LOGS/storage.log" 2>&1 &
pids+=($!)
for _ in $(seq 300); do
  [ -s "$LOGS/storage.json" ] && break
  sleep 0.2
done
[ -s "$LOGS/storage.json" ] || fail "storage did not start: $(tail -5 "$LOGS/storage.log")"
if [ "$MERGE_PROVER" = 1 ]; then
  # serves every chain and reads none; it proves once the merge keys are in, which takes a while
  env DEV_ENCLAVE=1 DEV_SKIP_PROOF="$SKIP_MERGE_PROOF" ARTIFACTS_DIR=zkp/artifacts/merge LISTEN=127.0.0.1:3506 \
    target/release/zerc20-merge-prover >"$LOGS/merge-prover.log" 2>&1 &
  pids+=($!)
fi
for u in 3500/status 3501/status 3502/attestation 3503/fee $([ "$MERGE_PROVER" = 1 ] && echo 3506/status); do
  for _ in $(seq 100); do
    curl -sf "127.0.0.1:$u" >/dev/null 2>&1 && break
    sleep 0.2
  done
done

circuit() { # NAME: its artifacts over HTTP, pinned by setup.json
  local s=zkp/artifacts/$1/setup.json
  jq -n --arg n "$1" --arg w "$(jq -r ".files[\"$1.wasm\"].sha256" "$s")" --arg z "$(jq -r ".files[\"$1.zkey\"].sha256" "$s")" \
    '{wasm: "http://127.0.0.1:3505/\($n)/\($n).wasm", zkey: "http://127.0.0.1:3505/\($n)/\($n).zkey", wasmSha256: $w, zkeySha256: $z}'
}
NETWORK=$LOGS/network.json
jq -n --slurpfile storage "$LOGS/storage.json" --arg rpc "$ANVIL" --arg verifier "$VERIFIER" --arg merge "$MERGE_PROVER" \
  --arg factory "$(jq -r .depositAddressFactory $D)" --argjson joinsplit "$(circuit joinsplit)" --argjson rageexit "$(circuit rageexit)" '{
  name: "local",
  chains: [{
    chainId: "31337", rpcUrls: [$rpc], verifier: $verifier, depositAddressFactory: $factory,
    indexer: "http://127.0.0.1:3500", asp: "http://127.0.0.1:3501", attester: "http://127.0.0.1:3502",
    attesterTrust: {development: true}, transactRelayer: "http://127.0.0.1:3503", depositRelayer: "http://127.0.0.1:3504"
  }],
  storage: $storage[0],
  circuits: {joinsplit: $joinsplit, rageexit: $rageexit}
} + if $merge == "1" then {mergeProver: {url: "http://127.0.0.1:3506", trust: {development: true}}} else {} end' >"$NETWORK"

# sourced: leave the stack to the caller
[[ "${BASH_SOURCE[0]}" != "$0" ]] && return 0

# the checkout server, for the wallet's For shops screen and its payment pages, once checkout/ is installed and built
CHECKOUT_INFO=
if [ "${CHECKOUT:-1}" != 0 ] && [ -d checkout/node_modules ]; then
  fresh_db checkout
  (cd checkout && exec env NETWORK="$NETWORK" DATABASE_URL="$PG/checkout" PUBLIC_URL=http://127.0.0.1:3507 LISTEN=127.0.0.1:3507 \
    SESSION_SECRET=dev-stack-only-dev-stack-only-dev-stack PRIVATE_WEBHOOKS=1 REFRESH_SECS=1 BURN_BLOCKS="$BURN_BLOCKS" \
    node server/main.ts) >"$LOGS/checkout.log" 2>&1 &
  pids+=($!)
  for _ in $(seq 100); do
    curl -sf 127.0.0.1:3507/api/status >/dev/null 2>&1 && break
    sleep 0.2
  done
  CHECKOUT_INFO="
  checkout:  http://127.0.0.1:3507, frontend/wallet's checkout server on this network (logs in $LOGS/checkout.log)"
fi

cat <<INFO

zERC20 dev stack is up (logs in $LOGS).
  network:   $NETWORK   (Wallet.open({ network: networkFromJson(text), ... }))
  chain:     $ANVIL, chain id 31337; zETH (token 1) at $(jq -r .zeth $D), zUSDC (token 2) at $(jq -r .zusdc $D)$([ -n "$SPEED" ] && echo "; SPEED=$SPEED")
  USDC:      DummyUSDC at $(jq -r .usdc $D): anyone may mint (the demo has a button)
  relayer:   flat fee $RELAYER_FEE wei of zETH, $USDC_FEE of zUSDC$([ "$MERGE" = 1 ] && echo "
  prover:    http://127.0.0.1:3506, the merge prover (it proves once its log says it holds the merge keys)")$([ "$SKIP_MERGE_PROOF" = 1 ] && echo "
  prover:    http://127.0.0.1:3506, the merge prover, checking merges and proving none (SPEED=fast)")$CHECKOUT_INFO
  accounts (anvil, 10000 ETH each), for wallets:
$(for k in "${USER_KEYS[@]}"; do echo "    $(addr "$k")  $k"; done)$([ -n "$FUND" ] && echo "
  funded (FUND, 10000 ETH each):" && tr , '\n' <<<"$FUND" | sed 's/^/    /')
Ctrl-C stops everything.
INFO
wait
