#!/usr/bin/env bash
# E2E: anvil + Postgres + indexer + root-prover on contracts/script/IndexerFixture.s.sol events, with the real
# RootDeciderVerifier and the keys in zkp/artifacts/root (`npm run artifacts:setup -- root` in zkp/, the setup the
# verifier was rendered from). Checks: the ledger accepts a proof from genesis, one from the middle of a chunk and
# one of a single step (Nova's first fold has a dummy running instance), and the indexer derives the same roots; an
# idle prover reserves nothing. About two minutes: loading the prover key takes ~7 s and each decider proof ~20 s.
source "$(dirname "$0")/../../indexer/scripts/common.sh"

# anvil account 3 proves, so its nonces never race the fixture's
PROVER=0x90F79bf6EB2c4f870365E785982E1f101E93b906
PROVER_KEY=0x7c852118294e51e653712a81e05800f419141751be58f605c371e15141b007a6
IDX=localhost:3100
export REAL_ROOT_VERIFIER=1

idx() { curl -sf "$IDX/status" | jq -r "$1"; }
nonce() { echo $(($(rpc eth_getTransactionCount "[\"$PROVER\",\"latest\"]"))); }
# wait_proved: the ledger's root covers every commitment, and the indexer derives the same root
wait_proved() {
  local n
  n=$(($(ledger_call 'nextIndex()')))
  for _ in $(seq 3600); do
    [ "$(idx .latest_root.index)" = "$n" ] && [ "$(idx .latest_root.matches)" = true ] && return
    kill -0 "$PP" 2>/dev/null || fail "root-prover died: $(tail -5 "$LOGS/root-prover.log")"
    sleep 1
  done
  fail "no proved root over $n: $(idx .latest_root); log: $(tail -5 "$LOGS/root-prover.log")"
}

[ -f zkp/artifacts/root/root_decider_pk.bin ] || fail "no keys in zkp/artifacts/root: npm run artifacts:setup -- root"
cargo build -q --release -p zerc20-indexer -p zerc20-root-prover
start_postgres
start_anvil
fixture "deploy()"
load_fixture
fixture "activity(uint256,uint256)" 1 0
mine 100 # all final
start e2e_root 3100 "$ANVIL"
wait_synced e2e_root 3100
: >"$LOGS/root-prover.log"
env RPC_URL="$ANVIL" LEDGER="$LEDGER" INDEXER_URL="http://$IDX" PRIVATE_KEY=$PROVER_KEY PROVE_SECS=1 \
  target/release/zerc20-root-prover >>"$LOGS/root-prover.log" 2>&1 &
PP=$!
pids+=("$PP")

echo "== from genesis"
wait_proved

echo "== idle"
before=$(nonce)
sleep 5
[ "$(nonce)" = "$before" ] || fail "reserved with nothing to prove"

echo "== from the middle of a chunk"
fixture "activity(uint256,uint256)" 1 0
mine 100
wait_proved

echo "== one step"
TOKEN=$(jq -r .token contracts/deployments/indexer-fixture.json)
ME=0xf39Fd6e51aad88F6F4ce6aB8827279cffFb92266 # anvil account 0, unlocked
rpc eth_sendTransaction "[{\"from\":\"$ME\",\"to\":\"$TOKEN\",\"value\":\"0x1\",\"data\":\"$(
  cast calldata 'wrap(uint256,address)' 1 0x000000000000000000000000000000000000c001
)\"}]" >/dev/null # one commitment
mine 100
wait_proved
[ "$(grep -o 'folded [0-9]* steps' "$LOGS/root-prover.log" | tail -1)" = "folded 1 steps" ] || fail "the last proof was not one step"

drop_db e2e_root
echo "ALL ROOT-PROVER E2E CHECKS PASSED"
