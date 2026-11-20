#!/usr/bin/env bash
# E2E: anvil + Postgres + indexer + three attester hosts in development mode, on contracts/script/IndexerFixture.s.sol.
# examples/e2e.rs plays the wallet and submits what the attester signs, so the contract checks it. Host A
# passes every recipient. Hosts B and C find Chainalysis down from their start: B's FALLBACK_SECS outlasts the run, so
# it answers 503; C's is short, so once it passes the Blocklist decides. KEEP=1 leaves everything running afterwards,
# for local development.
source "$(dirname "$0")/../../indexer/scripts/common.sh"

IDX=127.0.0.1:3300
A=127.0.0.1:3301
B=127.0.0.1:3302
C=127.0.0.1:3303
DEV_KEY=0x7c852118294e51e653712a81e05800f419141751be58f605c371e15141b007a6 # anvil account 3
FALLBACK_SECS=3

start_host() { # ADDR [ENV=VALUE...]
  local addr=$1
  shift
  env RPC_URL="$ANVIL" VERIFIER="$VERIFIER" INDEXER_URL="http://$IDX" DEV_SIGNING_KEY=$DEV_KEY LISTEN="$addr" "$@" \
    target/release/zerc20-attester >>"$LOGS/attester-${addr##*:}.log" 2>&1 &
  pids+=($!)
  for _ in $(seq 100); do
    curl -sf "$addr/attestation" >/dev/null 2>&1 && return
    sleep 0.2
  done
  fail "attester $addr did not start: $(tail -5 "$LOGS/attester-${addr##*:}.log")"
}

cargo build -q --release -p zerc20-indexer -p zerc20-attester --bin zerc20-indexer --bin zerc20-attester --example e2e
start_postgres
start_anvil
fixture "deploy()"
load_fixture
start e2e_attester "${IDX##*:}" "$ANVIL"
# not wait_synced, which cannot agree on an empty ledger; the example waits for each commitment itself
for _ in $(seq 100); do
  curl -sf "$IDX/status" >/dev/null 2>&1 && break
  sleep 0.2
done
start_host $A DEV_PASS_ALL=1
DOWN=(CHAINALYSIS_API_KEY=e2e CHAINALYSIS_API_BASE_URL=http://127.0.0.1:9) # nothing listens
start_host $B "${DOWN[@]}" FALLBACK_SECS=3600
start_host $C "${DOWN[@]}" FALLBACK_SECS=$FALLBACK_SECS
RPC_URL=$ANVIL VERIFIER=$VERIFIER INDEXER_URL=http://$IDX ATTESTER_A=http://$A ATTESTER_B=http://$B ATTESTER_C=http://$C \
  FALLBACK_SECS=$FALLBACK_SECS target/release/examples/e2e || fail "logs in $LOGS"
echo PASS

if [ "${KEEP:-0}" = 1 ]; then
  echo "Running until Ctrl-C: anvil $ANVIL, Verifier $VERIFIER, indexer http://$IDX,"
  echo "attester http://$A (DEV_PASS_ALL=1, signs as anvil account 3). Logs in $LOGS."
  wait
fi
