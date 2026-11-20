#!/usr/bin/env bash
# Chaos E2E: through flaky, lagging, pruned and silently log-dropping RPCs, the indexer must end exactly where a
# clean run ends, and agree with the chain.
# usage: scripts/e2e_chaos.sh [ROUNDS=20] [SPRAY=300]
source "$(dirname "$0")/common.sh"
ROUNDS=${1:-20}
SPRAY=${2:-300}
nonzero() { [ "$(echo "$1" | jq -r ".\"$2\"")" -gt 0 ] || fail "fault '$2' was never injected: $1"; }

build
start_postgres
start_anvil
fixture "deploy()"
load_fixture
echo "building chain: $ROUNDS rounds, $SPRAY extra transfers each"
fixture "activity(uint256,uint256)" "$ROUNDS" "$SPRAY"
mine 100

echo "== baseline (direct anvil)"
start chaos_base 3200 "$ANVIL"
wait_synced chaos_base 3200
stop "$SP"
CLEAN=$(fingerprint chaos_base)

echo "== backfill through silent loss, lag, pruned state and errors"
# 8-block ranges make enough getLogs calls for every fault to fire; ranges over 6 blocks always lose logs
proxy 8546 PDROP=0.2 PTRUNC=0.2 PEMPTY=0.1 DROP_WIDE=6 NOARCHIVE=32 PLAG=0.1 LAG=2 P5XX=0.03
start chaos_loss 3200 http://127.0.0.1:8546 BATCH_BLOCKS=8 BATCH_MAX_BLOCKS=8
wait_synced chaos_loss 3200
[ "$(fingerprint chaos_loss)" = "$CLEAN" ] || fail "differs from the clean run"
S=$(curl -sf localhost:8546/_stats)
echo "proxy stats: $S"
for k in dropped_mid truncated emptied wide_dropped no_state lagged_requests 5xx; do nonzero "$S" $k; done
curl -sf localhost:3200/status | jq -e '.indexer.gap_repairs > 0' >/dev/null || fail "no gap repair recorded"
! grep -q "reorg at" "$LOGS/indexer-chaos_loss.log" || fail "false rollback: $(grep 'reorg at' "$LOGS/indexer-chaos_loss.log" | head -2)"
echo "repairs: $(curl -sf localhost:3200/status | jq -c '.indexer | {gap_repairs, last_gap}')"
stop "$SP"

echo "== following the tip through truncated and empty answers"
proxy 8547 PTRUNC=0.3 PEMPTY=0.1 PLAG=0.2 LAG=2
start chaos_tip 3200 http://127.0.0.1:8547
wait_synced chaos_tip 3200
fixture "activity(uint256,uint256)" 5 50
wait_synced chaos_tip 3200
stop "$SP"
start chaos_base2 3200 "$ANVIL"
wait_synced chaos_base2 3200
stop "$SP"
[ "$(fingerprint chaos_tip)" = "$(fingerprint chaos_base2)" ] || fail "tip run differs from a clean run"
curl -sf localhost:8547/_stats | jq -e '.truncated > 0 and .emptied > 0' >/dev/null || fail "tip faults not injected"

for n in chaos_base chaos_loss chaos_tip chaos_base2; do drop_db $n; done
echo "ALL CHAOS CHECKS PASSED"
