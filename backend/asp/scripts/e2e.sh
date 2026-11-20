#!/usr/bin/env bash
# E2E: anvil + Postgres + indexer + asp on contracts/script/IndexerFixture.s.sol events, in development mode (every
# sender passes). Checks: nothing is decided before its block is SCREEN_DELAY_SECS old; then every final position is,
# transfers approved and notes not; the root on chain is the one served; kill -9 resumes; with Chainalysis down, the
# Blocklist alone decides; a new publisher gets the same root back.
source "$(dirname "$0")/../../indexer/scripts/common.sh"

ME=0xf39Fd6e51aad88F6F4ce6aB8827279cffFb92266 # anvil account 0: owner and fixture broadcaster, unlocked
# anvil account 1 publishes, so its nonces never race the fixture's
ASP_ADDR=0x70997970C51812dc3A010C7d01b50e0d17dc79C8
ASP_KEY=0x59c6995e998f97a5a0044966f0945389dc9e86dae88c7a8412f4603b6b78690d
IDX=localhost:3100
ASP=localhost:3200

OTHER=0x3C44CdDdB6a900fa2b585dd299e03d12FA4293BC # anvil account 2, unlocked: a sender to block
send_from() {                                    # FROM TO DATA [VALUE]
  rpc eth_sendTransaction "[{\"from\":\"$1\",\"to\":\"$2\",\"data\":\"$3\",\"value\":\"${4:-0x0}\"}]" >/dev/null
}
send() { send_from "$ME" "$@"; }                                                      # TO DATA [VALUE]
call() { rpc eth_call "[{\"to\":\"$1\",\"data\":\"$(cast sig "$2")\"},\"latest\"]"; } # TO SIG
latest_on_chain() { call "$VERIFIER" 'latestAspRoot()'; }
asp() { curl -sf "$ASP/status" | jq -r "$1"; }

AP=""         # pid of the asp
start_asp() { # [ENV=VALUE...]
  env RPC_URL="$ANVIL" VERIFIER="$VERIFIER" INDEXER_URL="http://$IDX" PRIVATE_KEY=$ASP_KEY \
    PUBLISH_SECS=1 DATA_DIR="$LOGS/asp-data" LISTEN=127.0.0.1:3200 "$@" target/release/zerc20-asp >>"$LOGS/asp.log" 2>&1 &
  AP=$!
  pids+=("$AP")
  for _ in $(seq 100); do
    curl -sf "$ASP/status" >/dev/null 2>&1 && return
    sleep 0.2
  done
  fail "asp did not start: $(tail -5 "$LOGS/asp.log")"
}
# wait_asp SIZE: SIZE positions decided, and the root over them is the one on chain
wait_asp() {
  for _ in $(seq 300); do
    [ "$(asp .decided)" = "$1" ] && [ "$(asp .latest_root.index)" = "$1" ] && [ "$(asp .latest_root.root)" = "$(latest_on_chain)" ] &&
      return
    kill -0 "$AP" 2>/dev/null || fail "asp died: $(tail -5 "$LOGS/asp.log")"
    sleep 0.2
  done
  fail "asp never published a root over $1: $(curl -sf "$ASP/status"), on chain $(latest_on_chain); log: $(tail -5 "$LOGS/asp.log")"
}
# one line per position of chunk C: 1 for a transfer (tag ddf252ad in bytes 24..28 of field0), else 0
transfers() { curl -sf "$IDX/commitments/$1" | tail -c +33 | xxd -p -c 128 | cut -c49-56 | awk '{print ($1 == "ddf252ad") ? 1 : 0}'; }
# one line per position of chunk C: its bit, least significant first
bits() { curl -sf "$ASP/bitmap/$1" | xxd -b -c 1 | awk '{for (k = 8; k >= 1; k--) print substr($2, k, 1)}'; }
hdr() { curl -s -o /dev/null -D - "$ASP$1" | tr -d '\r' | grep -i "^$2:" | cut -d' ' -f2-; }
size() { curl -sf "$ASP$1" | wc -c | tr -d ' '; }

cargo build -q --release -p zerc20-indexer -p zerc20-asp
start_postgres
start_anvil
fixture "deploy()"
load_fixture
TOKEN=$(jq -r .token contracts/deployments/indexer-fixture.json)
fixture "activity(uint256,uint256)" 3 1500 # 4518 commitments: chunk 0 full, chunk 1 filling
mine 100                                   # all final
send "$VERIFIER" "$(cast calldata 'setAspPublisher(address)' $ASP_ADDR)"
start e2e_asp 3100 "$ANVIL"
wait_synced e2e_asp 3100
rm -rf "$LOGS/asp-data"
: >"$LOGS/asp.log"

echo "== the screening delay"
start_asp DEV_PASS_ALL=1 SCREEN_DELAY_SECS=3600
for _ in $(seq 100); do
  [ "$(asp .latest_root.root)" = "$(latest_on_chain)" ] && break
  sleep 0.2
done
[ "$(asp .latest_root.root)" = "$(latest_on_chain)" ] || fail "the empty tree's root was not published"
sleep 6 # a screening tick has run
[ "$(asp .decided)" = 0 ] || fail "decided before the delay: $(asp .decided)"
stop "$AP"

echo "== screening"
start_asp DEV_PASS_ALL=1 SCREEN_DELAY_SECS=0
wait_asp 4518
[ "$(transfers 0 | sort -u | tr -d '\n')" = 01 ] || fail "chunk 0 should hold transfers and notes"
for c in 0 1; do
  n=$(transfers $c | wc -l | tr -d ' ')
  diff <(transfers $c) <(bits $c | head -n "$n") >/dev/null || fail "chunk $c: the approvals are not exactly the transfers"
  if bits $c | tail -n +$((n + 1)) | grep -q 1; then fail "chunk $c: a bit past the decided positions"; fi
done

echo "== API and cache headers"
[ "$(hdr /bitmap/0 cache-control)" = "public, max-age=31536000, immutable" ] || fail "decided chunk not immutable"
[ "$(hdr /bitmap/1 cache-control)" = "public, max-age=2" ] || fail "filling chunk cache-control"
[ "$(curl -s -o /dev/null -w '%{http_code}' "$ASP/bitmap/2")" = 404 ] || fail "a chunk not there yet is not 404"
[ "$(size /bitmap/1)" = 512 ] || fail "bitmap size"
[ "$(size /chunk-roots/0)" = 32 ] || fail "chunk roots: one full chunk"
[ "$(size /page-roots)" = 0 ] || fail "page roots: no full page yet"
[ "$(size /roots/0)" = $(($(asp .roots) * 104)) ] || fail "root records"
[ "0x$(curl -sf "$ASP/roots/0" | tail -c 104 | xxd -p -c 104 | cut -c17-80)" = "$(asp .latest_root.root)" ] ||
  fail "the last root record is not /status's"

echo "== restart"
kill -9 "$AP"
wait "$AP" 2>/dev/null || true
for to in c001 c002; do # one transfer commitment each, from account 0
  send "$TOKEN" "$(cast calldata 'wrap(uint256,address)' 1 0x000000000000000000000000000000000000$to)" 0x1
done
mine 100
wait_synced e2e_asp 3100
start_asp DEV_PASS_ALL=1 SCREEN_DELAY_SECS=0
wait_asp 4520
[ "$(bits 1 | sed -n "$((4518 - 4096 + 1)),$((4520 - 4096))p" | tr -d '\n')" = 11 ] || fail "the new transfers are not approved"

echo "== Chainalysis down: the Blocklist alone decides"
stop "$AP"
send_from "$OTHER" "$TOKEN" "$(cast calldata 'wrap(uint256,address)' 1 0x000000000000000000000000000000000000c003)" 0x1
send "$TOKEN" "$(cast calldata 'wrap(uint256,address)' 1 0x000000000000000000000000000000000000c004)" 0x1
BLOCKLIST=0x$(call "0x$(call "$VERIFIER" 'factory()' | cut -c27-)" 'blocklist()' | cut -c27-)
send "$BLOCKLIST" "$(cast calldata 'setBlocked(address[],bool)' "[$OTHER]" true)"
mine 100
wait_synced e2e_asp 3100
start_asp CHAINALYSIS_API_KEY=e2e CHAINALYSIS_API_BASE_URL=http://127.0.0.1:9 SCREEN_DELAY_SECS=0 # nothing listens
wait_asp 4522
[ "$(bits 1 | sed -n "$((4520 - 4096 + 1)),$((4522 - 4096))p" | tr -d '\n')" = 01 ] ||
  fail "the blocked sender should be rejected and the other approved"
grep -q "deciding by the Blocklist alone" "$LOGS/asp.log" || fail "no fallback logged"
[ "$(asp .chainalysis_down_secs)" -gt 0 ] || fail "/status does not say Chainalysis is down"

echo "== a new publisher"
ROOT=$(latest_on_chain)
send "$VERIFIER" "$(cast calldata 'setAspPublisher(address)' $ASP_ADDR)"
[ "$(latest_on_chain)" = "0x$(printf %064d 0)" ] || fail "setAspPublisher should clear the root"
for _ in $(seq 100); do
  [ "$(latest_on_chain)" = "$ROOT" ] && break
  sleep 0.2
done
[ "$(latest_on_chain)" = "$ROOT" ] || fail "the same root was not published again"

drop_db e2e_asp
echo "ALL ASP E2E CHECKS PASSED"
