#!/usr/bin/env bash
# E2E: anvil + Postgres, real ledger/verifier events from contracts/script/IndexerFixture.s.sol.
# Checks: the indexer agrees with the ledger's nextIndex / hashChain / rootState and with every NullifierSpent log;
# chunk cache headers follow finality; a reorg ends where a from-scratch indexer ends; kill -9 resumes; a recovery
# steps the root stream back, and a from-scratch indexer ends there too; a final-only indexer ends below the window
# with the same data and no window headers.
source "$(dirname "$0")/common.sh"

build
start_postgres
start_anvil
fixture "deploy()"
load_fixture
fixture "activity(uint256,uint256)" 3 1500 # 3 x 1506 commitments: chunk 0 full, chunk 1 filling; 18 nullifiers, 3 roots

echo "== sync"
start e2e_a 3100 "$ANVIL"
A=$SP
wait_synced e2e_a 3100
echo "state: $(indexer_state e2e_a)"

echo "== API and cache headers"
hdr() { curl -s -o /dev/null -D - "localhost:3100$1" | tr -d '\r' | grep -i "^$2:" | cut -d' ' -f2-; }
size() { curl -sf "localhost:3100$1" | wc -c | tr -d ' '; }
[ "$(hdr /commitments/0 cache-control)" = "public, max-age=5" ] || fail "fresh full chunk: $(hdr /commitments/0 cache-control)"
mine 100 # the chunk falls out of the reorg window
for _ in $(seq 100); do
  [ "$(hdr /commitments/0 cache-control)" = "public, max-age=31536000, immutable" ] && break
  sleep 0.2
done
[ "$(hdr /commitments/0 cache-control)" = "public, max-age=31536000, immutable" ] || fail "final chunk not immutable"
[ "$(hdr /tags/0 cache-control)" = "public, max-age=31536000, immutable" ] || fail "final tags not immutable"
[ "$(hdr /commitments/1 cache-control)" = "public, max-age=2" ] || fail "filling chunk cache-control"
[ "$(hdr /commitments/2 cache-control)" = "no-store" ] || fail "a chunk not there yet must not be cached"
[ "$(curl -s -o /dev/null -w '%{http_code}' localhost:3100/commitments/2)" = 404 ] || fail "a chunk not there yet is not 404"
[ "$(curl -s -o /dev/null -D - -H 'Accept-Encoding: gzip' localhost:3100/commitments/0 | tr -d '\r' | grep -i '^content-encoding:' | cut -d' ' -f2)" = gzip ] ||
  fail "chunk not gzipped"
[ "$(size /commitments/0)" = $((32 + 4096 * 128)) ] || fail "chunk size"
[ "$(size /tags/0)" = $((4096 * 4)) ] || fail "tags size"
[ "$(size /blocks/1)" = $(((4518 - 4096) * 8)) ] || fail "blocks size"
[ $((16#$(curl -sf localhost:3100/blocks/0 | xxd -p -c 8 | tail -1))) = $(($(rpc eth_getLogs "[{\"address\":\"$LEDGER\",\"topics\":[\"$(
  cast keccak 'Committed(uint64,uint256[4])'
)\",\"$(printf 0x%064x 4095)\"],\"fromBlock\":\"0x0\",\"toBlock\":\"latest\"}]" | jq -r '.[0].blockNumber'))) ] ||
  fail "block of commitment 4095"
[ "$(size /times/1)" = $(((4518 - 4096) * 8)) ] || fail "times size"
B4095=$((16#$(curl -sf localhost:3100/blocks/0 | xxd -p -c 8 | tail -1)))
[ $((16#$(curl -sf localhost:3100/times/0 | xxd -p -c 8 | tail -1))) = $(($(rpc eth_getBlockByNumber "[\"$(printf 0x%x "$B4095")\",false]" | jq -r .timestamp))) ] ||
  fail "time of commitment 4095"
[ "$(size /commitments/1)" = $((32 + (4518 - 4096) * 128)) ] || fail "filling chunk size"
[ "$(size /nullifiers/0)" = $((18 * 8)) ] || fail "filling nullifier chunk size"
[ "$(size /chunk-roots/0)" = 32 ] || fail "chunk roots: one full chunk"
[ "$(hdr /chunk-roots/0 cache-control)" = "public, max-age=2" ] || fail "a filling page of chunk roots is live"
[ "$(size /page-roots)" = 0 ] || fail "page roots: no full page yet"
[ "$(curl -sf localhost:3100/nullifiers/0 | xxd -p -c 8 | head -1)" = "$(chain_nullifiers | head -1 | cut -c1-16)" ] ||
  fail "nullifier prefixes differ from the chain"
# the made-up roots are listed, with the partial chunk's and page's roots, and flagged as not this indexer's
[ "$(size /roots/0)" = $((3 * 105)) ] || fail "root entries"
[ "$(curl -sf localhost:3100/roots/0 | xxd -p -c 105 | cut -c209-210 | sort -u)" = 00 ] || fail "roots should not match"
LAST=$(curl -sf localhost:3100/roots/0 | xxd -p -c 105 | tail -1)
[ "${LAST:0:16}" = "$(printf %016x 4518)" ] && [[ ${LAST:80:64} =~ [1-9a-f] && ${LAST:144:64} =~ [1-9a-f] ]] ||
  fail "last root entry: $LAST"
# none is usable, and the first is where an emergency would bound the ledger
curl -sf localhost:3100/status | jq -e '.roots == 3 and .latest_root == null and .mismatch.index == 1506' >/dev/null ||
  fail "roots in status: $(curl -sf localhost:3100/status | jq -c '{latest_root, mismatch}')"
curl -sf localhost:3100/status | jq -e '.commitments_final == 4518 and .nullifiers_final == 18' >/dev/null ||
  fail "final counts: $(curl -sf localhost:3100/status)"
# the made-up roots are not this indexer's, so no wait is measured from them
curl -sf localhost:3100/status | jq -e '.settle_secs == null' >/dev/null ||
  fail "settle_secs from roots the indexer does not derive: $(curl -sf localhost:3100/status | jq .settle_secs)"

echo "== reorg"
SNAP=$(rpc evm_snapshot '[]')
fixture "activity(uint256,uint256)" 1 10
wait_synced e2e_a 3100
BEFORE=$(indexer_state e2e_a)
[ "$(rpc evm_revert "[\"$SNAP\"]")" = true ] || fail "evm_revert"
fixture "activity(uint256,uint256)" 1 20 # same height, other content
wait_synced e2e_a 3100
[ "$(indexer_state e2e_a)" != "$BEFORE" ] || fail "state unchanged by the reorg"
grep -q "reorg at" "$LOGS/indexer-e2e_a.log" || fail "no rollback logged"
start e2e_b 3101 "$ANVIL"
B=$SP
wait_synced e2e_b 3101
[ "$(fingerprint e2e_a)" = "$(fingerprint e2e_b)" ] || fail "reorged indexer differs from a fresh one"
stop "$B"

echo "== restart"
kill -9 "$A"
wait "$A" 2>/dev/null || true
fixture "activity(uint256,uint256)" 1 5
KEEP_DB=1 start e2e_a 3100 "$ANVIL"
A=$SP
wait_synced e2e_a 3100

echo "== recovery"
read -r INDEX ROOT < <(curl -sf localhost:3100/status | jq -r '.mismatch | "\(.index) \(.root)"')
fixture "recover(uint64,uint256)" "$INDEX" "$ROOT" # back to the first root, which is proved a second time below
fixture "activity(uint256,uint256)" 1 0
wait_synced e2e_a 3100
[ "$(q e2e_a "SELECT count(*) FROM roots WHERE new_index = $INDEX")" = 2 ] || fail "the recovery is not a root entry"
# the new era starts at the recovery, whose made-up root is again not this indexer's
curl -sf localhost:3100/status | jq -e ".roots == 7 and .mismatch.index == $INDEX and .indexer.gap_repairs == 0" >/dev/null ||
  fail "status after the recovery: $(curl -sf localhost:3100/status | jq -c '{roots, mismatch, gaps: .indexer.gap_repairs}')"
start e2e_b 3101 "$ANVIL"
B=$SP
wait_synced e2e_b 3101
[ "$(fingerprint e2e_a)" = "$(fingerprint e2e_b)" ] || fail "an indexer through the recovery differs from a fresh one"
stop "$B"

echo "== final only"
mine 100 # the recovery falls out of the reorg window
# anvil's safe block trails the head by 64, so the window starts at head - 64 and a final-only indexer stops below it
start e2e_f 3102 "$ANVIL" FINAL_ONLY=1
F=$SP
for _ in $(seq 300); do
  [ "$(curl -sf localhost:3102/status | jq -r .indexer.cursor 2>/dev/null || true)" = $(($(head_block) - 65)) ] &&
    [ "$(fingerprint e2e_f)" = "$(fingerprint e2e_a)" ] && break
  kill -0 "$F" 2>/dev/null || fail "e2e_f: indexer died: $(tail -5 "$LOGS/indexer-e2e_f.log")"
  sleep 0.2
done
[ "$(fingerprint e2e_f)" = "$(fingerprint e2e_a)" ] || fail "a final-only indexer differs: $(curl -sf localhost:3102/status | jq -c .indexer)"
[ "$(curl -sf localhost:3102/status | jq -r .indexer.cursor)" = $(($(head_block) - 65)) ] || fail "a final-only indexer passed the final block"
[ "$(q e2e_f 'SELECT count(*) FROM blocks')" = 0 ] || fail "a final-only indexer read the window's headers"
stop "$F"

for n in e2e_a e2e_b e2e_f; do drop_db $n; done
echo "ALL E2E CHECKS PASSED"
