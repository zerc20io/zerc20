# shellcheck shell=bash
# Shared by e2e.sh and e2e_chaos.sh: anvil, a Postgres container, the IndexerFixture forge script, and the checks
# that compare an indexer with the chain. Needs anvil, forge, cast, curl, jq, psql, pg_isready, docker (postgres:16).
set -euo pipefail
# no forge here reaches the network: decoding a trace otherwise asks Sourcify about every address in it, one by one,
# and the fixture's sprays hold thousands
export FOUNDRY_OFFLINE=true
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$ROOT"
PGPORT=${PGPORT:-5433}
PG="postgres://postgres:pw@localhost:$PGPORT"
ANVIL=http://127.0.0.1:8545
export PRIVATE_KEY=0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80 # anvil account 0
BIN=target/release/zerc20-indexer
PROXY=target/release/examples/chaos_proxy
LOGS=$ROOT/target/indexer-e2e # indexer and forge logs
mkdir -p "$LOGS"

pids=()
cleanup() { for p in "${pids[@]:-}"; do kill "$p" 2>/dev/null || true; done; }
trap cleanup EXIT
fail() {
  echo "FAIL: $*" >&2
  exit 1
}

# (cast's HTTP client aborts inside the Claude sandbox, so RPC goes through curl; cast only hashes)
rpc() {
  curl -sf -H 'content-type: application/json' "$ANVIL" -d "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"$1\",\"params\":$2}" |
    jq -e -r '.result // empty | if type == "string" then . else tojson end'
}

start_postgres() {
  docker start zerc20-indexer-pg >/dev/null 2>&1 ||
    docker run -d --name zerc20-indexer-pg -e POSTGRES_PASSWORD=pw -p "$PGPORT:5432" postgres:16 >/dev/null
  for _ in $(seq 150); do
    psql "$PG/postgres" -qtAc 'SELECT 1' >/dev/null 2>&1 && return
    sleep 0.2
  done
  fail "postgres did not come up on $PGPORT"
}
drop_db() { PGOPTIONS='-c client_min_messages=warning' psql "$PG/postgres" -qc "DROP DATABASE IF EXISTS $1 WITH (FORCE)"; }
fresh_db() { drop_db "$1" && psql "$PG/postgres" -qc "CREATE DATABASE $1"; }

start_anvil() {
  anvil --silent --gas-limit 100000000 >/dev/null 2>&1 &
  pids+=($!)
  for _ in $(seq 50); do
    rpc eth_blockNumber '[]' >/dev/null 2>&1 && break
    sleep 0.2
  done
  rpc eth_blockNumber '[]' >/dev/null 2>&1 || fail "anvil did not start"
  # the fixture deploys through the CREATE3 factory
  (cd contracts && forge script script/Deploy.s.sol --sig "bootstrapAnvil()" --rpc-url "$ANVIL") >"$LOGS/forge.log" 2>&1 ||
    fail "forge script bootstrapAnvil(): $(tail -5 "$LOGS/forge.log")"
}
head_block() { echo $(($(rpc eth_blockNumber '[]'))); }
mine() { rpc anvil_mine "[\"$(printf 0x%x "$1")\"]" >/dev/null || true; } # returns null

# fixture "deploy()" | fixture "activity(uint256,uint256)" ROUNDS SPRAY
# --slow: sent all at once, a spray that no longer fits the block stays pending, and automine waits for a next tx
# that never comes
fixture() {
  (cd contracts && forge script script/IndexerFixture.s.sol --tc IndexerFixture --rpc-url "$ANVIL" --broadcast --slow --sig "$@") >"$LOGS/forge.log" 2>&1 ||
    fail "forge script $*: $(tail -5 "$LOGS/forge.log")"
}
load_fixture() {
  local f=contracts/deployments/indexer-fixture.json
  LEDGER=$(jq -r .ledger $f) VERIFIER=$(jq -r .verifier $f) START=$(jq -r .startBlock $f)
}

build() { cargo build -q --release -p zerc20-indexer --bin zerc20-indexer --example chaos_proxy; }

SP="" # pid of the last indexer started
# start NAME PORT URLS [ENV=VALUE...]   (fresh database and log unless KEEP_DB=1)
start() {
  local name=$1 port=$2 urls=$3
  shift 3
  [ "${KEEP_DB:-0}" = 1 ] || { fresh_db "$name" && : >"$LOGS/indexer-$name.log"; }
  env DATABASE_URL="$PG/$name" RPC_URLS="$urls" LEDGER="$LEDGER" VERIFIER="$VERIFIER" START_BLOCK="$START" \
    REORG_DEPTH=64 MISSING_GRACE_SECS=3 RPC_TIMEOUT_SECS=5 POLL_SECS=1 LISTEN="127.0.0.1:$port" "$@" \
    "$BIN" >>"$LOGS/indexer-$name.log" 2>&1 &
  SP=$!
  pids+=("$SP")
}
stop() {
  kill "$1" 2>/dev/null || true
  wait "$1" 2>/dev/null || true
}
proxy() { # PORT [ENV=VALUE...]
  local port=$1
  shift
  env UPSTREAM="$ANVIL" LISTEN="127.0.0.1:$port" "$@" "$PROXY" >/dev/null 2>&1 &
  pids+=($!)
  for _ in $(seq 50); do
    curl -sf "localhost:$port/_stats" >/dev/null 2>&1 && return
    sleep 0.1
  done
  fail "proxy $port did not start"
}

# ---- the chain's view
ledger_call() { rpc eth_call "[{\"to\":\"$LEDGER\",\"data\":\"$(cast sig "$1")\"},\"latest\"]"; }
chain_nullifiers() { # one hex nullifier per line, in order
  rpc eth_getLogs "[{\"address\":\"$VERIFIER\",\"topics\":[\"$(cast keccak 'NullifierSpent(uint256)')\"],\"fromBlock\":\"0x0\",\"toBlock\":\"latest\"}]" |
    jq -r '.[].topics[1][2:]'
}
# "<commitments> <hash chain> <root index> <nullifier digest>" as the ledger and the logs say
chain_state() {
  local rs
  rs=$(ledger_call 'rootState()')
  echo "$(($(ledger_call 'nextIndex()'))) $(ledger_call 'hashChain()' | cut -c3-) $((16#${rs:2:64})) $(chain_nullifiers | shasum | cut -c1-40)"
}

# ---- the indexer's view (database NAME)
q() { psql "$PG/$1" -qtAc "$2"; }
indexer_state() {
  echo "$(q "$1" 'SELECT count(*) FROM commitments') $(q "$1" "SELECT encode(hash_chain, 'hex') FROM commitments ORDER BY idx DESC LIMIT 1") $(q "$1" 'SELECT COALESCE((SELECT new_index FROM roots ORDER BY pos DESC LIMIT 1), 0)') $(q "$1" "SELECT encode(nullifier, 'hex') FROM nullifiers ORDER BY pos" | shasum | cut -c1-40)"
}
# everything derived, for comparing two indexers of the same chain
fingerprint() {
  q "$1" "SELECT md5(concat_ws('|',
    (SELECT string_agg(encode(hash_chain, 'hex'), ',' ORDER BY idx) FROM commitments),
    (SELECT string_agg(encode(nullifier, 'hex'), ',' ORDER BY pos) FROM nullifiers),
    (SELECT string_agg(pos || ':' || new_index || ':' || encode(local_root, 'hex') || ':' || COALESCE(encode(partial_chunk_root, 'hex'), '')
      || ':' || COALESCE(encode(partial_page_root, 'hex'), '') || ':' || COALESCE(block_time::text, ''), ',' ORDER BY pos) FROM roots),
    (SELECT string_agg(encode(root, 'hex'), ',' ORDER BY chunk) FROM chunk_roots),
    (SELECT string_agg(encode(root, 'hex'), ',' ORDER BY page) FROM page_roots)))"
}

# wait_synced NAME PORT: the indexer has reached the head and agrees with the chain
wait_synced() {
  local name=$1 port=$2 want got cursor
  for _ in $(seq 1500); do
    want=$(chain_state)
    cursor=$(curl -sf "localhost:$port/status" | jq -r .indexer.cursor 2>/dev/null || true)
    if [ "$cursor" = "$(head_block)" ]; then
      got=$(indexer_state "$name")
      [ "$got" = "$want" ] && return 0
    fi
    kill -0 "$SP" 2>/dev/null || fail "$name: indexer died: $(tail -5 "$LOGS/indexer-$name.log")"
    sleep 0.2
  done
  fail "$name: never agreed with the chain. chain: $want; indexer: $(indexer_state "$name") cursor $cursor/$(head_block); log: $(tail -5 "$LOGS/indexer-$name.log")"
}
