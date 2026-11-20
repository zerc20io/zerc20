#!/usr/bin/env bash
# E2E: the wallet SDK against the whole local stack scripts/dev-stack.sh starts (anvil with the real verifiers,
# every node, storage in PocketIC). test/e2e/*.test.ts play the users, each on accounts of its own, side by side.
# SPEED=fast skips the Nova root and merge proofs (see scripts/dev-stack.sh) and adds test/e2e/emergency.test.ts, which
# forges a root. Its merge prover checks each merge and proves none, so test/e2e/merge.test.ts and pos.test.ts merge
# too. MERGE=1 proves the merges: run merge pos alone with it when the merge circuit changes,
# MERGE=1 SPEED=fast scripts/e2e.sh merge pos. Arguments go to vitest (file names, -t).
# With SPEED=fast, about four minutes in all, MERGE=1 or not; merge pos alone, about two.
# KEEP=1 leaves the stack running afterwards; so does scripts/dev-stack.sh, and against either, from wallet/sdk:
#   NETWORK=../../target/dev-stack/network.json SPEED=fast npx vitest run --config vitest.e2e.config.ts usdc
# forge and PocketIC do not run inside the Claude Code sandbox.
source "$(dirname "$0")/../../../scripts/dev-stack.sh"
export NETWORK
# emergency.test.ts halts the roots every other file waits on: it runs alone, after the rest
e2e() { (cd wallet/sdk && npx vitest run --config vitest.e2e.config.ts --passWithNoTests "$@") || fail "wallet e2e; logs in $LOGS"; }
e2e --exclude '**/emergency.test.ts' "$@"
if [ $# = 0 ] || [[ " $* " = *" emergency "* ]]; then e2e emergency; fi
[ "${KEEP:-0}" = 1 ] && {
  echo "running; Ctrl-C to stop"
  wait
}
echo "ALL WALLET E2E CHECKS PASSED"
