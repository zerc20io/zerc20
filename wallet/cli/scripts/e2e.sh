#!/usr/bin/env bash
# E2E: the built `zerc20` run as a user runs it, one process a command (test/e2e/), against the whole local stack
# scripts/dev-stack.sh starts. Needs both SDKs built (npm run build in storage/sdk and wallet/sdk), as the CLI takes
# them from their dist. SPEED=fast skips the Nova root proofs, and runs a merge prover that proves nothing, which the
# CLI reaches as a prover on this machine. Arguments go to vitest. forge and PocketIC do not run inside the Claude Code
# sandbox.
source "$(dirname "$0")/../../../scripts/dev-stack.sh"
export NETWORK
(cd wallet/cli && npm run build && npx vitest run --config vitest.e2e.config.ts "$@") || fail "cli e2e; logs in $LOGS"
echo "ALL CLI E2E CHECKS PASSED"
