#!/usr/bin/env bash
# E2E: the plugin as a Kohaku wallet drives it (test/e2e/), against the whole local stack scripts/dev-stack.sh starts.
# Needs both SDKs built (npm run build in storage/sdk and wallet/sdk), as the plugin takes the wallet SDK from its dist.
# SPEED=fast skips the Nova root proofs. Arguments go to vitest. forge and PocketIC do not run inside the Claude Code
# sandbox.
source "$(dirname "$0")/../../../scripts/dev-stack.sh"
export NETWORK
(cd wallet/kohaku && npx vitest run --config vitest.e2e.config.ts "$@") || fail "kohaku plugin e2e; logs in $LOGS"
echo "ALL KOHAKU PLUGIN E2E CHECKS PASSED"
