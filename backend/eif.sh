#!/usr/bin/env bash
# Builds an enclave's EIF from this checkout and prints its PCR0, the same on any machine with Docker and jq:
#   backend/eif.sh attester <out.eif>
#   backend/eif.sh merge-prover <out.eif> <the merge setup's setup.json>
# So anyone can check that a published PCR0 is this source's, and no one has to trust the machine that built the EIF
# an instance runs. PCR0 measures the kernel and init nitro-cli packs in, and the image's files with their times:
# nitro-cli runs from a pinned image (backend/nitro-cli.Dockerfile), and each enclave's Dockerfile pins the rest.
set -euo pipefail
root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)
usage="usage: backend/eif.sh attester|merge-prover <out.eif> [<setup.json>]"
name=${1:?$usage}
out=${2:?$usage}
case $name in
  attester) set -- ;;
  merge-prover)
    setup=${3:?$usage}
    pk=$(jq -er '.files["merge_decider_pk.bin"].sha256' "$setup")
    vk=$(jq -er '.files["merge_decider_vk.bin"].sha256' "$setup")
    set -- --build-arg MERGE_PK_SHA256="$pk" --build-arg MERGE_VK_SHA256="$vk"
    ;;
  *)
    echo "$usage" >&2
    exit 1
    ;;
esac
# The instances are arm64, and an EIF runs on the architecture it is built for: another machine emulates it.
platform=linux/arm64
# a name of this run's own: nitro-cli reads the image by name, and another run's build would take a shared one
image=zerc20-$name-enclave-$$
trap 'docker rmi "$image" >/dev/null 2>&1 || true' EXIT
docker build --platform $platform -f "$root/backend/$name/Dockerfile" -t "$image" "$@" "$root" >&2
docker build --platform $platform -q -t zerc20-nitro-cli - <"$root/backend/nitro-cli.Dockerfile" >/dev/null
# nitro-cli reads the image from the Docker daemon, so it takes the daemon's socket
docker run --rm --platform $platform -v /var/run/docker.sock:/var/run/docker.sock \
  -v "$(cd "$(dirname "$out")" && pwd -P):/out" zerc20-nitro-cli \
  nitro-cli build-enclave --docker-uri "$image" --output-file "/out/$(basename "$out")" |
  jq -er .Measurements.PCR0
