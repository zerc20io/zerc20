#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TOOLCHAIN="$SCRIPT_DIR/picus_toolchain.mjs"

for command in git cargo rustc node; do
  if ! command -v "$command" >/dev/null 2>&1; then
    echo "$command is required to install Picus" >&2
    exit 127
  fi
done

repository="$(node "$TOOLCHAIN" config-field repository)"
revision="$(node "$TOOLCHAIN" config-field revision)"
version="$(node "$TOOLCHAIN" config-field version)"
cargo_path="$(node "$TOOLCHAIN" config-field cargoPath)"

install_root="${PICUS_INSTALL_ROOT:-${CARGO_HOME:-$HOME/.cargo}}"
provenance_file="${PICUS_PROVENANCE_FILE:-$install_root/share/zerc20/picus-provenance.json}"
source_dir="${PICUS_SOURCE_DIR:-}"
remove_source=0

if [[ -z "$source_dir" ]]; then
  source_dir="$(mktemp -d "${TMPDIR:-/tmp}/zerc20-picus.XXXXXX")"
  remove_source=1
elif [[ -e "$source_dir" ]]; then
  echo "PICUS_SOURCE_DIR already exists; refusing to reuse an unverified checkout" >&2
  exit 1
else
  mkdir -p "$(dirname "$source_dir")"
  mkdir "$source_dir"
fi

cleanup() {
  if [[ "$remove_source" -eq 1 && -d "$source_dir" ]]; then
    rm -rf -- "$source_dir"
  fi
}
trap cleanup EXIT

git -C "$source_dir" init --quiet
git -C "$source_dir" remote add origin "$repository"
git -C "$source_dir" fetch --quiet --depth 1 origin "$revision"

fetched_revision="$(git -C "$source_dir" rev-parse 'FETCH_HEAD^{commit}')"
if [[ "$fetched_revision" != "$revision" ]]; then
  echo "Picus fetch returned unexpected revision: $fetched_revision" >&2
  exit 1
fi

git -C "$source_dir" checkout --quiet --detach "$revision"
checkout_revision="$(git -C "$source_dir" rev-parse 'HEAD^{commit}')"
checkout_remote="$(git -C "$source_dir" remote get-url origin)"
if [[ "$checkout_revision" != "$revision" ]]; then
  echo "Picus checkout revision mismatch: $checkout_revision" >&2
  exit 1
fi
if [[ "$checkout_remote" != "$repository" ]]; then
  echo "Picus checkout remote mismatch: $checkout_remote" >&2
  exit 1
fi
if [[ -n "$(git -C "$source_dir" status --porcelain)" ]]; then
  echo "Picus checkout is dirty before build" >&2
  exit 1
fi

echo "Installing reviewed Picus $version from $revision"
cargo install \
  --locked \
  --force \
  --root "$install_root" \
  --path "$source_dir/$cargo_path"

binary="$install_root/bin/picus"
if [[ ! -x "$binary" ]]; then
  echo "Picus installation did not produce $binary" >&2
  exit 1
fi

node "$TOOLCHAIN" write-provenance \
  --binary "$binary" \
  --output "$provenance_file" \
  --source-dir "$source_dir"

echo "Add $install_root/bin to PATH before running npm run check:circuits."
