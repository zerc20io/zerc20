#!/usr/bin/env bash
set -euo pipefail

SKIP_PICUS=0
PICUS_TIMEOUT_MS="${PICUS_TIMEOUT_MS:-10000}"
PICUS_SOLVER="${PICUS_SOLVER:-native}"
PICUS_SELECTOR="${PICUS_SELECTOR:-counter}"
PICUS_LEMMAS="${PICUS_LEMMAS:-all}"
PICUS_FORMAT="${PICUS_FORMAT:-human}"
PICUS_SUMMARY_ONLY="${PICUS_SUMMARY_ONLY:-0}"
PICUS_REQUIRE_DECISIVE="${PICUS_REQUIRE_DECISIVE:-0}"
PICUS_EXPECT_RESULT="${PICUS_EXPECT_RESULT:-}"
PICUS_GB_STRATEGY="${PICUS_GB_STRATEGY:-}"
PICUS_POLY_REPR="${PICUS_POLY_REPR:-}"
PICUS_USE_F4="${PICUS_USE_F4:-0}"
PICUS_LINEAR_ELIM="${PICUS_LINEAR_ELIM:-0}"
PICUS_CIRCOM_O0="${PICUS_CIRCOM_O0:-1}"
CIRCOM_WASM="${CIRCOM_WASM:-auto}"

for arg in "$@"; do
  case "$arg" in
    --skip-picus)
      SKIP_PICUS=1
      ;;
    *)
      echo "unknown argument: $arg" >&2
      exit 2
      ;;
  esac
done

case "$PICUS_SUMMARY_ONLY" in
  0 | 1)
    ;;
  *)
    echo "PICUS_SUMMARY_ONLY must be either '0' or '1'" >&2
    exit 2
    ;;
esac

case "$PICUS_REQUIRE_DECISIVE" in
  0 | 1)
    ;;
  *)
    echo "PICUS_REQUIRE_DECISIVE must be either '0' or '1'" >&2
    exit 2
    ;;
esac

case "$CIRCOM_WASM" in
  auto | 0 | 1)
    ;;
  *)
    echo "CIRCOM_WASM must be 'auto', '0', or '1'" >&2
    exit 2
    ;;
esac

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ZKP_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
BUILD_DIR="${ZKP_BUILD_DIR:-$ZKP_DIR/build/circom}"

node "$SCRIPT_DIR/check_circuit_constants.mjs"

CIRCUITS=(
  "joinsplit"
  "rageexit"
)

if ! command -v circom >/dev/null 2>&1; then
  echo "circom is required but was not found in PATH" >&2
  exit 127
fi

if [[ "$SKIP_PICUS" -eq 0 ]] && ! command -v picus >/dev/null 2>&1; then
  cat >&2 <<'EOF'
picus is required but was not found in PATH.

Install the reviewed revision from zkp/picus-toolchain.json, then rerun:
  npm run install:picus

For a Circom-only check, run:
  npm run inspect:circom
EOF
  exit 127
fi

mkdir -p "$BUILD_DIR"

if [[ "$SKIP_PICUS" -eq 0 ]]; then
  picus_binary="$(command -v picus)"
  picus_bin_dir="$(cd "$(dirname "$picus_binary")" && pwd)"
  picus_install_root="$(cd "$picus_bin_dir/.." && pwd)"
  picus_provenance_file="${PICUS_PROVENANCE_FILE:-$picus_install_root/share/zerc20/picus-provenance.json}"
  picus_evidence_file="${PICUS_TOOLCHAIN_EVIDENCE_FILE:-$BUILD_DIR/picus-toolchain-evidence.json}"
  if [[ ! -f "$picus_provenance_file" ]]; then
    echo "Picus install provenance was not found: $picus_provenance_file" >&2
    echo "Reinstall the reviewed revision with: npm run install:picus" >&2
    exit 127
  fi
  node "$SCRIPT_DIR/picus_toolchain.mjs" verify-install \
    --binary "$picus_binary" \
    --evidence "$picus_evidence_file" \
    --provenance "$picus_provenance_file"
fi

for circuit in "${CIRCUITS[@]}"; do
  circuit_path="$ZKP_DIR/circom/main/$circuit.circom"
  circuit_label="$circuit"

  circuit_out="$BUILD_DIR/$circuit_label"
  r1cs_path="$circuit_out/$circuit.r1cs"

  if [[ ! -f "$circuit_path" ]]; then
    echo "circuit not found: $circuit_path" >&2
    exit 1
  fi

  echo "==> circom --inspect $circuit_label"
  rm -rf "$circuit_out"
  mkdir -p "$circuit_out"

  circom_args=(
    "$circuit_path"
    --inspect
    --r1cs
    --sym
  )

  emit_wasm="$CIRCOM_WASM"
  if [[ "$emit_wasm" == "auto" ]]; then
    emit_wasm=1
    if [[ "$SKIP_PICUS" -eq 0 ]]; then
      emit_wasm=0
    fi
  fi

  if [[ "$emit_wasm" == "1" ]]; then
    circom_args+=(--wasm)
  fi

  # Picus' benchmark guidance requires Circom --O0 so the analyzer sees the
  # raw production constraint structure. Keep the Circom-only inspect path
  # optimized for the artifact developers usually consume.
  if [[ "$PICUS_CIRCOM_O0" == "1" && "$SKIP_PICUS" -eq 0 ]]; then
    circom_args+=(--O0)
  fi

  circom_args+=(-o "$circuit_out")
  circom "${circom_args[@]}"

  if [[ "$SKIP_PICUS" -eq 0 ]]; then
    echo "==> picus info $circuit_label"
    picus info --r1cs "$r1cs_path"

    echo "==> picus check $circuit_label"
    picus_format="$PICUS_FORMAT"
    if [[ "$PICUS_SUMMARY_ONLY" == "1" ]]; then
      picus_format="json"
    fi

    picus_args=(
      check
      --r1cs "$r1cs_path"
      --timeout "$PICUS_TIMEOUT_MS"
      --solver "$PICUS_SOLVER"
      --selector "$PICUS_SELECTOR"
      --lemmas "$PICUS_LEMMAS"
      --format "$picus_format"
    )

    if [[ -n "$PICUS_GB_STRATEGY" ]]; then
      picus_args+=(--gb-strategy "$PICUS_GB_STRATEGY")
    fi
    if [[ -n "$PICUS_POLY_REPR" ]]; then
      picus_args+=(--poly-repr "$PICUS_POLY_REPR")
    fi
    if [[ "$PICUS_USE_F4" == "1" ]]; then
      picus_args+=(--use-f4)
    fi
    if [[ "$PICUS_LINEAR_ELIM" == "1" ]]; then
      picus_args+=(--linear-elim)
    fi

    if [[ "$PICUS_SUMMARY_ONLY" == "1" ]]; then
      picus_json="$(mktemp)"
      if ! picus "${picus_args[@]}" >"$picus_json"; then
        cat "$picus_json" >&2
        rm -f "$picus_json"
        exit 1
      fi
      picus_result="$(sed -n 's/^[[:space:]]*"result":[[:space:]]*"\([^"]*\)".*/\1/p' "$picus_json" | head -1)"
      if [[ -z "$picus_result" ]]; then
        echo "failed to parse Picus JSON result" >&2
        cat "$picus_json" >&2
        rm -f "$picus_json"
        exit 1
      fi
      rm -f "$picus_json"

      echo "picus result: $picus_result"
      if [[ "$picus_result" == "unsafe" ]]; then
        echo "picus reported the circuit is UNSAFE (under-constrained)" >&2
        echo "picus counterexample omitted; rerun with PICUS_SUMMARY_ONLY=0 for full witnesses" >&2
        exit 1
      fi
      if [[ "$PICUS_REQUIRE_DECISIVE" == "1" && "$picus_result" == "unknown" ]]; then
        echo "Picus result is unknown, but PICUS_REQUIRE_DECISIVE=1 was set" >&2
        exit 1
      fi
      if [[ -n "$PICUS_EXPECT_RESULT" && "$picus_result" != "$PICUS_EXPECT_RESULT" ]]; then
        echo "Picus result '$picus_result' did not match PICUS_EXPECT_RESULT='$PICUS_EXPECT_RESULT'" >&2
        exit 1
      fi
    else
      # Picus exits 0 even when it reports "unsafe", so inspect the output to
      # decide pass/fail rather than relying on the process exit code.
      picus_output="$(picus "${picus_args[@]}")"
      printf '%s\n' "$picus_output"
      if printf '%s' "$picus_output" | grep -qi 'unsafe'; then
        echo "picus reported the circuit is UNSAFE (under-constrained)" >&2
        exit 1
      fi
    fi
  fi
done

echo "all circuit checks completed"
