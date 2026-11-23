#!/usr/bin/env bash
# Extracts rust/sirm-keys-core to Lean with Charon and Aeneas (needs a built Aeneas checkout).
set -euo pipefail
: "${AENEAS_DIR:?set AENEAS_DIR to a built Aeneas checkout}"
root="$(cd "$(dirname "$0")/.." && pwd)"
out="$root/refinement/generated"
mkdir -p "$out"
cd "$root/rust/sirm-keys-core"
"$AENEAS_DIR/charon/bin/charon" cargo --preset=aeneas --dest-file "$out/sirm_keys_core.llbc"
"$AENEAS_DIR/bin/aeneas" -backend lean "$out/sirm_keys_core.llbc" -dest "$out"
echo "Generated Lean files in $out"
