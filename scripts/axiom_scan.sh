#!/usr/bin/env bash
# Axiom scan of the SIRM Lean package. Run from the repository root after `lake build`.
# Every theorem (generated equation lemmas included) declared in a module under SIRM must depend only on
# `propext`, `Quot.sound` and `Classical.choice`; no module may declare an axiom (a `native_decide` adds one).
# Exit code 0: nothing found. Non-zero: a problem, listed in the output.
set -euo pipefail
PFX="${1:-SIRM}"
TMP="$(mktemp -d)"
{
  echo "import Lean"
  find SIRM -name '*.lean' | sort | sed 's|\.lean$||; s|/|.|g; s|^|import |'
  cat scripts/axiom_scan_body.lean
  echo "#scan_axioms $PFX"
} > "$TMP/AxiomScan.lean"
lake env lean "$TMP/AxiomScan.lean"
