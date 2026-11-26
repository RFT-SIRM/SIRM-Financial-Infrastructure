#!/usr/bin/env bash
# Axiom scan of the SIRM Lean package. Run from the repository root after `lake build`.
# Every theorem declared in a module under SIRM (equation lemmas that exist in the compiled modules included) must
# depend only on `propext`, `Quot.sound` and `Classical.choice`; no module may declare an axiom. A proof placeholder
# (`sorryAx`) shows up as an extra axiom of the theorem that uses it; `native_decide` declares an auxiliary axiom
# (`<theorem>._native.native_decide.ax_N`), reported as a declared axiom and as an extra axiom of its theorem.
# Definitions are not scanned themselves; a definition that uses a placeholder is caught through the theorems that
# depend on it, and by the static audit "No proof placeholders".
# For the package SIRM the script also enforces the claims of the documentation that the modules in NO_CHOICE depend
# only on `propext` and `Quot.sound`: a theorem of such a module that uses `Classical.choice` fails the scan.
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
lake env lean "$TMP/AxiomScan.lean" | tee "$TMP/scan.out"

if [ "$PFX" = "SIRM" ]; then
  NO_CHOICE="SIRM.IntegratedLedger SIRM.BoundedAmounts SIRM.DisputeResolution SIRM.RequestEncodingV2 SIRM.SignedEnvelopeV3 SIRM.StateCommitmentV6 SIRM.CacheDigestV6 SIRM.EscrowConfigDigestV6 SIRM.SparseTreeV0 SIRM.LedgerRootsV0 SIRM.StateRootV6 SIRM.SignedPipelineV3"
  for M in $NO_CHOICE; do
    if ! grep -qx "import $M" "$TMP/AxiomScan.lean"; then
      echo "claim check: module $M is not part of the scan"; exit 1
    fi
    if grep -qF "CHOICE_MODULE $M " "$TMP/scan.out"; then
      echo "documentation claim is false: theorems of $M depend on Classical.choice"; exit 1
    fi
  done
  echo "documented claims confirmed: no theorem of the modules in NO_CHOICE depends on Classical.choice"
fi
