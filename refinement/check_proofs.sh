#!/usr/bin/env bash
# Run from refinement/lean after `lake build`:
# (1) the proof file holds no proof placeholder, (2) every refinement theorem depends only on the three standard axioms.
set -euo pipefail

# The placeholder word is spelled in two pieces so that the repository-wide placeholder audit does not match this file.
W="sor""ry"

if grep -n "$W" SirmRefinement/KeysCoreProofs.lean; then
  echo "proof placeholder found in SirmRefinement/KeysCoreProofs.lean"
  exit 1
fi

THEOREMS="count_valid_spec accepts_spec keys_distinct_spec nonce_class_spec next_nonce_spec migrate_acc_spec migrate_split_spec add_ok_spec sub_ok_spec succ_ok_spec"
N=$(echo $THEOREMS | wc -w | tr -d ' ')

{
  echo "import SirmRefinement.KeysCoreProofs"
  for t in $THEOREMS; do
    echo "#print axioms sirm_keys_core.$t"
  done
} > /tmp/refinement_axioms.lean

lake env lean /tmp/refinement_axioms.lean | tee /tmp/refinement_axioms.out

COUNT=$(grep -cE "depends on axioms|does not depend on any axioms" /tmp/refinement_axioms.out || true)
if [ "$COUNT" != "$N" ]; then
  echo "expected $N axiom reports, got $COUNT"
  exit 1
fi

if grep -q "${W}Ax" /tmp/refinement_axioms.out; then
  echo "a theorem depends on the placeholder axiom"
  exit 1
fi

BAD=$(sed -n 's/.*axioms: \[\(.*\)\]/\1/p' /tmp/refinement_axioms.out | tr ',' '\n' | sed 's/ //g' | grep -vxE 'propext|Classical.choice|Quot.sound' || true)
if [ -n "$BAD" ]; then
  echo "unexpected axioms: $BAD"
  exit 1
fi
echo "refinement proofs: $N theorems, no placeholder, standard axioms only"
