#!/usr/bin/env bash
# Self-test of the axiom scanner (scripts/axiom_scan_body.lean). Run from anywhere inside the repository.
# Five small modules are compiled outside the package and scanned with the real scanner body:
#   Clean        a theorem with no axiom             -> scan passes
#   Choice       a theorem using Classical.choice    -> counted, scan passes
#   Placeholder  a proof placeholder                 -> reported, scan fails
#   Axiom        a declared axiom and a theorem on it -> reported, scan fails
#   Native       native_decide                       -> reported, scan fails
# Exit code 0: the scanner behaves as stated. Non-zero: it does not, with the scanner output.
set -euo pipefail
cd "$(dirname "$0")/.."

# the placeholder word is spelled in two pieces so that the repository-wide placeholder audit never matches this file
P="sor""ry"
W="$(mktemp -d)"
mkdir -p "$W/AxTest"
printf '%s\n' 'theorem t_clean : 1 + 1 = 2 := rfl' > "$W/AxTest/Clean.lean"
printf '%s\n' 'theorem t_choice (p : Prop) : p ∨ ¬p := Classical.em p' > "$W/AxTest/Choice.lean"
printf '%s\n' "theorem t_placeholder : 1 = 2 := by $P" > "$W/AxTest/Placeholder.lean"
printf '%s\n' 'axiom ax_false : False' 'theorem t_uses_axiom : False := ax_false' > "$W/AxTest/Axiom.lean"
printf '%s\n' 'theorem t_native : 10 * 10 = 100 := by native_decide' > "$W/AxTest/Native.lean"

LEAN="$(lake env which lean)"
export LEAN_PATH="$(lake env printenv LEAN_PATH):$W"

for m in Clean Choice Placeholder Axiom Native; do
  if ! "$LEAN" --root="$W" -o "$W/AxTest/$m.olean" "$W/AxTest/$m.lean" > "$W/compile_$m.out" 2>&1; then
    echo "SELFTEST BROKEN: test module $m does not compile:"; cat "$W/compile_$m.out"; exit 1
  fi
done

OUT=""
RC=0
scan() {   # scan <case name> <module>...
  local name="$1"; shift
  {
    echo "import Lean"
    for m in "$@"; do echo "import AxTest.$m"; done
    cat scripts/axiom_scan_body.lean
    echo "#scan_axioms AxTest"
  } > "$W/Scan_$name.lean"
  RC=0
  OUT="$("$LEAN" "$W/Scan_$name.lean" 2>&1)" || RC=$?
}
fail() {
  echo "SELFTEST FAILED: $1"
  echo "--- scanner output (exit code $RC):"
  echo "$OUT"
  exit 1
}

scan ok Clean Choice
[ "$RC" = "0" ] || fail "the scan of a clean module and a Classical.choice module must pass"
echo "$OUT" | grep -q "problems=0" || fail "expected problems=0"
echo "$OUT" | grep -q "using_Classical.choice=1" || fail "expected exactly one theorem using Classical.choice"
echo "$OUT" | grep -qF "CHOICE_MODULE AxTest.Choice 1" || fail "expected the Classical.choice module line"

scan placeholder Clean Placeholder
[ "$RC" != "0" ] || fail "a proof placeholder must make the scan fail"
echo "$OUT" | grep -q "t_placeholder" || fail "the placeholder theorem must be named"
echo "$OUT" | grep -q "${P}Ax" || fail "the placeholder axiom must be named"

scan axiom Clean Axiom
[ "$RC" != "0" ] || fail "a declared axiom must make the scan fail"
echo "$OUT" | grep -qF "axiom declared: ax_false" || fail "the declared axiom must be named"
echo "$OUT" | grep -q "t_uses_axiom" || fail "the theorem that depends on the declared axiom must be named"

scan native Clean Native
[ "$RC" != "0" ] || fail "native_decide must make the scan fail"
echo "$OUT" | grep -q "t_native" || fail "the native_decide theorem must be named"
echo "$OUT" | grep -q "native_decide.ax" || fail "the auxiliary axiom declared by native_decide must be named"

echo "axiom scanner self-test: ok (clean passes; Classical.choice is counted; placeholder, declared axiom and native_decide are reported and fail the scan)"
