import Lake
open Lake DSL

-- Separate package: the Aeneas backend needs Lean 4.36 and Mathlib; the main SIRM package stays on 4.33.1.
require aeneas from git
  "https://github.com/AeneasVerif/aeneas" @ "2e3d4488280bb8a95411db81019a7854a784861f" / "backends/lean"

package sirm_refinement

@[default_target] lean_lib SirmRefinement {}
