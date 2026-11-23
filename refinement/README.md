# Refinement of the Rust key checks against the Lean model (setup, not yet proved)

Status: **the extraction pipeline is prepared; no refinement theorem exists yet.** Until one is proved and
merged, the Rust code is tied to the Lean model only by differential tests (see `docs/TESTING.md`).

What is here:

- `rust/sirm-keys-core`: the decision core of `keys_distinct` and `threshold_accepts` written with plain loops
  (no closures, iterators or collections), which Charon can extract. It has unit tests and is not wired into
  `sirm-codec` yet.
- `refinement/run_extraction.sh`: runs Charon and Aeneas on that crate and writes the Lean translation to
  `refinement/generated/` (not committed).

Why this is separate from the main Lean package: the Aeneas Lean backend requires Lean 4.36 and Mathlib, the
SIRM proofs are on Lean 4.33.1 and the new SIRM files avoid Mathlib. The refinement is therefore a second Lake
package in `refinement/lean/` that is built on its own and is not part of the 19 CI checks until it has been
shown to build there.

## Steps on a machine with network access (Mac)

1. `git clone https://github.com/AeneasVerif/aeneas ~/aeneas && cd ~/aeneas && make setup-charon && make`
2. From the repository root: `AENEAS_DIR=~/aeneas ./refinement/run_extraction.sh`
3. Create `refinement/lean/` as a Lake package that requires `Aeneas` (copy `lean-toolchain` from
   `~/aeneas/backends/lean`), import the generated file and prove the targets below.

## Targets (to be proved against `SIRM/ThresholdAuth.lean`)

With `keys` the list of `KeyRecord`s of a policy and `valid` the boolean list of verified indices:

1. `keys_distinct keys = ok true ↔ KeysDistinct` (every pair of indices with equal key values is the same index);
2. `count_valid valid = ok n` with `n = (List.filter id valid).length`, and no overflow for lengths below `2^64`;
3. `accepts valid k = ok true ↔ 0 < k ∧ k ≤ (List.filter id valid).length`, which is the decision of
   `thresholdAccepts`.

Then `sirm_codec::keys` is changed to call this core, so that the proved code is the code that runs.

Not claimed: the verifier, hashing, and anything outside this module. Moving the machine (`Machine::process`)
into the same pipeline is a later, larger step.

## The Lean package (`refinement/lean`)

`lake build` in `refinement/lean` (Lean 4.36 and Mathlib come with the Aeneas dependency; the first build
downloads Mathlib, so use `lake exe cache get` if it is offered). `SirmRefinement/SirmKeysCore.lean` is the
generated translation (regenerate it with `run_extraction.sh`, do not edit it); `SirmRefinement/KeysCoreProofs.lean`
holds `count_valid_spec`, `accepts_spec` and `keys_distinct_spec`. First draft, not yet compiled: the
theorems are claims until `lake build` succeeds.
