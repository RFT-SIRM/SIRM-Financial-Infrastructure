# Refinement of the Rust key checks against the Lean model

Status: **the first refinement proofs are built and checked by SIRM** (`lake build` completes on the Mac, no `sorry`):
`count_valid_spec`, `accepts_spec` and `keys_distinct_spec` hold for the Aeneas translation of
`rust/sirm-keys-core`, with axioms `propext`, `Classical.choice`, `Quot.sound` (the package uses Mathlib).
Scope is this small core only. Everything else in the Rust code is still tied to the Lean model by differential
tests (see `docs/TESTING.md`).

Limits: (1) the Aeneas translation is trusted (Charon and Aeneas are not verified here); (2) the specifications are
stated in this package (`total`, `Distinct`, `kk`) in the shape of `SIRM/ThresholdAuth.lean` (`validIndices` length,
`KeysDistinct`), but the two packages are on different Lean versions, so the link between them is by reading, not by a
theorem; (3) `sirm_codec::keys::{keys_distinct, threshold_accepts}` now call the proved core, which decides the result; the code around it (building the list of valid indices from the verifier, the permits function) is still covered by the 1,500 differential threshold cases only.

What is here:

- `rust/sirm-keys-core`: the decision core of `keys_distinct`, `threshold_accepts` and (not yet proved) `nonce_class` written with plain loops
  (no closures, iterators or collections), which Charon can extract. It has unit tests and is called by
  `sirm_codec::keys`.
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
holds `count_valid_spec`, `accepts_spec` and `keys_distinct_spec` (built successfully, 3,617 jobs).
