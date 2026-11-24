# Refinement of the Rust decision core against the Lean model

Status: **the refinement proofs are built and checked by SIRM** (`lake build` completes on the Mac and in the CI job
`Refinement / build and proofs` of every pull request, no `sorry`): `count_valid_spec`, `accepts_spec`,
`keys_distinct_spec`, `nonce_class_spec`, `next_nonce_spec`, `migrate_acc_spec`, `migrate_split_spec`, `add_ok_spec`,
`sub_ok_spec` and `succ_ok_spec` hold for the Aeneas translation of `rust/sirm-keys-core`, with axioms `propext`,
`Classical.choice`, `Quot.sound` (the package uses Mathlib). `refinement/check_proofs.sh` checks in CI that
`KeysCoreProofs.lean` holds no proof placeholder and that each of these ten theorems depends only on those three axioms.
Scope is this small core only. Everything else in the Rust code is still tied to the Lean model by differential
tests (see `docs/TESTING.md`).

Limits: (1) the Aeneas translation is trusted (Charon and Aeneas are not verified here); (2) the specifications are
stated in this package (`total`, `Distinct`, `kk`) in the shape of `SIRM/ThresholdAuth.lean` (`validIndices` length,
`KeysDistinct`), but the two packages are on different Lean versions, so the link between them is by identical
conditions, not by an imported theorem. The main package states the same conditions for the nonce ceiling
(`IntegratedPipeline.succOk`, `processCapped_accept_succ`, `processCapped_stale_iff`, `processCapped_future_iff`), the
supply ceiling (`BoundedAmounts.addOk`, `fitsB_issue_iff_addOk`, `boundVal_issue_overflow`) and the balance check
(`IntegratedLedger.subOk`, `pre_burn_iff_subOk`, `pre_transfer_iff_subOk`, `burn_bal_subOk`, `transfer_src_subOk`); the
migration conditions of `fitsB` and the balance conditions of escrow open and migrate are not stated this way;
(3) `sirm_codec` calls the proved core where it decides (see below); the code around the calls (building the list of
valid indices from the verifier, the permits function, the request cache, the nonce map and the ledger bookkeeping) is
still covered by differential tests only.

What is here:

- `rust/sirm-keys-core`: the decision core written with plain loops (no closures, iterators or collections), which
  Charon can extract: `keys_distinct`, `count_valid` and `accepts` (the threshold decision), the nonce decision
  (`nonce_class`, `next_nonce`, `succ_ok`), the migration arithmetic (`migrate_acc`, `migrate_split`) and the checked
  `u128` addition and subtraction (`add_ok`, `sub_ok`). It has unit tests, which run in the Rust CI job.
- Where `sirm_codec` calls it (`rust/sirm-codec/src`): `keys.rs` (`keys_distinct`, `accepts`), `ledger.rs` and `fees.rs`
  (checked sums and differences), `envelope.rs`, `machine.rs`, `receipt.rs` and `timelock.rs` (nonce successor and checked
  sums), `migration.rs` (`migrate_acc`, `migrate_split`, checked sums, nonce successor) and `integrated.rs` (the nonce
  decision `nonce_class`, the migration arithmetic, checked sums, and `sub_ok` for the four balance checks of the
  validation: transfer between different accounts, burn, escrow open and migrate).
- `refinement/run_extraction.sh`: runs Charon and Aeneas on that crate and writes the Lean translation to
  `refinement/generated/` (not committed).
- `refinement/lean`: the Lake package with the translation and the proofs (below); its `lake-manifest.json` is committed,
  so that CI builds the same dependency versions.
- `refinement/check_proofs.sh`: run from `refinement/lean` after `lake build`; fails on a proof placeholder and on any
  axiom other than `propext`, `Classical.choice`, `Quot.sound` for the ten theorems above.

Why this is separate from the main Lean package: the Aeneas Lean backend requires Lean 4.36 and Mathlib, the
SIRM proofs are on Lean 4.33.1 and the new SIRM files avoid Mathlib. The refinement is therefore a second Lake
package in `refinement/lean/` that is built on its own and has its own CI job (`Refinement / build and proofs`)
that runs `lake build` and `refinement/check_proofs.sh`.

## Steps on a machine with network access (Mac)

1. `git clone https://github.com/AeneasVerif/aeneas ~/aeneas && cd ~/aeneas && make setup-charon && make`
2. From the repository root: `AENEAS_DIR=~/aeneas ./refinement/run_extraction.sh`
3. Copy `refinement/generated/SirmKeysCore.lean` to `refinement/lean/SirmRefinement/SirmKeysCore.lean`, then run
   `lake build` in `refinement/lean` and `bash ../check_proofs.sh`. A new core function needs its translation copied this
   way, a specification in `SirmRefinement/KeysCoreProofs.lean` and its name in the list of `refinement/check_proofs.sh`,
   so that CI checks its axioms.

## The first targets (proved against `SIRM/ThresholdAuth.lean`)

With `keys` the list of `KeyRecord`s of a policy and `valid` the boolean list of verified indices:

1. `keys_distinct keys = ok true ↔ KeysDistinct` (every pair of indices with equal key values is the same index);
2. `count_valid valid = ok n` with `n = (List.filter id valid).length`, and no overflow for lengths below `2^64`;
3. `accepts valid k = ok true ↔ 0 < k ∧ k ≤ (List.filter id valid).length`, which is the decision of
   `thresholdAccepts`.

These are `keys_distinct_spec`, `count_valid_spec` and `accepts_spec`, and `sirm_codec::keys` calls this core, so that the
proved code is the code that runs. The later specifications (nonce, migration arithmetic, checked sums, differences and
successor) follow the same pattern.

Not claimed: the verifier, hashing, and anything outside the core. The machines (`integrated::Machine::process` and the
older `machine::Processor::process`) are not extracted: `integrated::Machine::process` takes its nonce decision, its
checked sums and differences, the migration arithmetic and the four balance checks of its validation from the core, but
the request cache, the nonce map and the ledger bookkeeping are outside the core (it is written without collections) and
are covered by differential tests only.

## The Lean package (`refinement/lean`)

`lake build` in `refinement/lean` (Lean 4.36 and Mathlib come with the Aeneas dependency; the first build
downloads Mathlib, so use `lake exe cache get` if it is offered). `SirmRefinement/SirmKeysCore.lean` is the
generated translation (regenerate it with `run_extraction.sh`, do not edit it); `SirmRefinement/KeysCoreProofs.lean`
holds the ten specifications listed above (built successfully, 3,617 jobs).
