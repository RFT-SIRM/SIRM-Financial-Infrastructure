# Testing and Verification

## Pinned Lean build

The CI workflow pins Lean 4.33.1 and Mathlib v4.33.1 and explicitly runs:

- `lake build` for the normative `SIRM` target;
- `lake test` for the `SIRMTests` theorem-level regression library.

## What the theorem-level regression suite checks

`SIRMTests.lean` instantiates the formal model with three accounts and two assets. It checks:

- initial per-asset holdings/supply reconciliation;
- a funded transfer and its exact resulting balances;
- rejection of an over-funded transfer request by the guarded command API (no next state is produced);
- successful guarded transfer and preservation of reconciliation;
- successful guarded holder burn and rejection of a burn exceeding the holder's balance;
- self-transfer behavior;
- non-interference with another asset;
- issuance and corresponding outstanding-supply increase;
- a holder-bounded burn and corresponding supply decrease;
- exact founder-allocation arithmetic;
- a concrete use of the balanced journal conservation theorem.

Because the test driver is a Lean library, `lake test` succeeds only if these statements and proof terms compile. The tests are theorem-level regression checks, not a runtime node test or a randomized fuzz campaign.

## Lint and runtime tests

Linting is explicitly disabled in CI until a linter driver is added. Runtime/property/fuzz tests for an executable reference implementation are not yet present. These are separate requirements and must not be described as passed.

## Reproducibility

A green run must be tied to the exact commit SHA and pinned toolchain. An absent test driver, skipped test command, or empty build is not accepted as a passing test result.
