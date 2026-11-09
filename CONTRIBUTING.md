# Contributing

Contributions should improve the normative specification, its proofs, or a demonstrably conforming implementation.

## Before submitting

- read the project README, architecture, formalization status, and release gates;
- identify the exact protocol rule being changed;
- update Lean definitions and proof obligations before changing implementation behavior;
- include tests for boundary values, overflow/underflow, rounding, replay, and failure atomicity where relevant;
- update decisions and documentation when semantics or parameters change;
- do not claim that tests, fuzzing, or a Lean lemma prove properties outside their scope.

## Review expectations

Every protocol change needs independent review. Changes to genesis, issuance, burn, redemption, governance, consensus, or security-critical authorization require explicit rationale and review from more than one responsible maintainer before release.

## Licensing

By intentionally submitting a contribution for inclusion, contributors agree that the contribution is offered under Apache-2.0 unless a separate written agreement says otherwise. Do not submit code or text unless you have the right to contribute it.