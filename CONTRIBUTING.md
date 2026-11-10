# Contributing

Contributions should improve the normative specification, its proofs, or a
demonstrably conforming implementation.

## Before submitting

- read the project README, architecture, formalization status, and release
  gates;
- identify the exact protocol rule being changed;
- update Lean definitions and proof obligations before changing
  implementation behavior;
- include tests for boundary values, overflow/underflow, rounding, replay,
  and failure atomicity where relevant;
- update decisions and documentation when semantics or parameters change;
- do not claim that tests, fuzzing, or a Lean lemma prove properties
  outside their scope.

## Review expectations

Every protocol change needs independent review. Changes to genesis,
issuance, burn, redemption, governance, consensus, or security-critical
authorization require explicit rationale and review from more than one
responsible maintainer before release.

## License and contribution terms

The repository's default license is Apache License 2.0. The full license
text is in the root `LICENSE` file. See
[Licensing and Intellectual Property Policy](docs/LICENSING_AND_IP_POLICY.md)
for the distinction between the formal specification, future commercial
components, project identifiers, and contributor rights.

Under Section 5 of Apache-2.0, contributions intentionally submitted for
inclusion are licensed under Apache-2.0 unless the contributor explicitly
states otherwise or a separate written agreement applies.

Submitting a contribution does not by itself assign copyright ownership
to the repository maintainer. Contributors must have the right to submit
their work and must preserve applicable third-party notices and obligations.

Do not submit code, text, data, or other material unless you have the right
to contribute it. Identify third-party material and its license when
relevant.

Any future CLA, copyright assignment, dual-licensing arrangement, or
change to contribution terms requires an explicit, separately documented
decision and legal review before it is introduced.
