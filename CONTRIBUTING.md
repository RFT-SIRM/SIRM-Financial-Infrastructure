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

The repository is under the Business Source License 1.1 (root `LICENSE`; versions published before the
change remain under Apache-2.0, see `LICENSES/Apache-2.0.txt`). See
[Licensing and Intellectual Property Policy](docs/LICENSING_AND_IP_POLICY.md).

**Outside contributions are not accepted yet.** Relicensing later (for example at the change date, or for a
commercial license) needs the consent of every contributor, so contributor terms (a CLA or an equivalent) must
be decided and documented before any outside code or text is merged. You are welcome to open issues and to
report review findings; please do not send pull requests until this section changes.

Do not submit code, text, data, or other material unless you have the right
to contribute it. Identify third-party material and its license when
relevant.

Any future CLA, copyright assignment, dual-licensing arrangement, or
change to contribution terms requires an explicit, separately documented
decision and legal review before it is introduced.
