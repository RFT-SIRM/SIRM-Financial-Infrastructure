# Guide for an independent reviewer (proposal)

This repository has had **no independent review**. No human other than the author has read the
code, the proofs or the specifications. Most of the text, Lean and Rust here was written with heavy AI
assistance and checked by the Lean kernel, the test suites and CI, not by a person who is expert in
cryptography or protocol design. A reviewer should assume nothing here is trustworthy until they have
read it. This page tells you where to start and what we most want to hear. It is not a request for
speed, an endorsement or a service agreement: any reading, even of one file, is welcome.

## What is in scope

1. **Lean semantics** (`SIRM/`, start with `IntegratedPipeline.lean`, then `IntegratedLedger.lean`):
   does the model say what the prose says, and are the theorem statements the ones that matter?
2. **Request and signature wire formats** (`engineering/canonical_encoding/SPEC_request_v1.md`,
   `SPEC_signed_request_v2.md`) and `rust/sirm-codec/src/`: encoding, domain separation, verification
   order, the downgrade defence.
3. **State commitment v5** (`SPEC_state_commitment_v5.md`): what is committed, and what is not.
4. **Accounting claims** (`docs/ACCOUNTING_MODEL.md`) against the Lean model.

Out of scope for now: deployment, custody, reserves, settlement, legal status, the network layer.

## Questions we most want answered

- Is the encoding injective, and does the decoder accept **only** canonical inputs (no padding, no
  trailing bytes, no overlong values)? The specs claim this; the evidence is Lean round trips for a
  bounded record plus frozen vectors and mutation tests, not a proof for the Rust decoder.
- Are the domain tags (`SIRM/SIG/v2\0`, `SIRM/SRQ/v2\0`, and the v0 and v1 tags) sufficient to prevent
  cross-protocol and cross-version replay? Is chain id binding complete?
- Does the Ed25519 verification (`verify_strict`) and the rule that post-quantum suites are **refused**
  rather than accepted leave any downgrade or confusion path?
- Nonces and the request-id cache: can a denied, replayed or conflicting request change state?
  Which of these properties are proved in Lean and which only fuzzed?
- State commitment v5: second-preimage or ambiguity between leaves, empty subtrees and configuration;
  is anything relevant missing from the root?
- The `u128` ceiling (`SIRM/BoundedAmounts.lean`) and the Rust checks: does the Lean predicate match what
  the code enforces on every path? The evidence is a differential test, not a refinement proof.
- The arbiter layer (`SIRM/DisputeResolution.lean`) is separate from the pipeline and the wire formats.
  Is the model of a resolution the right one to extend?

## What counts as evidence here

| Kind | Meaning |
|---|---|
| Lean theorem | Holds for the model as written; says nothing about the Rust or Python code. |
| Differential test | Rust and Python agree on the stated runs; not a proof of refinement. |
| Static audit | A script checks repository structure and claims; it does not check semantics. |

`docs/STATUS_AT_A_GLANCE.md` lists what is proved, tested and open.

## Run it

```
lake build                                  # Lean proofs
cd rust/sirm-codec && cargo test --locked   # Rust tests
python3 scripts/ci_audit.py all             # static audits
```

## How to report

Use the private route in [SECURITY.md](../SECURITY.md) for anything that looks like a vulnerability and
a normal GitHub issue for everything else. Say what you read and what you did not; a partial review with
a clear scope is more useful than a complete-looking one. A negative result ("this is fine, here is why")
is as valuable as a finding.
