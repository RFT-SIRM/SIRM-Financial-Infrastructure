# Post-Quantum Security Architecture (PROPOSAL)

Status: **proposal, not adopted.** Nothing here changes Lean, Rust, or any adopted decision.
Companion: `docs/PQ_DECISIONS_PROPOSED.md`. Written against `main` at `faf2433` (2026-11-15).
No claim is made of quantum-proof or unhackable security. Every guarantee below is conditional
on the assumptions in section 12, and the whole design needs independent cryptographic review
before any implementation phase starts.

## 1. Summary

1. **Isolate cryptography behind one boundary.** Financial transitions (ledger, supply, fees,
   escrow, disputes, migration) only ever see "principal P is authenticated". They never see an
   algorithm. Replacing an algorithm then touches the authentication layer, not accounting.
2. **Signatures:** ML-DSA-65 (FIPS 204) as the default; SLH-DSA (FIPS 205) for rare,
   long-lived, high-value trust roles; hybrid (classical AND post-quantum) only as a bounded
   transition tool, not a permanent design.
3. **Key establishment (transport, backups):** ML-KEM-768 (FIPS 203) combined with X25519.
4. **Hashing:** SHA-256 stays for commitments, with a hash-suite identifier so it can change.
5. **Agility without confusion:** a versioned suite registry, committed in state; the suite id
   is inside every signed byte string; a (domain tag, version) pair is never reinterpreted.
6. **No single key** controls treasury, issuance, upgrades or recovery. Threshold approval is an
   explicit k-of-n list of independent signatures. Post-quantum signatures do not aggregate in
   any standardized way, and this design does not assume that they do.
7. **Do not migrate what is not deployed.** No RFT Network exists, and the Ed25519 signed
   request (`SPEC_signed_request_v0.md`) is a proposal only. The cheapest and safest migration
   is to not launch with Ed25519 as the sole authorization path.

## 2. Standards check (primary sources, 2026-11-15)

| Document | Status found | Note |
|---|---|---|
| FIPS 203 ML-KEM | Final, 2024-08-13 | Sets ML-KEM-512/768/1024. NIST page notes (2025-11-17) an issue "to be corrected in a future update". Track it. |
| FIPS 204 ML-DSA | Final, 2024-08-13 | NIST page notes (2026-07-31) minor errata for a future revision. Track it. |
| FIPS 205 SLH-DSA | Final, 2024-08-13 | No errata listed. SP 800-230 (draft) is related. |
| SP 800-227 KEM recommendations | Final, 2025-09-18 | Read the PDF for exact hybrid and KEM usage rules before writing the transport spec. |
| NIST IR 8547 | **Final, October 2026** | Quantum-vulnerable signatures (RSA, ECDSA, EdDSA) and key establishment (finite-field and elliptic-curve DH): deprecated after 2030, disallowed after 2035. Hybrids are described as temporary. Symmetric and hash standards are not expected to need replacement; SHA-256 is listed with 128-bit classical collision strength. |
| NIST CSWP 39 | Final 2025-12-19, update 1 as of 2026-06-29 | Cryptographic agility guidance. |
| FIPS 206 FN-DSA (Falcon) | **Not verified** | The NIST page could not be fetched. Treated as not available. |
| HQC | Selected by NIST as a backup KEM (March 2025) | Not a standard yet to our knowledge; diversity option only. |

Interpretation: the 2030/2035 dates apply to NIST-approved use; they are a floor for planning,
not a statement about when a quantum computer will exist. This repository has no deployed
classical keys, so it can start PQ-first.

## 3. Threat model

Quantum-specific:

- **Q1 Shor:** forges Ed25519/ECDSA/RSA signatures and recovers private keys from public keys.
  Any key whose public half has ever been published is exposed.
- **Q2 Harvest now, decrypt later:** recorded transport traffic and encrypted backups are
  decrypted later. This affects confidentiality only. Ledger data is public, so the exposure
  is metadata, RPC traffic, backups, and any future confidential data.
- **Q3 Grover:** halves symmetric strength; AES-256 and SHA-256 retain adequate margin.
- **Q4 Retroactive forgery of history:** a future attacker re-signs old finalized records with
  forged classical keys. Defended by hash-chained commitments and PQ-signed checkpoints.

Ordinary (not quantum-specific) and equally important:

- **O1 Algorithm downgrade and substitution:** attacker presents a weaker suite or reuses a
  signature under another suite.
- **O2 Replay, cross-chain replay, malleability, key substitution.**
- **O3 Insider, compromised administrator, validator collusion, governance capture.**
- **O4 Supply chain:** dependencies, build pipeline, release signing keys. This is the most
  likely real-world path to loss.
- **O5 Key theft, loss, recovery abuse, denial of service.**
- **O6 Implementation flaws:** side channels, non-canonical encodings, verification bugs.
  Post-quantum implementations are young; this risk is larger than for Ed25519.

## 4. Candidate algorithms (sizes from FIPS tables)

| Scheme | NIST category | Public key | Signature / ciphertext | Role |
|---|---|---|---|---|
| Ed25519 (reference) | none (quantum-broken) | 32 B | 64 B | Transition second factor only |
| ML-DSA-44 | 2 | 1,312 B | 2,420 B | Not chosen: lowest margin |
| **ML-DSA-65** | 3 | 1,952 B | 3,309 B | **Default user and operational signatures** |
| ML-DSA-87 | 5 | 2,592 B | 4,627 B | Option for treasury/governance roles |
| SLH-DSA-128s | 1 | 32 B | 7,856 B | **Root, recovery, checkpoint, release** signatures (slow signing is acceptable) |
| SLH-DSA-128f | 1 | 32 B | 17,088 B | Not chosen: larger, only faster to sign |
| ML-KEM-768 | 3 | 1,184 B (encaps key) | 1,088 B (ciphertext) | **Default key establishment** |
| ML-KEM-1024 | 5 | 1,568 B | 1,568 B | Option for long-term confidential data |

Why ML-DSA-65: NIST standard, lattice-based (efficient), Category 3 gives margin over 44.
Why also SLH-DSA: it relies only on hash-function security, so a break of lattice assumptions
does not break it. Mixing two unrelated hardness assumptions on the highest-value keys is the
main diversity measure. Cost: SLH-DSA signatures are large and rare use only.

Size impact (computed): a signed request grows from 169 B (Ed25519 v0) to about 3.4 KB with
ML-DSA-65 (the 85-byte request, 8-byte chain id, 12-byte domain, a 2-byte suite id and a
3,309-byte signature), about 20 times larger. Verification speed, memory and throughput are
**not measured** and are an open task (section 9).

## 5. Cryptographic suite registry and agility

A suite registry is part of committed state, changed only by governed upgrade.

    entry = { suite_id u16, kind (sign | kem | hash | aead), algorithm, parameter set,
              public key length, signature length, status, activation height,
              deprecation height, disable height }
    status: proposed -> active -> deprecated (verify only) -> disabled (reject)

Rules:

1. The suite id is inside every signed byte string and in the wire format. The signing domain
   tag carries the layer version (`SIRM/SIG/v1\0`, not reused for another algorithm).
2. A (domain tag, wire version, suite id) triple has exactly one meaning forever. A change of
   algorithm is a new suite id; a change of layout is a new version.
3. Verifiers accept only suites that are `active` (or `deprecated` where policy allows) for
   the key's registered suite. The suite comes from the **registered key**, never from the
   message. A message claiming another suite is rejected, which closes downgrade by
   substitution.
4. Unknown, disabled, malformed or wrong-length keys and signatures are rejected before any
   state access.
5. Negotiation exists only for transport; ledger authorization is not negotiated.
6. Emergency migration: a governed upgrade can move a suite to `deprecated` or `disabled`
   with a timelock; the accounts' recovery credentials (section 6) cover keys left stranded.

The chain id, protocol version, suite id and key id are all part of the signed transcript.

## 6. Key management and governance

Roles and keys (each role has its own keys; no key serves two roles):

| Role | Signature | Control |
|---|---|---|
| User / operational principal | ML-DSA-65 (+ optional hybrid) | Account policy |
| Treasury, issuance, burn | ML-DSA-87 or 65, threshold | k-of-n, timelock, per-operation limits (existing grants) |
| Governance and upgrades | SLH-DSA-128s + ML-DSA-65, threshold | Versioned proposal, timelock, public notice |
| Recovery | SLH-DSA-128s, pre-registered | Threshold plus delay, cancellable by the live key |
| Validators (future) | ML-DSA-65, individual signatures | Set by governance; no aggregation assumed |
| Release signing | SLH-DSA-128s + ML-DSA-65, threshold of maintainers | Reproducible build, public manifest |

Lifecycle:

- **Generation:** on the owner's device or an HSM that supports the chosen algorithm, from a
  vetted OS entropy source; the registry records a proof of possession (a signature by the new
  key over its own registration).
- **Registration and binding:** a key is bound to a principal by a transaction signed by an
  existing authority for that principal and by the new key. Both signatures cover chain id,
  suite id, key id and validity window.
- **Rotation:** new key registered, old key moves to `retired` after a notice period; no
  single key can both rotate and spend inside one transaction without the policy allowing it.
- **Revocation and compromise response:** a revocation is accepted from the recovery
  credential or a threshold; a `frozen` account state blocks outgoing authorization while
  allowing deposits and recovery.
- **Threshold authorization:** a policy object lists n keys (with suites) and a threshold k; an
  authorization carries k distinct signatures over the same transcript. Verification cost and
  size grow linearly. Aggregation or threshold-signature schemes are not assumed; they would
  be a separate, reviewed addition.
- **Recovery:** a recovery key is registered in advance, uses a different algorithm family
  from the day-to-day key, and acts only after a delay during which the current key can
  cancel. Recovery cannot move funds directly; it can only re-register keys.
- **No unilateral control:** founder, administrator or single gate keys have no path to mint,
  confiscate, rewrite history or silently change the protocol (`SECURITY_MODEL.md` key rule).
  This is a design constraint on the registry, not a claim about operations.

## 7. Migration from Ed25519 and history integrity

Facts: the repository has no deployed Ed25519 identities. The signed-request proposal is
v0 and not adopted. Older identities exist only in the Rift prototype (`MIGRATION_FROM_RIFT.md`).

Plan:

1. **Genesis is PQ-first:** every principal with authority is registered with an ML-DSA key
   (and a recovery key). Ed25519 is optional, only as the second signature of a hybrid
   account, never alone.
2. **Hybrid rule (transition):** a hybrid account requires both signatures. A break of either
   algorithm alone does not authorize anything.
3. **Legacy keys cannot overwrite PQ keys:** once a PQ key is registered for a principal,
   classical keys lose the right to register, rotate or revoke keys for it. The Ed25519 key can
   at most co-sign ordinary operations.
4. **The race problem:** an attacker holding a broken legacy key could register their own PQ
   key first for an account that has not migrated. Defence: publish a **hash commitment to the
   successor PQ key** while the legacy key is still unbroken; the registry then accepts only a
   key matching the commitment. Accounts that never pre-commit stay exposed until a recovery
   credential or off-chain process resolves them. This is an inherent limit and is listed
   in section 12.
5. **Imports from Rift:** a one-time, governed claim signed by the legacy key together with a
   pre-registered commitment to a PQ key, with a challenge period and caps.
6. **Historical integrity:** finalized state roots are linked in a hash chain; periodic
   checkpoints are signed by the governance threshold with SLH-DSA and ML-DSA together.
   Verification of old records relies on hash security and the checkpoint signatures, not on
   old classical signatures, which are treated as untrusted after their suite is disabled.
7. **Deprecation:** `deprecated` suites verify old records but cannot authorize new ones;
   `disabled` suites are rejected everywhere except in archival verification mode.

## 8. State commitments and hash agility

Current proposal (`SPEC_state_commitment_v0.md`): SHA-256 sparse Merkle tree over balances,
supply and nonces. **This is a partial root, not a commitment to the full protocol state.**

| State element | In v0 root? | Needed for consensus | Plan |
|---|---|---|---|
| Balances, supply, nonces | yes | yes | keep |
| Transaction receipts, request-id cache | no | yes (idempotency) | add (or commit per block) |
| Account and asset registries | no | yes | add |
| Authorization grants, account control | no | yes | add |
| Key registry (registrations, rotations, revocations, commitments) | no (new) | yes | add |
| Suite registry, protocol version, chain id | no (new) | yes | add |
| Fee parameters, governance state, timelocks | no | yes | add |
| Escrow, time-lock, dispute, migration, residuals | no | yes | add |

Hash policy: SHA-256 is kept for commitments; NIST expects no transition for it, with 128-bit
classical collision strength (Category 2). Every tree root and leaf domain carries a hash
suite id. A move to SHA-384, SHA3-256 or another hash is a new suite id with a dual-root
transition epoch (both roots computed and committed), not an in-place change. Domain tags
stay versioned and unique per structure.

## 9. Rust implementation boundary

- One `crypto` boundary crate exposes `verify(suite, key, message, signature) -> bool`-style
  traits and error kinds; the processor never imports an algorithm.
- Use standardized algorithms only; no custom primitives. **Audit status is the main risk:** a
  July 2025 survey (Project Eleven) found no professionally audited post-quantum Rust crate;
  pure-Rust RustCrypto crates (ML-KEM, ML-DSA, SLH-DSA) were unaudited, libcrux was formally
  verified but lacked SLH-DSA, and C-FFI options (aws-lc-rs, liboqs) carried their own caveats.
  That survey is over a year old. **Re-check the current state before choosing**, and treat
  the choice as pending.
- Required tests: NIST ACVP and known-answer vectors, cross-implementation differential tests
  (the Python reference uses a different implementation), malformed and non-canonical input
  rejection, downgrade and suite-substitution tests, property and fuzz tests, and constant-time
  checks (for example with a timing-analysis tool) where the library claims them.
- Supply chain: pinned `Cargo.lock`, `cargo audit`/`cargo deny`, vendoring for release
  builds, reproducible builds, signed SBOM, dual-signed release manifests.
- Pin the exact FIPS text version and errata state each implementation follows, because FIPS
  203 and 204 have announced pending corrections.
- Benchmarks (open): key and signature sizes (above), verification time per core, memory,
  network overhead, and processor throughput with and without signature verification.

## 10. Lean formalization plan

Lean models cryptography as a **hypothesis**, not a proof of hardness.

Provable in Lean (planned, in separate modules, no change to existing invariants):

- algorithm-tagged keys and signatures as data; a suite registry with statuses;
- a total, deterministic verification function with explicit reject reasons;
- downgrade rejection: a verification accepted under policy P never uses a suite P forbids;
- key registry transitions (register, rotate, revoke, recover, freeze) as a state machine, with
  proofs that they never change balances, supply, GL or nonces (frame lemmas);
- threshold authorization: acceptance implies at least k distinct registered keys signed;
- legacy-key rule: once a PQ key is registered, no classical-only transition changes keys;
- atomic cryptographic migration: key change and any paired state change succeed or fail
  together; replay protection and supply invariants are preserved on every reachable state.

Assumed, not proved: signature unforgeability (EUF-CMA) of ML-DSA and SLH-DSA, IND-CCA
security of ML-KEM, hash collision resistance, entropy and key secrecy. Lean states safety as
"if a signature verifies for a registered key then the key owner authorized this message",
and takes that implication as an explicit hypothesis.

## 11. Phased roadmap and acceptance gates

| Phase | Content | Gate to leave the phase |
|---|---|---|
| P0 | This proposal, reviewed; decisions drafted | Written review by someone other than the author; open decisions answered |
| P1 | Spec v1 of signed request with suite id; Lean abstract verification and downgrade proofs | `lake build` green, no `sorry`, documented assumptions |
| P2 | Key registry, rotation, revocation, threshold, recovery: spec, Lean state machine, frame lemmas | Invariants preserved on all reachable states; Python reference agrees |
| P3 | Rust crypto boundary with chosen libraries; KATs, differential and fuzz tests; benchmarks | Dependency choice reviewed; audit status recorded; numbers published |
| P4 | Full state commitment (all rows of section 8), suite and key registries committed | Every consensus-critical element classified and covered or explicitly excluded |
| P5 | Independent cryptographic and protocol review | Findings resolved; no unresolved critical or high |
| P6+ | Transport (ML-KEM hybrid), validator keys and consensus, release signing, testnet | Per `RELEASE_GATES.md` gates C and D |

Nothing in P0 to P5 is production deployment. Production remains gate F.

## 12. External assumptions and unresolved risks

Assumed: ML-DSA, SLH-DSA, ML-KEM and SHA-256 meet their stated security categories; the
chosen libraries implement the standards correctly and without exploitable side channels;
entropy sources are sound; at least k of n threshold holders are honest and uncompromised;
the social and legal recovery process works.

Unresolved:

1. No audited Rust PQ implementation is known (survey dated 2025; to re-verify).
2. Announced errata for FIPS 203 and 204 may change implementation details.
3. Legacy-key race for accounts that never pre-commit a successor key (section 7.4).
4. Signature size (about 20 times larger) may constrain throughput and storage; unmeasured.
5. FIPS 206 (FN-DSA) status unverified; HQC is not a standard yet.
6. Threshold signatures and aggregation for PQ schemes are not standardized; a linear list of
   signatures costs size.
7. Consensus is not selected, so validator and finality signing designs are only requirements.
8. HSM and hardware wallet support for ML-DSA and SLH-DSA is unverified.
9. Whether hybrid (two signatures) is mandatory for all accounts or only for roles is open.
10. Governance and operational security (who holds the threshold keys) cannot be solved by
    cryptography.
11. This design has had no independent review.

## Sources

- NIST FIPS 203, 204, 205 and SP 800-227, IR 8547, CSWP 39, pages on csrc.nist.gov
  (retrieved 2026-11-15).
- NIST news, HQC selected as fifth post-quantum algorithm (March 2025).
- Project Eleven, "The State of Post-Quantum Cryptography in Rust" (2025-07-31).
