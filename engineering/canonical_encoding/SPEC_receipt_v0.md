# Canonical receipt encoding v0 (proposal, not adopted)

Executable reference: `scripts/canonical_receipt_reference.py`; vectors: `results/receipt_vectors_v0.json`;
Rust: `rust/sirm-codec/src/receipt.rs`. It builds on the request encoding of `SPEC_v0.md` and serializes the
stored responses of `SIRM/FinancialTransactionEnvelope.lean` (`FinancialTransactionReceipt`) and
`SIRM/FinancialTransactionDenials.lean` (`FinancialTransactionDenialReceipt`).

## Decisions of this proposal

1. **A receipt binds the whole request.** The receipt embeds the canonical request encoding (domain tag, request ID,
   principal, nonce, operation). The Lean response also stores the request ID; it is the request ID inside the embedded
   request, not a second copy.
2. **Only responses that Lean stores are encoded.** Success and the two denial families (authorization,
   insufficient funds). Replays return the stored response; same-ID conflicts, stale and future nonces and
   range/overflow failures store nothing and have no receipt.
3. **No state hash in v0.** Receipts carry no state root or ledger digest. State commitments are a separate decision
   (the third open protocol item); a receipt that carries one would be a v1 layout with its own domain tag.
4. **No signature or chain id in v0.** They belong to the request/receipt authentication decision (the second open
   protocol item) and would also be a new version.
5. **Non-redundant canonical form.** Lean's stored fields are kept (`acceptedNonce`, `nextNonce`, `expectedNonce`),
   but the decoder rejects any receipt that violates the Lean construction: `acceptedNonce` = request nonce,
   `nextNonce` = `acceptedNonce` + 1, a denial's `expectedNonce` = request nonce, and the denial reason matches the
   operation family. So every accepted byte string is the unique encoding of one consistent receipt.

## Layout (big-endian)

| Field | Bytes | Notes |
| --- | --- | --- |
| domain tag | 12 | ASCII `SIRM/RCT/v0` + `0x00` (differs from the request tag `SIRM/FTX/v0`) |
| status | 1 | 0 accepted, 1 denied |
| request encoding | 85 or 81 | exactly the v0 request encoding (transfer, issue: 85; burn: 81) |
| accepted: accepted nonce, next nonce | 8 + 8 | u64 each |
| denied: expected nonce, reason | 8 + 1 | reason codes in Lean enum order |

Reason codes: 0 `transferAuthorizationDenied`, 1 `issueAuthorizationDenied`, 2 `burnAuthorizationDenied`,
3 `transferInsufficientFunds`, 4 `burnInsufficientFunds`.
Total: accepted 13 + request + 16 (114 or 110 bytes); denied 13 + request + 9 (107 or 103 bytes). Digest: SHA-256 of the
full byte string.

## Checked properties (finite, by the script and the Rust tests)

- Round trip of 11 vectors (all response kinds and operation families, plus all-maximum values).
- Exhaustive small-domain run (4374 receipts): all encodings distinct, exact lengths, exact round trip, no receipt
  encoding starts with the request domain tag.
- Decoder rejects truncated input, trailing bytes, wrong domain, unknown status, unknown operation tag, a corrupted
  embedded request, an accepted nonce that differs from the request nonce, `nextNonce` != `acceptedNonce` + 1, a denial
  whose expected nonce differs, an unknown reason, a reason of the wrong operation family, and a bare request.
- The encoder refuses every receipt the decoder would refuse (also: nonce `u64::MAX` cannot be accepted because its
  successor is not a u64; the Rust processor also refuses such a request as an overflow).
- Rust: every response stored by the integrated processor (`machine::Stored`) encodes to a canonical receipt that
  decodes back to the same receipt, and an exact retry returns byte-identical receipt bytes.

## Not covered (explicit gaps)

- No Lean theorem about this layout (no `decode_encode`/injectivity for receipts); the evidence is the executable
  reference, finite exhaustive runs and the Rust conformance tests. Lean models `Nat` (unbounded); the u64 nonce bound
  is an explicit extension.
- Signatures, chain id, expiry, state commitments, and an authenticated receipt log are not defined.
- Field widths and the status/reason numbering are proposals, not an adopted protocol format.
