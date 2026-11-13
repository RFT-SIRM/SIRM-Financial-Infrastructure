# Canonical request encoding v0 (proposal, not adopted)

Executable reference: `scripts/canonical_encoding_reference.py`; vectors: `results/vectors_v0.json`.
Purpose: give the future Rust implementation a byte-exact target and conformance vectors for the
`FinancialTransactionRequest` payload in `SIRM/FinancialTransactionEnvelope.lean`.

## Layout (big-endian, fixed width, no optional fields)

| Field | Bytes | Notes |
| --- | --- | --- |
| domain tag | 12 | ASCII `SIRM/FTX/v0` + `0x00` |
| request ID | 32 | opaque |
| principal | 4 | u32 account index |
| nonce | 8 | u64 |
| operation tag | 1 | 0 transfer, 1 issue, 2 burn |
| operation fields | 3x4+16 or 2x4+16 | transfer: source, destination, asset, amount; issue: issuer, recipient, asset, amount; burn: holder, asset, amount. Account/asset = u32, amount = u128 |

Total 85 bytes (transfer, issue) or 81 bytes (burn). Digest: SHA-256 of the full byte string.

## Checked properties (finite, by the script)

- Round trip on boundary vectors, including all-maximum values.
- Exhaustive small-domain run (2268 requests): all encodings distinct and every one decodes back exactly.
- Decoder rejects truncated input, trailing bytes, wrong domain tag and unknown operation tag.
- Encoder rejects values outside u32/u64/u128 and negatives.
- Output is byte-identical across runs.

## Not covered (explicit gaps)

- Lean models `Nat` (unbounded). Here nonce and amount are bounded; a Lean-to-Rust refinement must state the bound and prove no in-range request is rejected and every overflow is rejected deterministically.
- Lean (`SIRM/CanonicalEncoding.lean`, `SIRM/CanonicalRequestEncoding.lean`) proves, for a concrete bounded request record: fixed-width big-endian digit codec (value recovery, length, digit bound, injectivity on [0, 256^n)), `decode_encode` and `encodeRequest_injective` for in-range requests. Not proved: the link to the polymorphic `FinancialTransactionRequest`, the inverse direction on arbitrary digit lists (every digit list of the right length decodes and re-encodes to itself), the constant domain-tag prefix, and the byte-range bound for the whole encoding.
- Chain id, protocol version negotiation, expiry, signatures/thresholds, response and receipt encoding, and state commitments are not defined.
- Field widths are proposals; the real account/asset universe size (`accountCount`) may allow narrower or require wider indices.
