# Request encoding v2 (proposal, not adopted)

Request encoding v1 plus the arbiter operation `resolve`
(`docs/INTEGRATED_STATE_MACHINE_PROPOSAL.md`). All integers big-endian. Request encoding v1
(`SPEC_request_v1.md`) and its frozen vectors are unchanged.

```
domain      12  "SIRM/FTX/v2\0"
request id  32
principal    4  u32
nonce        8  u64
tag          1  u8
fields          by tag
```

Tags 0 to 9 and their fields are exactly those of v1; for them the v2 bytes differ from the v1 bytes
only in the domain. New:

| tag | operation | fields | total |
|---|---|---|---|
| 10 | resolve | id u32, to_beneficiary u8 | 62 |

`to_beneficiary` is `1` for the beneficiary (the escrow is settled as `released`) and `0` for the
depositor (settled as `cancelled`). Any other byte is rejected.

## Decoding rules

- Wrong domain (including the v0 and v1 domains), truncated input, an unknown tag, trailing bytes or a
  `to_beneficiary` byte other than 0 or 1 are rejected. No padding, no optional field: the encoding is
  injective and every accepted input is the canonical encoding of exactly one request.
- An escrow id above `u32::MAX` cannot be encoded (encoder error, not a silent truncation).
- A v1 decoder rejects every v2 input (domain) and a v2 decoder rejects every v1 input.

## Evidence

- `scripts/request_v2_reference.py`: independent encoder/decoder, 19 vectors
  (`results/request_v2_vectors.json`), round trip on 5463 cases, 1374 single-byte mutations, 176 tag
  changes, 245 unknown tags, 254 non-canonical `resolve` flag values, 12 invalid requests rejected,
  cross-checks against v1, and the encoding of all 27816 requests of `integrated_trace_v0.json` and all
  25137 requests (3647 of them `resolve`) of `integrated_resolve_trace_v0.json` (aggregate SHA-256 in the
  vector file).
- `rust/sirm-codec/src/request_v2.rs` and `tests/request_v2_conformance.rs`: the Rust codec reproduces
  the vector bytes and both aggregate digests, accepts only canonical inputs under every single-bit
  mutation, and `bytes -> decode -> Machine::process` reproduces every outcome token of both traces.

## Lean

`SIRM/RequestEncodingV2.lean` (no Mathlib) models this layout without the domain prefix and proves the round
trip, injectivity, that every byte string the decoder accepts is the encoding of the request it returns
(with the `resolve` side byte restricted to 0 or 1), and that an unknown tag is rejected. The field-width
table in Lean is written by hand; its agreement with the Rust and Python tables is covered by the
conformance test, not by a proof.

## Not covered

- Signed requests (`SPEC_signed_request_v2.md`) still carry request v1, so a signed `resolve` does not
  exist yet; the state commitment (`SPEC_state_commitment_v5.md`) does not cover a machine whose cache
  holds a `resolve` request (`state_root_v5` is `None`).
- Differential evidence, not a refinement proof. Proposal only, not adopted.
