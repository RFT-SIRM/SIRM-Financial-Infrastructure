# Request encoding v1 (proposal, not adopted)

Canonical byte encoding of one request of the integrated state machine
(`docs/INTEGRATED_STATE_MACHINE_PROPOSAL.md`, step I3). All integers big-endian.

```
domain      12  "SIRM/FTX/v1\0"
request id  32
principal    4  u32
nonce        8  u64
tag          1  u8
fields          by tag
```

The prefix is 57 bytes. Fields by tag (ids of escrows are u32 on the wire):

| tag | operation | fields | total |
|---|---|---|---|
| 0 | transfer | src u32, dst u32, asset u32, amount u128 | 85 |
| 1 | issue | issuer u32, recipient u32, asset u32, amount u128 | 85 |
| 2 | burn | holder u32, asset u32, amount u128 | 81 |
| 3 | open | id u32, depositor u32, beneficiary u32, asset u32, amount u128 | 89 |
| 4 | release | id u32 | 61 |
| 5 | cancel | id u32 | 61 |
| 6 | expire | id u32 | 61 |
| 7 | dispute | id u32, claimant u32 | 65 |
| 8 | advance | to u64 | 65 |
| 9 | migrate | amount u128 | 73 |

## Decoding rules

- Wrong domain (including the v0 domain `SIRM/FTX/v0\0`), truncated input, an unknown tag or trailing
  bytes are rejected. There is no padding and no optional field, so the encoding is injective and every
  accepted input is the canonical encoding of exactly one request.
- An escrow id above `u32::MAX` cannot be encoded (encoder error, not a silent truncation).
- The request id is part of the signed bytes; it is the replay and conflict key of the pipeline.

## Evidence

- `scripts/request_v1_reference.py`: independent encoder/decoder, 16 vectors
  (`results/request_v1_vectors.json`), round trip on 5409 cases, 1188 single-byte mutations, 130 tag
  changes, 246 unknown tags, 6 malformed inputs, 8 invalid requests rejected, and the encoding of all
  27816 requests of `integrated_trace_v0.json` (aggregate SHA-256 `516fd226...b7824`).
- `rust/sirm-codec/src/request_v1.rs` and `tests/request_v1_conformance.rs`: the Rust codec reproduces the
  vector bytes and the aggregate digest, accepts only canonical inputs under every single-bit mutation, and
  `bytes -> decode -> Machine::process` reproduces every outcome token of the 402 reference episodes.

## Not covered

- Signed requests (versions v0 and v1) still embed only the v0 request bytes. Carrying request v1 needs a
  new signed version; it is not defined yet.
- Differential evidence, not a refinement proof. Proposal only, not adopted.
