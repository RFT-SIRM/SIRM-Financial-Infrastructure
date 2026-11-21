//! Conformance of the Rust request encoding v2 (v1 plus `resolve`) with the independent Python
//! reference: the explicit vectors (bytes), the aggregate digests over the base trace (27816
//! requests) and the resolve trace (25137 requests, 3647 of them `resolve`), the canonical-input
//! property, and the path bytes -> decode -> integrated machine, which must reproduce every outcome
//! token of both traces. Request encoding v1 is unchanged and still refuses `resolve`.
#![allow(dead_code)]

use serde_json::Value;
use sha2::{Digest, Sha256};
use sirm_codec::escrow::Phase;
use sirm_codec::integrated::*;
use sirm_codec::request_v2::*;

include!("support/integrated_load.rs");

fn hex(s: &str) -> Vec<u8> {
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

fn vectors() -> Value {
    serde_json::from_str(include_str!(
        "../../../engineering/canonical_encoding/results/request_v2_vectors.json"
    ))
    .unwrap()
}

fn base_trace() -> Value {
    serde_json::from_str(include_str!(
        "../../../engineering/ledger_core/results/integrated_trace_v0.json"
    ))
    .unwrap()
}

fn resolve_trace() -> Value {
    serde_json::from_str(include_str!(
        "../../../engineering/ledger_core/results/integrated_resolve_trace_v0.json"
    ))
    .unwrap()
}

fn vector_request(v: &Value) -> WireRequest {
    let op = v["op"].as_array().unwrap();
    let f = |k: usize| num(&op[k]);
    let op = match op[0].as_str().unwrap() {
        "transfer" => Op::Transfer {
            src: f(1) as u32,
            dst: f(2) as u32,
            asset: f(3) as u32,
            amount: f(4),
        },
        "issue" => Op::Issue {
            issuer: f(1) as u32,
            recipient: f(2) as u32,
            asset: f(3) as u32,
            amount: f(4),
        },
        "burn" => Op::Burn {
            holder: f(1) as u32,
            asset: f(2) as u32,
            amount: f(3),
        },
        "open" => Op::Open {
            id: f(1) as usize,
            depositor: f(2) as u32,
            beneficiary: f(3) as u32,
            asset: f(4) as u32,
            amount: f(5),
        },
        "release" => Op::Release(f(1) as usize),
        "cancel" => Op::Cancel(f(1) as usize),
        "expire" => Op::Expire(f(1) as usize),
        "dispute" => Op::Dispute {
            id: f(1) as usize,
            claimant: f(2) as u32,
        },
        "advance" => Op::Advance(f(1) as u64),
        "migrate" => Op::Migrate(f(1)),
        "resolve" => Op::Resolve {
            id: f(1) as usize,
            to_beneficiary: f(2) != 0,
        },
        other => panic!("op {other}"),
    };
    WireRequest {
        request_id: hex(v["request_id"].as_str().unwrap()).try_into().unwrap(),
        request: Request {
            principal: v["principal"].as_u64().unwrap() as u32,
            nonce: num(&v["nonce"]) as u64,
            op,
        },
    }
}

#[test]
fn vectors_encode_to_the_python_bytes_and_decode_back() {
    let d = vectors();
    let vs = d["vectors"].as_array().unwrap();
    assert!(vs.len() >= 19);
    let mut resolves = 0;
    for v in vs {
        let w = vector_request(v);
        let bytes = hex(v["hex"].as_str().unwrap());
        assert_eq!(encode(&w).unwrap(), bytes, "{}", v["name"]);
        assert_eq!(decode(&bytes).unwrap(), w, "{}", v["name"]);
        if matches!(w.request.op, Op::Resolve { .. }) {
            resolves += 1;
            assert_eq!(bytes.len(), 62);
        }
    }
    assert_eq!(resolves, 3);
}

fn run_trace(d: &Value, key_n: &str, key_h: &str) {
    let want = vectors()["checks"][key_h].as_str().unwrap().to_string();
    let n_want = vectors()["checks"][key_n].as_u64().unwrap();
    let (accounts, assets) = (
        d["accounts"].as_u64().unwrap() as u32,
        d["assets"].as_u64().unwrap() as u32,
    );
    let mut agg = Sha256::new();
    let (mut n, mut resolves) = (0u64, 0u64);
    for (ei, ep) in d["episodes"].as_array().unwrap().iter().enumerate() {
        let mut m = machine_for(ep, accounts, assets);
        for (row, tok) in ep["requests"]
            .as_array()
            .unwrap()
            .iter()
            .zip(ep["tokens"].as_array().unwrap())
        {
            let (id, request) = request(row.as_array().unwrap());
            if matches!(request.op, Op::Resolve { .. }) {
                resolves += 1;
            }
            let w = WireRequest {
                request_id: id,
                request,
            };
            let bytes = encode(&w).unwrap();
            agg.update(Sha256::digest(&bytes));
            n += 1;
            let back = decode(&bytes).unwrap();
            assert_eq!(back, w);
            assert_eq!(
                m.process(back.request_id, back.request).token(),
                tok.as_str().unwrap(),
                "episode {ei}"
            );
        }
    }
    assert_eq!(n, n_want);
    let got: String = agg.finalize().iter().map(|b| format!("{b:02x}")).collect();
    assert_eq!(got, want);
    let _ = resolves;
}

#[test]
fn base_trace_matches_the_python_aggregate_and_runs_through_the_machine() {
    run_trace(&base_trace(), "trace_requests", "trace_aggregate_sha256");
}

#[test]
fn resolve_trace_matches_the_python_aggregate_and_runs_through_the_machine() {
    let d = resolve_trace();
    run_trace(
        &d,
        "resolve_trace_requests",
        "resolve_trace_aggregate_sha256",
    );
    let resolves = d["episodes"]
        .as_array()
        .unwrap()
        .iter()
        .flat_map(|e| e["requests"].as_array().unwrap())
        .filter(|r| r[3] == "resolve")
        .count() as u64;
    assert_eq!(
        resolves,
        vectors()["checks"]["resolve_trace_resolve_requests"]
            .as_u64()
            .unwrap()
    );
}

#[test]
fn only_canonical_inputs_are_accepted() {
    let d = vectors();
    let mut checked = 0;
    for v in d["vectors"].as_array().unwrap() {
        let bytes = hex(v["hex"].as_str().unwrap());
        for i in 0..bytes.len() {
            let mut m = bytes.clone();
            m[i] ^= 0x01;
            if let Ok(w) = decode(&m) {
                assert_eq!(
                    encode(&w).unwrap(),
                    m,
                    "non-canonical input accepted at byte {i}"
                );
            }
            checked += 1;
        }
        for cut in 0..bytes.len() {
            assert!(decode(&bytes[..cut]).is_err());
        }
        let mut extra = bytes.clone();
        extra.push(0);
        assert_eq!(decode(&extra), Err(DecodeError::TrailingBytes));
    }
    assert!(checked > 1200);
    let good = hex(d["vectors"][1]["hex"].as_str().unwrap());
    for t in 11..=255u8 {
        let mut m = good.clone();
        m[56] = t;
        assert_eq!(decode(&m), Err(DecodeError::UnknownOperation(t)));
    }
    // the v0 and v1 domains are not accepted
    for old in [b"SIRM/FTX/v0\0", b"SIRM/FTX/v1\0"] {
        let mut m = good.clone();
        m[..12].copy_from_slice(old);
        assert_eq!(decode(&m), Err(DecodeError::BadDomain));
    }
    assert_eq!(decode(b""), Err(DecodeError::BadDomain));
}

#[test]
fn resolve_flag_other_than_zero_or_one_is_rejected() {
    let w = WireRequest {
        request_id: [7; 32],
        request: Request {
            principal: 3,
            nonce: 9,
            op: Op::Resolve {
                id: 4,
                to_beneficiary: true,
            },
        },
    };
    let bytes = encode(&w).unwrap();
    assert_eq!(bytes.len(), 62);
    assert_eq!(*bytes.last().unwrap(), 1);
    for flag in 2..=255u8 {
        let mut m = bytes.clone();
        *m.last_mut().unwrap() = flag;
        assert_eq!(decode(&m), Err(DecodeError::NonCanonicalFlag(flag)));
    }
}

#[test]
fn escrow_ids_above_u32_cannot_be_encoded() {
    let big = usize::try_from(u64::from(u32::MAX) + 1).unwrap();
    for op in [
        Op::Release(big),
        Op::Resolve {
            id: big,
            to_beneficiary: false,
        },
    ] {
        let w = WireRequest {
            request_id: [0; 32],
            request: Request {
                principal: 0,
                nonce: 0,
                op,
            },
        };
        assert_eq!(encode(&w), Err(EncodeError::IdOutOfRange));
    }
}

#[test]
fn v1_is_unchanged_and_still_refuses_resolve() {
    use sirm_codec::request_v1 as v1;
    let w = WireRequest {
        request_id: [1; 32],
        request: Request {
            principal: 1,
            nonce: 1,
            op: Op::Resolve {
                id: 0,
                to_beneficiary: true,
            },
        },
    };
    assert_eq!(v1::encode(&w), Err(v1::EncodeError::UnsupportedOperation));
    // for every other operation, v2 differs from v1 only in the domain
    let other = WireRequest {
        request_id: [1; 32],
        request: Request {
            principal: 1,
            nonce: 1,
            op: Op::Dispute { id: 2, claimant: 3 },
        },
    };
    let (a, b) = (v1::encode(&other).unwrap(), encode(&other).unwrap());
    assert_eq!(a[12..], b[12..]);
    assert_ne!(a[..12], b[..12]);
    assert_eq!(v1::decode(&b), Err(v1::DecodeError::BadDomain));
}
