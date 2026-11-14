//! Conformance of the Rust receipt codec with the Python reference vectors
//! (`engineering/canonical_encoding/results/receipt_vectors_v0.json`), the same
//! malformed-input rejections, and a link to the integrated processor: every response the
//! processor stores encodes to a canonical receipt that decodes back to the same receipt.

use serde_json::Value;
use sha2::{Digest, Sha256};
use sirm_codec::auth::*;
use sirm_codec::ledger::*;
use sirm_codec::machine::{self, Outcome, Processor};
use sirm_codec::receipt::*;
use sirm_codec::{Op, Request};

fn hex(s: &str) -> Vec<u8> {
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

fn reason(name: &str) -> Reason {
    match name {
        "transferAuthorizationDenied" => Reason::TransferAuthorizationDenied,
        "issueAuthorizationDenied" => Reason::IssueAuthorizationDenied,
        "burnAuthorizationDenied" => Reason::BurnAuthorizationDenied,
        "transferInsufficientFunds" => Reason::TransferInsufficientFunds,
        "burnInsufficientFunds" => Reason::BurnInsufficientFunds,
        o => panic!("reason {o}"),
    }
}

fn from_vector(v: &Value) -> Receipt {
    let f = |i: usize| v["op"][i].as_str().unwrap();
    let u32f = |i: usize| f(i).parse::<u32>().unwrap();
    let u128f = |i: usize| f(i).parse::<u128>().unwrap();
    let op = match f(0) {
        "transfer" => Op::Transfer {
            source: u32f(1),
            destination: u32f(2),
            asset: u32f(3),
            amount: u128f(4),
        },
        "issue" => Op::Issue {
            issuer: u32f(1),
            recipient: u32f(2),
            asset: u32f(3),
            amount: u128f(4),
        },
        "burn" => Op::Burn {
            holder: u32f(1),
            asset: u32f(2),
            amount: u128f(3),
        },
        o => panic!("op {o}"),
    };
    let r = |i: usize| v["response"][i].as_str().unwrap();
    let response = match r(0) {
        "accepted" => Response::Accepted {
            accepted_nonce: r(1).parse().unwrap(),
            next_nonce: r(2).parse().unwrap(),
        },
        "denied" => Response::Denied {
            expected_nonce: r(1).parse().unwrap(),
            reason: reason(r(2)),
        },
        o => panic!("response {o}"),
    };
    Receipt {
        request: Request {
            request_id: hex(v["request_id"].as_str().unwrap()).try_into().unwrap(),
            principal: v["principal"].as_u64().unwrap() as u32,
            nonce: v["nonce"].as_u64().unwrap(),
            op,
        },
        response,
    }
}

fn vectors() -> Vec<Value> {
    let d: Value = serde_json::from_str(include_str!(
        "../../../engineering/canonical_encoding/results/receipt_vectors_v0.json"
    ))
    .unwrap();
    d["vectors"].as_array().unwrap().clone()
}

#[test]
fn vectors_encode_to_reference_bytes_digest_and_decode_back() {
    let vs = vectors();
    assert_eq!(vs.len(), 11);
    for v in &vs {
        let r = from_vector(v);
        let bytes = encode(&r).unwrap();
        let name = v["name"].as_str().unwrap();
        assert_eq!(bytes, hex(v["bytes_hex"].as_str().unwrap()), "{name}");
        assert_eq!(bytes.len() as u64, v["length"].as_u64().unwrap(), "{name}");
        let digest: String = Sha256::digest(&bytes)
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect();
        assert_eq!(digest, v["sha256"].as_str().unwrap(), "{name}");
        assert_eq!(decode(&bytes), Ok(r), "{name}");
    }
}

#[test]
fn malformed_and_inconsistent_receipts_are_rejected() {
    let vs = vectors();
    let accepted = encode(&from_vector(&vs[0])).unwrap();
    let denied = encode(&from_vector(&vs[1])).unwrap();
    let l = DOMAIN.len() + 1;
    let n = accepted.len();
    let mut cases: Vec<(&str, Vec<u8>, ReceiptError)> = Vec::new();
    cases.push((
        "truncated",
        accepted[..n - 1].to_vec(),
        ReceiptError::Truncated,
    ));
    let mut t = accepted.clone();
    t.push(0);
    cases.push(("trailing", t, ReceiptError::TrailingBytes));
    let mut b = accepted.clone();
    b[0] = b'X';
    cases.push(("bad domain", b, ReceiptError::BadDomain));
    let mut b = accepted.clone();
    b[DOMAIN.len()] = 2;
    cases.push(("bad status", b, ReceiptError::UnknownStatus(2)));
    let mut b = accepted.clone();
    b[l + 56] = 9;
    cases.push((
        "bad op tag",
        b,
        ReceiptError::Request(sirm_codec::DecodeError::UnknownOperation(9)),
    ));
    let mut b = accepted.clone();
    b[l] = b'X';
    cases.push((
        "embedded request domain",
        b,
        ReceiptError::Request(sirm_codec::DecodeError::BadDomain),
    ));
    let mut b = accepted.clone();
    b[n - 16..n - 8].copy_from_slice(&8u64.to_be_bytes());
    b[n - 8..].copy_from_slice(&9u64.to_be_bytes());
    cases.push((
        "accepted nonce differs",
        b,
        ReceiptError::AcceptedNonceMismatch,
    ));
    let mut b = accepted.clone();
    b[n - 8..].copy_from_slice(&12u64.to_be_bytes());
    cases.push(("next not +1", b, ReceiptError::NextNonceMismatch));
    let m = denied.len();
    let mut b = denied.clone();
    b[m - 9..m - 1].copy_from_slice(&8u64.to_be_bytes());
    cases.push(("expected differs", b, ReceiptError::ExpectedNonceMismatch));
    let mut b = denied.clone();
    b[m - 1] = 5;
    cases.push(("unknown reason", b, ReceiptError::UnknownReason(5)));
    let mut b = denied.clone();
    b[m - 1] = 1;
    cases.push(("reason wrong family", b, ReceiptError::ReasonMismatch));
    cases.push((
        "request bytes as receipt",
        sirm_codec::encode(&from_vector(&vs[0]).request),
        ReceiptError::BadDomain,
    ));
    for (name, bytes, want) in cases {
        assert_eq!(decode(&bytes), Err(want), "{name}");
    }
}

#[test]
fn encoder_refuses_what_the_decoder_would_refuse() {
    let vs = vectors();
    let base = from_vector(&vs[0]);
    let nonce = base.request.nonce;
    let with = |response| Receipt {
        request: base.request.clone(),
        response,
    };
    for bad in [
        Response::Accepted {
            accepted_nonce: nonce + 1,
            next_nonce: nonce + 2,
        },
        Response::Accepted {
            accepted_nonce: nonce,
            next_nonce: nonce,
        },
        Response::Denied {
            expected_nonce: nonce + 1,
            reason: Reason::TransferAuthorizationDenied,
        },
        Response::Denied {
            expected_nonce: nonce,
            reason: Reason::IssueAuthorizationDenied,
        },
    ] {
        assert!(encode(&with(bad)).is_err(), "{bad:?}");
    }
    // u64::MAX nonce cannot be accepted: its successor is not representable.
    let mut max = base.clone();
    max.request.nonce = u64::MAX;
    max.response = Response::Accepted {
        accepted_nonce: u64::MAX,
        next_nonce: 0,
    };
    assert_eq!(encode(&max), Err(ReceiptError::NextNonceMismatch));
}

#[test]
fn every_response_stored_by_the_processor_has_a_canonical_receipt() {
    // Small deterministic stream through the integrated processor with a permissive policy.
    let mut grants = Vec::new();
    for a in 0..3u32 {
        grants.push(Grant {
            principal: 0,
            scope: Scope::Burn { holder: a },
            asset: 0,
            max_amount: 100,
        });
        for b in 0..3u32 {
            grants.push(Grant {
                principal: 0,
                scope: Scope::Transfer {
                    source: a,
                    destination: b,
                },
                asset: 0,
                max_amount: 100,
            });
            grants.push(Grant {
                principal: 0,
                scope: Scope::Issue {
                    issuer: a,
                    recipient: b,
                },
                asset: 0,
                max_amount: 100,
            });
        }
    }
    let control: Vec<(u32, u32)> = (0..2).map(|a| (0, a)).collect(); // account 2 is not controlled
    let policy = Policy::new(&grants, &control).unwrap();
    let mut p = Processor::new(Holdings::new(3, 1), policy);
    let (mut accepted, mut denied) = (0, 0);
    let mut x: u64 = 0x9E37_79B9;
    for i in 0..600u64 {
        x = x
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let k = (x >> 33) as u32;
        let (a, b, amt) = (k % 3, (k >> 3) % 3, ((k >> 6) % 120) as u128);
        let operation = match k % 7 {
            0..=2 => machine::Operation::Transfer {
                source: a,
                destination: b,
                asset: 0,
                amount: amt,
            },
            3 | 4 => machine::Operation::Issue {
                issuer: a,
                recipient: b,
                asset: 0,
                amount: amt,
            },
            _ => machine::Operation::Burn {
                holder: a,
                asset: 0,
                amount: amt,
            },
        };
        let req = machine::Request {
            principal: 0,
            nonce: p.next_nonce(0),
            operation,
        };
        let mut id = [0u8; 32];
        id[24..].copy_from_slice(&i.to_be_bytes());
        match p.process(id, req) {
            Outcome::Accepted(s) | Outcome::DeniedCached(s) => {
                let is_ok = matches!(s, machine::Stored::Accepted { .. });
                let receipt = from_processor(id, &req, &s);
                let bytes = encode(&receipt).expect("processor responses are consistent");
                assert_eq!(decode(&bytes), Ok(receipt));
                // an exact retry returns the stored response, hence byte-identical receipt bytes
                match p.process(id, req) {
                    Outcome::Replay(s2) => {
                        assert_eq!(encode(&from_processor(id, &req, &s2)).unwrap(), bytes)
                    }
                    o => panic!("expected replay, got {o:?}"),
                }
                if is_ok {
                    accepted += 1
                } else {
                    denied += 1
                }
            }
            Outcome::Invalid(_) => {}
            o => panic!("unexpected {o:?}"),
        }
    }
    assert!(
        accepted > 100 && denied > 100,
        "weak coverage {accepted}/{denied}"
    );
}
