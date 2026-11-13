use serde_json::Value;
use sirm_codec::*;
use std::collections::HashSet;

fn hex(s: &str) -> Vec<u8> {
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

fn from_vector(v: &Value) -> Request {
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
        other => panic!("unknown op {other}"),
    };
    Request {
        request_id: hex(v["request_id"].as_str().unwrap()).try_into().unwrap(),
        principal: v["principal"].as_u64().unwrap().try_into().unwrap(),
        nonce: v["nonce"].as_u64().unwrap(),
        op,
    }
}

fn vectors() -> Vec<Value> {
    let text = include_str!("../../../engineering/canonical_encoding/results/vectors_v0.json");
    serde_json::from_str::<Value>(text).unwrap()["vectors"]
        .as_array()
        .unwrap()
        .clone()
}

#[test]
fn bytes_and_digest_match_python_reference() {
    let vs = vectors();
    assert_eq!(vs.len(), 5);
    for v in &vs {
        let r = from_vector(v);
        let e = encode(&r);
        assert_eq!(e, hex(v["bytes_hex"].as_str().unwrap()), "{}", v["name"]);
        assert_eq!(e.len() as u64, v["length"].as_u64().unwrap());
        assert_eq!(
            sha256_hex(&e),
            v["sha256"].as_str().unwrap(),
            "{}",
            v["name"]
        );
        assert_eq!(decode(&e), Ok(r));
    }
}

#[test]
fn malformed_input_is_rejected() {
    let r = from_vector(&vectors()[1]);
    let good = encode(&r);
    assert_eq!(decode(&good[..good.len() - 1]), Err(DecodeError::Truncated));
    let mut t = good.clone();
    t.push(0);
    assert_eq!(decode(&t), Err(DecodeError::TrailingBytes));
    let mut d = good.clone();
    d[0] = b'X';
    assert_eq!(decode(&d), Err(DecodeError::BadDomain));
    let mut g = good.clone();
    g[DOMAIN.len() + 32 + 12] = 9;
    assert_eq!(decode(&g), Err(DecodeError::UnknownOperation(9)));
    assert_eq!(decode(&[]), Err(DecodeError::BadDomain));
}

#[test]
fn exhaustive_small_domain_injective_and_roundtrips() {
    let small = [0u32, 1, 2];
    let amts = [0u128, 1, 255, 256];
    let mut seen = HashSet::new();
    let mut count = 0;
    for pr in small {
        for nc in small {
            let mut reqs = Vec::new();
            for a in small {
                for b in small {
                    for c in small {
                        for m in amts {
                            reqs.push(Op::Transfer {
                                source: a,
                                destination: b,
                                asset: c,
                                amount: m,
                            });
                            reqs.push(Op::Issue {
                                issuer: a,
                                recipient: b,
                                asset: c,
                                amount: m,
                            });
                        }
                    }
                }
            }
            for a in small {
                for c in small {
                    for m in amts {
                        reqs.push(Op::Burn {
                            holder: a,
                            asset: c,
                            amount: m,
                        });
                    }
                }
            }
            for op in reqs {
                let r = Request {
                    request_id: [pr as u8; 32],
                    principal: pr,
                    nonce: nc as u64,
                    op,
                };
                let e = encode(&r);
                assert!(seen.insert(e.clone()), "collision");
                assert_eq!(decode(&e), Ok(r));
                count += 1;
            }
        }
    }
    assert_eq!(count, 2268);
}
