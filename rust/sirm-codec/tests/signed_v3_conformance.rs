//! Conformance of the Rust signed-request layer v3 (request encoding v2, including `resolve`) with the independent Python reference
//! (`engineering/canonical_encoding/results/signed_request_v3_vectors.json`). Ed25519 is deterministic
//! and verified in Rust, so those vectors are signed again here and must match byte for byte; ML-DSA-65
//! and hybrid wires get every structural check and are then refused with `VerifierUnavailable` (this
//! crate has no post-quantum verifier): never accepted. Also: every single-byte mutation, the downgrade
//! cases, and an end-to-end node that only lets verified requests reach the integrated machine.

use ed25519_dalek::{Signer, SigningKey};
use serde_json::Value;
use sirm_codec::integrated::*;
use sirm_codec::request_v2::{decode, encode, WireRequest};
use sirm_codec::signed_v3::*;

fn hex(s: &str) -> Vec<u8> {
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

fn doc() -> Value {
    serde_json::from_str(include_str!(
        "../../../engineering/canonical_encoding/results/signed_request_v3_vectors.json"
    ))
    .unwrap()
}

fn registry(d: &Value) -> KeyRegistry {
    let mut r = KeyRegistry::new();
    for (p, info) in d["principals"].as_object().unwrap() {
        let suite = u16::from_str_radix(info["suite"].as_str().unwrap(), 16).unwrap();
        r.insert(
            p.parse().unwrap(),
            suite,
            &hex(info["public_hex"].as_str().unwrap()),
        )
        .unwrap();
    }
    // a principal registered under a suite that is only proposed
    r.insert(3, SLH_DSA_128S, &[0u8; 32]).unwrap();
    r
}

fn suite_of(wire: &[u8]) -> u16 {
    u16::from_be_bytes([wire[20], wire[21]])
}

fn expected(kind: &str, wire: &[u8]) -> SignedError {
    match kind {
        "bad_domain" => SignedError::BadDomain,
        "truncated" => SignedError::Truncated,
        "unknown_suite" => SignedError::UnknownSuite,
        "trailing_bytes" => SignedError::TrailingBytes,
        "wrong_chain" => SignedError::WrongChain,
        "unknown_principal" => SignedError::UnknownPrincipal,
        "suite_mismatch" => SignedError::SuiteMismatch,
        "suite_not_allowed" => SignedError::SuiteNotAllowed,
        // without a verifier the answer for a post-quantum wire is "unavailable", never "accepted"
        "bad_signature" if suite_of(wire) == ED25519 => SignedError::BadSignature,
        "bad_signature" => SignedError::VerifierUnavailable,
        other => panic!("{other}"),
    }
}

#[test]
fn valid_vectors() {
    let d = doc();
    let reg = registry(&d);
    let mut ed = 0;
    for v in d["valid"].as_array().unwrap() {
        let wire = hex(v["wire_hex"].as_str().unwrap());
        let chain: u64 = v["chain_id"].as_str().unwrap().parse().unwrap();
        let want = decode(&hex(v["request_hex"].as_str().unwrap())).unwrap();
        assert_eq!(
            encode(&want).unwrap(),
            hex(v["request_hex"].as_str().unwrap())
        );
        match suite_of(&wire) {
            ED25519 => {
                assert_eq!(
                    verify(&wire, chain, &reg, true).unwrap(),
                    want,
                    "{}",
                    v["name"]
                );
                assert_eq!(
                    verify(&wire, chain, &reg, false),
                    Err(SignedError::SuiteNotAllowed)
                );
                ed += 1;
            }
            _ => {
                // structure, chain, principal, suite and policy all pass; no verifier: refused
                assert_eq!(
                    verify(&wire, chain, &reg, true),
                    Err(SignedError::VerifierUnavailable),
                    "{}",
                    v["name"]
                );
            }
        }
    }
    assert!(ed >= 8);
}

#[test]
fn ed25519_signatures_are_reproduced_byte_for_byte() {
    let d = doc();
    let seed: [u8; 32] = hex(d["principals"]["2"]["seed_hex"].as_str().unwrap())
        .try_into()
        .unwrap();
    let sk = SigningKey::from_bytes(&seed);
    let pk = hex(d["principals"]["2"]["public_hex"].as_str().unwrap());
    assert_eq!(sk.verifying_key().to_bytes().to_vec(), pk);
    let kid = key_id(ED25519, &pk);
    let mut n = 0;
    for v in d["valid"].as_array().unwrap() {
        let wire = hex(v["wire_hex"].as_str().unwrap());
        if suite_of(&wire) != ED25519 {
            continue;
        }
        let chain: u64 = v["chain_id"].as_str().unwrap().parse().unwrap();
        let req = &wire[22..wire.len() - 64];
        let sig = sk.sign(&signing_message(chain, ED25519, &kid, req));
        assert_eq!(
            sig.to_bytes().to_vec(),
            wire[wire.len() - 64..].to_vec(),
            "{}",
            v["name"]
        );
        assert_eq!(encode_wire(chain, ED25519, req, &sig.to_bytes()), wire);
        n += 1;
    }
    assert!(n >= 8);
}

#[test]
fn negative_cases() {
    let d = doc();
    let reg = registry(&d);
    let mut n = 0;
    for c in d["negative"].as_array().unwrap() {
        let wire = hex(c["wire_hex"].as_str().unwrap());
        let chain: u64 = c["node_chain"].as_str().unwrap().parse().unwrap();
        let allow = c["allow_deprecated"].as_bool().unwrap();
        let got = verify(&wire, chain, &reg, allow);
        let kind = c["expect"].as_str().unwrap();
        if kind == "unknown_operation" {
            assert!(
                matches!(got, Err(SignedError::UnknownOperation(11))),
                "{}",
                c["name"]
            );
        } else if kind == "bad_request" {
            assert!(
                matches!(got, Err(SignedError::BadRequest(_))),
                "{}",
                c["name"]
            );
        } else {
            assert_eq!(got, Err(expected(kind, &wire)), "{}", c["name"]);
        }
        n += 1;
    }
    assert!(n >= 32);
}

#[test]
fn no_single_byte_mutation_is_accepted() {
    let d = doc();
    let reg = registry(&d);
    let mut tried = 0;
    for v in d["valid"].as_array().unwrap() {
        let wire = hex(v["wire_hex"].as_str().unwrap());
        let chain: u64 = v["chain_id"].as_str().unwrap().parse().unwrap();
        // every Ed25519 vector (small) and one ML-DSA vector: no mutation yields Ok
        if suite_of(&wire) != ED25519 && !(v["name"] == "migrate_p0" && chain == 1) {
            continue;
        }
        for pos in 0..wire.len() {
            for mask in [0x01u8, 0x80] {
                let mut m = wire.clone();
                m[pos] ^= mask;
                assert!(
                    verify(&m, chain, &reg, true).is_err(),
                    "{} byte {pos}",
                    v["name"]
                );
                tried += 1;
            }
        }
    }
    assert!(tried > 5000);
}

#[test]
fn end_to_end_only_verified_requests_reach_the_machine() {
    let d = doc();
    let reg = registry(&d);
    let seed: [u8; 32] = hex(d["principals"]["2"]["seed_hex"].as_str().unwrap())
        .try_into()
        .unwrap();
    let sk = SigningKey::from_bytes(&seed);
    let pk = hex(d["principals"]["2"]["public_hex"].as_str().unwrap());
    let kid = key_id(ED25519, &pk);
    let chain = 7u64;
    let sign = |w: &WireRequest| {
        let bytes = encode(w).unwrap();
        let sig = sk.sign(&signing_message(chain, ED25519, &kid, &bytes));
        encode_wire(chain, ED25519, &bytes, &sig.to_bytes())
    };

    let mut policy = Policy::default();
    policy.controls.insert((2, 0));
    policy.limits.insert((2, Kind::Issue, 0, Some(0), 0), 1_000);
    let machine = Machine::new(Config {
        accounts: 4,
        assets: 2,
        vault: Some(3),
        deadlines: vec![],
        now: 0,
        migration: None,
        policy,
    })
    .unwrap();
    let mut node = Node {
        chain_id: chain,
        keys: reg,
        allow_deprecated: true,
        machine,
    };
    let req = |id: u8, nonce: u64, amount: u128| WireRequest {
        request_id: [id; 32],
        request: Request {
            principal: 2,
            nonce,
            op: Op::Issue {
                issuer: 0,
                recipient: 0,
                asset: 0,
                amount,
            },
        },
    };

    let w0 = sign(&req(1, 0, 10));
    assert_eq!(node.submit(&w0).unwrap().token(), "A0>1");
    assert_eq!(node.machine.ledger.balance(0, 0), 10);
    // the same wire again is a replay answered from the cache
    assert_eq!(node.submit(&w0).unwrap().token(), "RA0>1");
    assert_eq!(node.machine.ledger.balance(0, 0), 10);
    // a tampered wire never reaches the machine: no receipt, no state change
    let before = (node.machine.cached(), node.machine.snapshot());
    let mut bad = sign(&req(2, 1, 5));
    let last = bad.len() - 1;
    bad[last] ^= 1;
    assert_eq!(node.submit(&bad), Err(SignedError::BadSignature));
    assert_eq!((node.machine.cached(), node.machine.snapshot()), before);
    // a request outside the grant is authenticated but denied by the machine (cached denial)
    let denied = sign(&req(3, 1, 5_000));
    assert_eq!(node.submit(&denied).unwrap().token(), "Nia@1");
    // a signature for another chain is refused
    let mut other = Node {
        chain_id: 8,
        ..node.clone()
    };
    assert_eq!(
        other.submit(&sign(&req(4, 1, 1))),
        Err(SignedError::WrongChain)
    );
}

#[test]
fn end_to_end_resolve_is_signed_authorized_and_settles_a_dispute() {
    let d = doc();
    let reg = registry(&d);
    let seed: [u8; 32] = hex(d["principals"]["2"]["seed_hex"].as_str().unwrap())
        .try_into()
        .unwrap();
    let sk = SigningKey::from_bytes(&seed);
    let pk = hex(d["principals"]["2"]["public_hex"].as_str().unwrap());
    let kid = key_id(ED25519, &pk);
    let chain = 9u64;
    let sign = |w: &WireRequest| {
        let bytes = encode(w).unwrap();
        let sig = sk.sign(&signing_message(chain, ED25519, &kid, &bytes));
        encode_wire(chain, ED25519, &bytes, &sig.to_bytes())
    };
    let mut policy = Policy::default();
    policy.controls.insert((2, 0));
    policy.limits.insert((2, Kind::Issue, 0, Some(0), 0), 1_000);
    policy.limits.insert((2, Kind::Open, 0, Some(1), 0), 1_000);
    policy.ids.insert((2, Kind::Dispute, 0));
    policy.ids.insert((2, Kind::Resolve, 0));
    let machine = Machine::new(Config {
        accounts: 4,
        assets: 1,
        vault: Some(3),
        deadlines: vec![1_000, 1_000],
        now: 0,
        migration: None,
        policy,
    })
    .unwrap();
    let mut node = Node {
        chain_id: chain,
        keys: reg,
        allow_deprecated: true,
        machine,
    };
    let req = |id: u8, nonce: u64, op: Op| WireRequest {
        request_id: [id; 32],
        request: Request {
            principal: 2,
            nonce,
            op,
        },
    };
    let steps = [
        Op::Issue {
            issuer: 0,
            recipient: 0,
            asset: 0,
            amount: 100,
        },
        Op::Open {
            id: 0,
            depositor: 0,
            beneficiary: 1,
            asset: 0,
            amount: 40,
        },
        Op::Dispute { id: 0, claimant: 0 },
    ];
    for (i, op) in steps.into_iter().enumerate() {
        let w = sign(&req(i as u8 + 1, i as u64, op));
        assert_eq!(node.submit(&w).unwrap().token().chars().next(), Some('A'));
    }
    assert_eq!(node.machine.ledger.balance(3, 0), 40);
    let resolve = |to_beneficiary| Op::Resolve {
        id: 0,
        to_beneficiary,
    };
    let w = sign(&req(4, 3, resolve(true)));
    assert_eq!(node.submit(&w).unwrap().token(), "A3>4");
    assert_eq!(node.machine.ledger.balance(1, 0), 40);
    assert_eq!(node.machine.ledger.balance(3, 0), 0);
    assert!(node.machine.filing(0).is_none());
    assert!(node.machine.invariant());
    // the same wire is a replay; a second resolve of the same escrow is denied (no longer pending)
    assert_eq!(node.submit(&w).unwrap().token(), "RA3>4");
    let again = sign(&req(5, 4, resolve(false)));
    assert_eq!(node.submit(&again).unwrap().token(), "Nresolve:n@4");
    assert_eq!(node.machine.ledger.balance(1, 0), 40);
    // a resolve for an escrow without a grant is denied by the machine, not by the signature layer
    let ungranted = sign(&req(
        6,
        4,
        Op::Resolve {
            id: 1,
            to_beneficiary: true,
        },
    ));
    assert_eq!(node.submit(&ungranted).unwrap().token(), "Nresolve:auth@4");
}
