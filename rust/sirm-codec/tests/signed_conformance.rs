//! Conformance of the Rust signed-request layer with the Python reference vectors
//! (`engineering/canonical_encoding/results/signed_request_vectors_v0.json`). Signatures
//! come from two independent Ed25519 implementations (OpenSSL via Python, ed25519-dalek):
//! Ed25519 is deterministic, so signing the same message with the same seed must give the
//! same bytes. Also: RFC 8032 vector 1, rejection of every single-byte mutation, structured
//! negatives, and an end-to-end node that only lets verified requests reach the processor.

use ed25519_dalek::{Signer, SigningKey};
use serde_json::Value;
use sirm_codec::auth::*;
use sirm_codec::ledger::*;
use sirm_codec::machine::{Outcome, Processor};
use sirm_codec::signed::*;
use sirm_codec::{Op, Request};

fn hex(s: &str) -> Vec<u8> {
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

fn doc() -> Value {
    serde_json::from_str(include_str!(
        "../../../engineering/canonical_encoding/results/signed_request_vectors_v0.json"
    ))
    .unwrap()
}

fn request(v: &Value) -> Request {
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
    Request {
        request_id: hex(v["request_id"].as_str().unwrap()).try_into().unwrap(),
        principal: v["principal"].as_u64().unwrap() as u32,
        nonce: v["nonce"].as_str().unwrap().parse().unwrap(),
        op,
    }
}

fn registry(d: &Value) -> (KeyRegistry, Vec<SigningKey>) {
    let mut keys = KeyRegistry::new();
    let mut signers = Vec::new();
    for k in d["test_keys"].as_array().unwrap() {
        let seed: [u8; 32] = hex(k["seed_hex"].as_str().unwrap()).try_into().unwrap();
        let sk = SigningKey::from_bytes(&seed);
        let public: [u8; 32] = hex(k["public_hex"].as_str().unwrap()).try_into().unwrap();
        assert_eq!(
            sk.verifying_key().to_bytes(),
            public,
            "public key derivation"
        );
        keys.insert(k["principal"].as_u64().unwrap() as u32, public)
            .unwrap();
        signers.push(sk);
    }
    (keys, signers)
}

fn sign(sk: &SigningKey, chain: u64, r: &Request) -> [u8; 64] {
    sk.sign(&signing_message(chain, r)).to_bytes()
}

#[test]
fn rfc8032_vector_and_reference_vectors_agree_with_dalek() {
    let rfc = SigningKey::from_bytes(
        &hex("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60")
            .try_into()
            .unwrap(),
    );
    assert_eq!(
        rfc.verifying_key().to_bytes().to_vec(),
        hex("d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a")
    );
    assert_eq!(
        rfc.sign(b"").to_bytes().to_vec(),
        hex(
            &("e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e06522490155".to_string()
                + "5fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b")
        )
    );
    let d = doc();
    let (keys, signers) = registry(&d);
    let vs = d["vectors"].as_array().unwrap();
    assert_eq!(vs.len(), 8);
    for v in vs {
        let name = v["name"].as_str().unwrap();
        let (chain, r) = (
            v["chain_id"].as_str().unwrap().parse::<u64>().unwrap(),
            request(v),
        );
        assert_eq!(
            signing_message(chain, &r),
            hex(v["signing_message_hex"].as_str().unwrap()),
            "{name}"
        );
        let sig = sign(&signers[r.principal as usize], chain, &r);
        assert_eq!(
            sig.to_vec(),
            hex(v["signature_hex"].as_str().unwrap()),
            "{name}: dalek vs OpenSSL"
        );
        let wire = encode_wire(chain, &r, &sig);
        assert_eq!(wire, hex(v["wire_hex"].as_str().unwrap()), "{name}");
        assert_eq!(wire.len() as u64, v["length"].as_u64().unwrap());
        assert_eq!(verify(&wire, chain, &keys), Ok(r), "{name}");
    }
}

#[test]
fn every_single_byte_mutation_of_every_vector_is_rejected() {
    let d = doc();
    let (keys, _) = registry(&d);
    let mut tried = 0;
    for v in d["vectors"].as_array().unwrap() {
        let chain = v["chain_id"].as_str().unwrap().parse::<u64>().unwrap();
        let wire = hex(v["wire_hex"].as_str().unwrap());
        for pos in 0..wire.len() {
            for mask in [0x01u8, 0x80] {
                let mut m = wire.clone();
                m[pos] ^= mask;
                assert!(
                    verify(&m, chain, &keys).is_err(),
                    "{} accepted a mutation at byte {pos}",
                    v["name"]
                );
                tried += 1;
            }
        }
    }
    assert!(tried > 2500, "{tried}");
}

#[test]
fn structured_negatives_report_the_expected_reason() {
    let d = doc();
    let (keys, signers) = registry(&d);
    let v = &d["vectors"][0];
    let r = request(v);
    let chain = 1u64;
    let good = encode_wire(chain, &r, &sign(&signers[r.principal as usize], chain, &r));
    assert_eq!(verify(&good, chain, &keys), Ok(r.clone()));
    assert_eq!(verify(&good, 2, &keys), Err(SignedError::WrongChain));
    assert_eq!(
        verify(&good[..good.len() - 1], chain, &keys),
        Err(SignedError::Truncated)
    );
    let mut t = good.clone();
    t.push(0);
    assert_eq!(verify(&t, chain, &keys), Err(SignedError::TrailingBytes));
    let mut b = good.clone();
    b[0] = b'X';
    assert_eq!(verify(&b, chain, &keys), Err(SignedError::BadDomain));
    // a signature by another principal's key
    let other = encode_wire(chain, &r, &sign(&signers[0], chain, &r));
    assert_eq!(verify(&other, chain, &keys), Err(SignedError::BadSignature));
    // principal without a registered key
    let mut only0 = KeyRegistry::new();
    only0
        .insert(0, signers[0].verifying_key().to_bytes())
        .unwrap();
    assert_eq!(
        verify(&good, chain, &only0),
        Err(SignedError::UnknownPrincipal)
    );
    // non-canonical S (S + L): malleability must not verify
    let mut mall = good.clone();
    let n = mall.len();
    let l: [u8; 32] = hex("edd3f55c1a631258d69cf7a2def9de1400000000000000000000000000000010")
        .try_into()
        .unwrap();
    let mut carry = 0u16;
    for i in 0..32 {
        let s = mall[n - 32 + i] as u16 + l[i] as u16 + carry;
        mall[n - 32 + i] = s as u8;
        carry = s >> 8;
    }
    assert_eq!(verify(&mall, chain, &keys), Err(SignedError::BadSignature));
    // a signature over the bare request encoding (no domain, no chain) is not accepted
    let bare = signers[r.principal as usize]
        .sign(&sirm_codec::encode(&r))
        .to_bytes();
    assert_eq!(
        verify(&encode_wire(chain, &r, &bare), chain, &keys),
        Err(SignedError::BadSignature)
    );
    // a signature made for another chain is not accepted
    let cross = encode_wire(chain, &r, &sign(&signers[r.principal as usize], 2, &r));
    assert_eq!(verify(&cross, chain, &keys), Err(SignedError::BadSignature));
    // invalid public keys cannot be registered
    let mut k = KeyRegistry::new();
    // about half of all y values are not on the curve; scan small ones for such an encoding
    let rejected = (2u8..40).any(|y| {
        let mut b = [0u8; 32];
        b[0] = y;
        k.insert(0, b).is_err()
    });
    assert!(
        rejected,
        "no off-curve key encoding found among small y values"
    );
}

#[test]
fn only_verified_requests_reach_the_processor() {
    let d = doc();
    let (keys, signers) = registry(&d);
    let mut grants = Vec::new();
    for a in 0..4u32 {
        for p in 0..3u32 {
            grants.push(Grant {
                principal: p,
                scope: Scope::Burn { holder: a },
                asset: 0,
                max_amount: 1_000,
            });
            for b in 0..4u32 {
                grants.push(Grant {
                    principal: p,
                    scope: Scope::Transfer {
                        source: a,
                        destination: b,
                    },
                    asset: 0,
                    max_amount: 1_000,
                });
                grants.push(Grant {
                    principal: p,
                    scope: Scope::Issue {
                        issuer: a,
                        recipient: b,
                    },
                    asset: 0,
                    max_amount: 1_000,
                });
            }
        }
    }
    let control: Vec<(u32, u32)> = (0..3).flat_map(|p| (0..4).map(move |a| (p, a))).collect();
    let policy = Policy::new(&grants, &control).unwrap();
    let chain = 7u64;
    let mut node = Node {
        chain_id: chain,
        keys,
        processor: Processor::new(Holdings::new(4, 1), policy),
    };
    let (mut ok, mut rejected, mut replay) = (0, 0, 0);
    let mut x: u64 = 0x1234_5678_9ABC_DEF1;
    for i in 0..400u64 {
        x = x
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let k = (x >> 33) as u32;
        let principal = k % 3;
        let (a, b, amt) = ((k >> 2) % 4, (k >> 5) % 4, ((k >> 8) % 1_200) as u128);
        let op = match k % 5 {
            0 | 1 => Op::Issue {
                issuer: a,
                recipient: b,
                asset: 0,
                amount: amt,
            },
            2 | 3 => Op::Transfer {
                source: a,
                destination: b,
                asset: 0,
                amount: amt,
            },
            _ => Op::Burn {
                holder: a,
                asset: 0,
                amount: amt,
            },
        };
        let mut id = [0u8; 32];
        id[24..].copy_from_slice(&i.to_be_bytes());
        let req = Request {
            request_id: id,
            principal,
            nonce: node.processor.next_nonce(principal),
            op,
        };
        let wire = encode_wire(
            chain,
            &req,
            &sign(&signers[principal as usize], chain, &req),
        );
        // forged variants never change the processor
        let before = node.processor.clone();
        let mut mutated = wire.clone();
        let pos = (k as usize) % mutated.len();
        mutated[pos] ^= 1 << (k % 8);
        assert!(
            node.submit(&mutated).is_err(),
            "mutated wire accepted at {pos}"
        );
        let foreign = encode_wire(
            chain,
            &req,
            &sign(&signers[((principal + 1) % 3) as usize], chain, &req),
        );
        assert_eq!(node.submit(&foreign), Err(SignedError::BadSignature));
        let other_chain = encode_wire(
            chain + 1,
            &req,
            &sign(&signers[principal as usize], chain + 1, &req),
        );
        assert_eq!(node.submit(&other_chain), Err(SignedError::WrongChain));
        assert_eq!(
            node.processor, before,
            "a rejected wire message changed the processor"
        );
        rejected += 3;
        // the genuine message goes through, and an exact retry is a replay
        match node.submit(&wire).expect("genuine message verifies") {
            Outcome::Accepted(_) | Outcome::DeniedCached(_) => ok += 1,
            Outcome::Invalid(_) => {}
            o => panic!("unexpected {o:?}"),
        }
        if let Ok(Outcome::Replay(_)) = node.submit(&wire) {
            replay += 1;
        }
    }
    assert!(
        ok > 300 && replay > 300 && rejected == 1200,
        "{ok}/{replay}/{rejected}"
    );
}
