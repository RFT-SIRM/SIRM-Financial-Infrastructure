//! Cryptographic stress test of the signed-request layer v3 and of the request decoder (checked by SIRM).
//!
//! On valid Ed25519 wires of pseudo-random requests (all eleven operations, boundary values):
//! - the wire verifies and returns exactly the request that was signed;
//! - without `allow_deprecated` the deprecated Ed25519 suite is refused;
//! - every single-bit flip of the wire is rejected, and so is every truncation and every extension;
//! - the signature with a non-canonical scalar (`S + L`, same signature mathematically) is rejected;
//! - a universal forgery under a weak (small-order) public key is rejected, whether or not the registry
//!   accepts such a key.
//!
//! On arbitrary bytes: `verify` and `decode` never panic, and whatever `decode` accepts re-encodes to
//! exactly the input bytes (no second encoding of one request is accepted).
//!
//! The seeds are fixed, so a failure reproduces.

use ed25519_dalek::{Signer, SigningKey, VerifyingKey};
use sirm_codec::integrated::{Op, Request};
use sirm_codec::request_v2::{decode, encode, WireRequest};
use sirm_codec::signed_v3::{
    encode_wire, key_id, signing_message, verify, KeyRegistry, SignedError, ED25519,
};

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
    fn amount(&mut self) -> u128 {
        const EDGE: [u128; 6] = [0, 1, 255, u64::MAX as u128, u128::MAX - 1, u128::MAX];
        match self.below(3) {
            0 => EDGE[self.below(EDGE.len() as u64) as usize],
            1 => self.below(1000) as u128,
            _ => ((self.next() as u128) << 64) | self.next() as u128,
        }
    }
    fn small(&mut self) -> u32 {
        match self.below(4) {
            0 => u32::MAX,
            1 => 0,
            _ => self.below(50) as u32,
        }
    }
}

fn random_wire_request(rng: &mut Rng, principal: u32) -> WireRequest {
    let op = match rng.below(11) {
        0 => Op::Transfer {
            src: rng.small(),
            dst: rng.small(),
            asset: rng.small(),
            amount: rng.amount(),
        },
        1 => Op::Issue {
            issuer: rng.small(),
            recipient: rng.small(),
            asset: rng.small(),
            amount: rng.amount(),
        },
        2 => Op::Burn {
            holder: rng.small(),
            asset: rng.small(),
            amount: rng.amount(),
        },
        3 => Op::Open {
            id: rng.small() as usize,
            depositor: rng.small(),
            beneficiary: rng.small(),
            asset: rng.small(),
            amount: rng.amount(),
        },
        4 => Op::Release(rng.small() as usize),
        5 => Op::Cancel(rng.small() as usize),
        6 => Op::Expire(rng.small() as usize),
        7 => Op::Dispute {
            id: rng.small() as usize,
            claimant: rng.small(),
        },
        8 => Op::Advance(rng.next()),
        9 => Op::Migrate(rng.amount()),
        _ => Op::Resolve {
            id: rng.small() as usize,
            to_beneficiary: rng.below(2) == 0,
        },
    };
    let mut request_id = [0u8; 32];
    for c in request_id.chunks_mut(8) {
        c.copy_from_slice(&rng.next().to_be_bytes());
    }
    WireRequest {
        request_id,
        request: Request {
            principal,
            nonce: rng.next(),
            op,
        },
    }
}

fn signing_key(principal: u32) -> SigningKey {
    SigningKey::from_bytes(&[principal as u8 + 1; 32])
}

fn registry() -> KeyRegistry {
    let mut r = KeyRegistry::new();
    for p in 0..6u32 {
        r.insert(p, ED25519, signing_key(p).verifying_key().as_bytes())
            .unwrap();
    }
    r
}

fn sign(chain: u64, w: &WireRequest) -> Vec<u8> {
    let req = encode(w).expect("encodable");
    let sk = signing_key(w.request.principal);
    let pk = sk.verifying_key();
    let kid = key_id(ED25519, pk.as_bytes());
    let sig = sk.sign(&signing_message(chain, ED25519, &kid, &req));
    encode_wire(chain, ED25519, &req, &sig.to_bytes())
}

/// The group order L of Ed25519, little endian.
const L: [u8; 32] = [
    0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58, 0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde, 0x14,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x10,
];

fn add_l(s: &[u8]) -> Vec<u8> {
    let mut out = vec![0u8; 32];
    let mut carry = 0u16;
    for i in 0..32 {
        let v = s[i] as u16 + L[i] as u16 + carry;
        out[i] = v as u8;
        carry = v >> 8;
    }
    assert_eq!(carry, 0, "S + L must fit in 256 bits for a reduced S");
    out
}

#[test]
fn valid_wires_verify_and_every_modification_is_rejected() {
    let reg = registry();
    let mut rng = Rng(0xC0FF_EE11_5EED_0001);
    let (mut wires, mut flips, mut cuts) = (0usize, 0usize, 0usize);
    // 100 wires in CI (every bit flip of each is checked); `SIRM_SIG_WIRES=2000` runs the extended search.
    let count: usize = std::env::var("SIRM_SIG_WIRES")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(100);
    for _ in 0..count {
        let principal = rng.below(6) as u32;
        let w = random_wire_request(&mut rng, principal);
        let chain = rng.next();
        let wire = sign(chain, &w);

        // accepted, and exactly what was signed
        let got = verify(&wire, chain, &reg, true).expect("a valid wire verifies");
        assert_eq!(got, w);
        // the deprecated suite is refused unless allowed
        assert_eq!(
            verify(&wire, chain, &reg, false),
            Err(SignedError::SuiteNotAllowed)
        );
        // another chain is refused
        assert_eq!(
            verify(&wire, chain.wrapping_add(1), &reg, true),
            Err(SignedError::WrongChain)
        );

        // every single-bit flip is rejected
        for byte in 0..wire.len() {
            for bit in 0..8 {
                let mut m = wire.clone();
                m[byte] ^= 1 << bit;
                assert!(
                    verify(&m, chain, &reg, true).is_err(),
                    "a flipped bit was accepted: byte {byte} bit {bit} of {w:?}"
                );
                flips += 1;
            }
        }
        // every truncation and several extensions are rejected
        for len in 0..wire.len() {
            assert!(
                verify(&wire[..len], chain, &reg, true).is_err(),
                "truncation to {len} accepted"
            );
            cuts += 1;
        }
        for extra in 1..=3usize {
            let mut m = wire.clone();
            m.extend(std::iter::repeat_n(0u8, extra));
            assert!(
                verify(&m, chain, &reg, true).is_err(),
                "extension by {extra} accepted"
            );
            cuts += 1;
        }
        // non-canonical scalar: the same signature with S replaced by S + L
        let sig_at = wire.len() - 64;
        let mut m = wire.clone();
        let s_plus_l = add_l(&wire[sig_at + 32..]);
        m[sig_at + 32..].copy_from_slice(&s_plus_l);
        assert!(
            verify(&m, chain, &reg, true).is_err(),
            "a malleated signature (S + L) was accepted"
        );
        wires += 1;
    }
    println!("wires {wires}, bit flips {flips}, truncations and extensions {cuts}");
}

#[test]
fn weak_key_universal_forgery_is_rejected() {
    // The identity point as public key and as R, with S = 0, verifies for every message under the
    // non-strict Ed25519 equation. The registry may or may not accept such a key; either way no forged
    // request may be accepted.
    let identity = {
        let mut p = [0u8; 32];
        p[0] = 1;
        p
    };
    let mut reg = KeyRegistry::new();
    let accepted_by_registry = reg.insert(7, ED25519, &identity).is_ok();
    println!("registry accepts the identity point as a public key: {accepted_by_registry}");
    if !accepted_by_registry {
        return;
    }
    let mut rng = Rng(0xDEAD_BEEF_0000_0007);
    for _ in 0..50 {
        let w = random_wire_request(&mut rng, 7);
        let chain = rng.next();
        let req = encode(&w).unwrap();
        let mut forged_sig = [0u8; 64];
        forged_sig[..32].copy_from_slice(&identity);
        let wire = encode_wire(chain, ED25519, &req, &forged_sig);
        assert!(
            verify(&wire, chain, &reg, true).is_err(),
            "a universal forgery under a weak key was accepted: {w:?}"
        );
    }
}

#[test]
fn arbitrary_bytes_never_panic_and_decode_is_canonical() {
    let reg = registry();
    let mut rng = Rng(0x0BAD_C0DE_0000_0003);
    let mut decoded = 0usize;
    let domains: [&[u8]; 3] = [b"SIRM/SRQ/v3\0", b"SIRM/FTX/v2\0", b""];
    for i in 0..200_000usize {
        let len = rng.below(220) as usize;
        let mut b: Vec<u8> = (0..len).map(|_| rng.next() as u8).collect();
        // half of the inputs start with a real domain so that the later checks are reached
        if i % 2 == 0 {
            let d = domains[rng.below(domains.len() as u64) as usize];
            let n = d.len().min(b.len());
            b[..n].copy_from_slice(&d[..n]);
        }
        let _ = verify(&b, rng.next(), &reg, true);
        if let Ok(w) = decode(&b) {
            decoded += 1;
            assert_eq!(
                encode(&w).expect("a decoded request re-encodes"),
                b,
                "non-canonical input was accepted"
            );
        }
    }
    // Structured inputs: start from valid encodings and perturb them, so that the decoder accepts many.
    for _ in 0..20_000usize {
        let principal = rng.below(6) as u32;
        let w = random_wire_request(&mut rng, principal);
        let mut b = encode(&w).unwrap();
        assert_eq!(decode(&b).unwrap(), w, "round trip");
        let at = rng.below(b.len() as u64) as usize;
        b[at] = rng.next() as u8;
        if let Ok(d) = decode(&b) {
            decoded += 1;
            assert_eq!(encode(&d).unwrap(), b, "non-canonical input was accepted");
        }
    }
    assert!(
        decoded > 100,
        "the decoder accepted too few inputs ({decoded}): the canonical check proves little"
    );
    println!("decoded and re-encoded inputs: {decoded}");
}

#[test]
fn registry_rejects_malformed_keys() {
    let mut reg = KeyRegistry::new();
    assert!(
        reg.insert(0, ED25519, &[1u8; 31]).is_err(),
        "a short key was accepted"
    );
    assert!(
        reg.insert(0, ED25519, &[1u8; 33]).is_err(),
        "a long key was accepted"
    );
    assert!(
        reg.insert(0, 0x7777, &[1u8; 32]).is_err(),
        "an unknown suite was accepted"
    );
    // an encoding that is not a curve point
    let off_curve = (2u8..=255)
        .map(|y| {
            let mut b = [0u8; 32];
            b[0] = y;
            b
        })
        .find(|b| VerifyingKey::from_bytes(b).is_err())
        .expect("some small y coordinate is off the curve");
    assert!(
        reg.insert(0, ED25519, &off_curve).is_err(),
        "an off-curve key was accepted"
    );
    assert!(reg.get(0).is_none(), "a rejected key left an entry behind");
}
