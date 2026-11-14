//! Property and fuzz tests for the integrated processor (`machine.rs`), independent of the
//! Python traces: 200 seeded random runs x 400 requests mixing fresh requests, exact
//! replays, same-ID conflicts, stale and future nonces, out-of-range accounts/assets and
//! extreme amounts. No external crates; a fixed PRNG keeps every run reproducible.
//!
//! Properties checked after EVERY request:
//! - holdings invariant and per-asset conservation (minted - burned = outstanding = sum of balances);
//! - `Accepted`: exactly the acting principal's nonce advances by one, one cache entry is added;
//! - `DeniedCached`: ledger and all nonces unchanged, one cache entry added;
//! - `Replay`, `RequestIdConflict`, `StaleNonce`, `FutureNonce`, `Invalid`: the whole
//!   processor is unchanged (atomicity);
//! - a replay returns exactly the response stored by the first submission of that ID;
//! - accepted nonces of one principal are consecutive from zero.
//!
//! At the end of each run: re-feeding the whole request log to a fresh processor yields an
//! identical processor (determinism).

use sirm_codec::auth::*;
use sirm_codec::ledger::*;
use sirm_codec::machine::*;
use std::collections::BTreeMap;

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
    fn chance(&mut self, percent: u64) -> bool {
        self.below(100) < percent
    }
}

const ACCOUNTS: u32 = 5;
const ASSETS: u32 = 3;
const PRINCIPALS: u32 = 4;

fn random_policy(r: &mut Rng) -> Policy {
    let mut grants = Vec::new();
    let mut control = Vec::new();
    for p in 0..PRINCIPALS {
        for a in 0..ACCOUNTS {
            if r.chance(70) {
                control.push((p, a));
            }
            for asset in 0..ASSETS {
                let limit = [0u128, 50, 1_000, 100_000, u128::MAX][r.below(5) as usize];
                if r.chance(45) {
                    grants.push(Grant {
                        principal: p,
                        scope: Scope::Burn { holder: a },
                        asset,
                        max_amount: limit,
                    });
                }
                for b in 0..ACCOUNTS {
                    let limit = [0u128, 50, 1_000, 100_000, u128::MAX][r.below(5) as usize];
                    if r.chance(35) {
                        grants.push(Grant {
                            principal: p,
                            scope: Scope::Transfer {
                                source: a,
                                destination: b,
                            },
                            asset,
                            max_amount: limit,
                        });
                    }
                    if r.chance(35) {
                        grants.push(Grant {
                            principal: p,
                            scope: Scope::Issue {
                                issuer: a,
                                recipient: b,
                            },
                            asset,
                            max_amount: limit,
                        });
                    }
                }
            }
        }
    }
    Policy::new(&grants, &control).expect("grants generated without conflicts")
}

fn amount(r: &mut Rng) -> u128 {
    match r.below(10) {
        0 => 0,
        1 => 1,
        2 => u128::MAX,
        3 => u128::MAX - r.below(3) as u128,
        4..=6 => r.below(60) as u128,
        7 | 8 => r.below(2_000) as u128,
        _ => r.below(200_000) as u128,
    }
}

fn account(r: &mut Rng) -> u32 {
    if r.chance(3) {
        ACCOUNTS + r.below(3) as u32
    } else {
        r.below(ACCOUNTS as u64) as u32
    }
}

fn asset(r: &mut Rng) -> u32 {
    if r.chance(3) {
        ASSETS + r.below(2) as u32
    } else {
        r.below(ASSETS as u64) as u32
    }
}

fn operation(r: &mut Rng) -> Operation {
    match r.below(10) {
        0..=3 => Operation::Transfer {
            source: account(r),
            destination: account(r),
            asset: asset(r),
            amount: amount(r),
        },
        4..=6 => Operation::Issue {
            issuer: account(r),
            recipient: account(r),
            asset: asset(r),
            amount: amount(r),
        },
        _ => Operation::Burn {
            holder: account(r),
            asset: asset(r),
            amount: amount(r),
        },
    }
}

fn id_bytes(n: u64) -> RequestId {
    let mut id = [0u8; 32];
    id[24..].copy_from_slice(&n.to_be_bytes());
    id
}

fn conserved(p: &Processor) -> bool {
    p.ledger.invariant()
        && (0..ASSETS).all(|s| {
            let sup = p.ledger.supply(s);
            sup.minted.checked_sub(sup.burned) == Some(sup.outstanding)
                && p.ledger.total_holdings(s) == Some(sup.outstanding)
        })
}

#[test]
fn processor_properties_hold_under_random_request_streams() {
    let mut classes: BTreeMap<&'static str, usize> = BTreeMap::new();
    for seed in 0..200u64 {
        let mut r = Rng(seed.wrapping_mul(0x1234_5678_9ABC_DEF1) ^ 0xA5A5);
        let policy = random_policy(&mut r);
        let mut p = Processor::new(Holdings::new(ACCOUNTS, ASSETS), policy.clone());
        let mut log: Vec<(RequestId, Request)> = Vec::new();
        let mut first: BTreeMap<RequestId, (Request, Stored)> = BTreeMap::new();
        let mut accepted_nonces: BTreeMap<u32, Vec<u64>> = BTreeMap::new();
        let mut next_id = 0u64;
        for step in 0..400 {
            let (id, req) = match r.below(100) {
                0..=59 => {
                    let principal = r.below(PRINCIPALS as u64) as u32;
                    next_id += 1;
                    (
                        id_bytes(next_id),
                        Request {
                            principal,
                            nonce: p.next_nonce(principal),
                            operation: operation(&mut r),
                        },
                    )
                }
                60..=74 if !log.is_empty() => log[r.below(log.len() as u64) as usize],
                75..=82 if !log.is_empty() => {
                    let (id, old) = log[r.below(log.len() as u64) as usize];
                    (
                        id,
                        Request {
                            operation: operation(&mut r),
                            ..old
                        },
                    )
                }
                83..=89 => {
                    let principal = r.below(PRINCIPALS as u64) as u32;
                    next_id += 1;
                    let cur = p.next_nonce(principal);
                    (
                        id_bytes(next_id),
                        Request {
                            principal,
                            nonce: cur.saturating_sub(1 + r.below(3)),
                            operation: operation(&mut r),
                        },
                    )
                }
                _ => {
                    let principal = r.below(PRINCIPALS as u64) as u32;
                    next_id += 1;
                    (
                        id_bytes(next_id),
                        Request {
                            principal,
                            nonce: p.next_nonce(principal) + 1 + r.below(3),
                            operation: operation(&mut r),
                        },
                    )
                }
            };
            let before = p.clone();
            let out = p.process(id, req);
            log.push((id, req));
            assert!(
                conserved(&p),
                "seed {seed} step {step}: conservation broken after {out:?}"
            );
            let nonces_equal = (0..PRINCIPALS).all(|q| p.next_nonce(q) == before.next_nonce(q));
            match out {
                Outcome::Accepted(stored) => {
                    classes
                        .entry("accepted")
                        .and_modify(|c| *c += 1)
                        .or_insert(1);
                    assert_eq!(p.cached(), before.cached() + 1, "seed {seed} step {step}");
                    assert_eq!(
                        p.next_nonce(req.principal),
                        before.next_nonce(req.principal) + 1
                    );
                    for q in (0..PRINCIPALS).filter(|&q| q != req.principal) {
                        assert_eq!(
                            p.next_nonce(q),
                            before.next_nonce(q),
                            "other principal's nonce moved"
                        );
                    }
                    match stored {
                        Stored::Accepted {
                            accepted_nonce,
                            next_nonce,
                        } => {
                            assert_eq!((accepted_nonce, next_nonce), (req.nonce, req.nonce + 1));
                        }
                        other => panic!("accepted outcome stored {other:?}"),
                    }
                    let seen = accepted_nonces.entry(req.principal).or_default();
                    assert_eq!(
                        seen.len() as u64,
                        req.nonce,
                        "accepted nonces must be consecutive"
                    );
                    seen.push(req.nonce);
                    assert!(first.insert(id, (req, stored)).is_none());
                }
                Outcome::DeniedCached(stored) => {
                    classes.entry("denied").and_modify(|c| *c += 1).or_insert(1);
                    assert_eq!(p.cached(), before.cached() + 1);
                    assert!(nonces_equal, "a denial consumed a nonce");
                    assert_eq!(p.ledger, before.ledger, "a denial changed the ledger");
                    assert!(first.insert(id, (req, stored)).is_none());
                }
                Outcome::Replay(stored) => {
                    classes.entry("replay").and_modify(|c| *c += 1).or_insert(1);
                    assert_eq!(p, before, "a replay changed state");
                    let (orig, orig_stored) = first[&id];
                    assert_eq!(orig, req);
                    assert_eq!(
                        orig_stored, stored,
                        "replay must return the stored response"
                    );
                }
                Outcome::RequestIdConflict => {
                    classes
                        .entry("conflict")
                        .and_modify(|c| *c += 1)
                        .or_insert(1);
                    assert_eq!(p, before, "a conflict changed state");
                    assert_ne!(first[&id].0, req);
                }
                Outcome::StaleNonce => {
                    classes.entry("stale").and_modify(|c| *c += 1).or_insert(1);
                    assert_eq!(p, before);
                    assert!(req.nonce < before.next_nonce(req.principal));
                }
                Outcome::FutureNonce => {
                    classes.entry("future").and_modify(|c| *c += 1).or_insert(1);
                    assert_eq!(p, before);
                    assert!(req.nonce > before.next_nonce(req.principal));
                }
                Outcome::Invalid(_) => {
                    classes
                        .entry("invalid")
                        .and_modify(|c| *c += 1)
                        .or_insert(1);
                    assert_eq!(p, before, "an invalid request wrote state");
                }
            }
        }
        // Determinism: the same request log replayed into a fresh processor gives the same state.
        let mut again = Processor::new(Holdings::new(ACCOUNTS, ASSETS), policy);
        for &(id, req) in &log {
            again.process(id, req);
        }
        assert_eq!(
            again, p,
            "seed {seed}: replaying the log is not deterministic"
        );
    }
    for class in [
        "accepted", "denied", "replay", "conflict", "stale", "future",
    ] {
        assert!(
            classes.get(class).copied().unwrap_or(0) > 500,
            "weak coverage of {class}: {classes:?}"
        );
    }
    // Ledger-range and overflow failures are rare by construction (out-of-range IDs, u128::MAX).
    assert!(
        classes.get("invalid").copied().unwrap_or(0) > 50,
        "weak coverage of invalid: {classes:?}"
    );
}
