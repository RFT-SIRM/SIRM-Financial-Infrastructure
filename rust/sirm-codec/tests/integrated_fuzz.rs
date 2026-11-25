//! Adversarial stress test of `integrated::Machine::process` (checked by SIRM).
//!
//! Deterministic pseudo-random machines and requests, including boundary amounts (`0`, `1`,
//! `u128::MAX - 1`, `u128::MAX`), accounts, assets and escrow ids outside the configured ranges, stale,
//! future and maximal nonces, and repeated request ids (replay and conflict). After every request:
//! `process` did not panic; `Machine::invariant` holds (conservation, vault backing, the migration
//! equation, every filing has a record); a replay, conflict, stale, future or denied request left the whole
//! state (without the response cache) unchanged; an accepted request advanced the nonce of its principal by
//! exactly one and no other nonce. The seeds are fixed, so a failure reproduces.

use sirm_codec::integrated::{
    Config, Kind, Machine, MigrationConfig, Op, Outcome, Policy, Request, Stored,
};

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        // xorshift64*
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
        const EDGE: [u128; 9] = [
            0,
            1,
            2,
            3,
            10,
            1000,
            u128::MAX / 2,
            u128::MAX - 1,
            u128::MAX,
        ];
        match self.below(4) {
            0 => EDGE[self.below(EDGE.len() as u64) as usize],
            1 => self.below(5) as u128,
            2 => self.below(2000) as u128,
            _ => ((self.next() as u128) << 64) | self.next() as u128,
        }
    }
}

/// Mostly generous limits, so that a large share of requests is authorised; the rest are edge values.
fn limit(rng: &mut Rng) -> u128 {
    match rng.below(10) {
        0..=4 => u128::MAX,
        5..=7 => 1000,
        _ => rng.amount(),
    }
}

const KINDS: [Kind; 11] = [
    Kind::Transfer,
    Kind::Issue,
    Kind::Burn,
    Kind::Open,
    Kind::Release,
    Kind::Cancel,
    Kind::Expire,
    Kind::Dispute,
    Kind::Advance,
    Kind::Migrate,
    Kind::Resolve,
];

fn build(rng: &mut Rng) -> Machine {
    let accounts = 4 + rng.below(4) as u32;
    let assets = 2 + rng.below(3) as u32;
    let vault = if rng.below(8) == 0 {
        None
    } else {
        Some(accounts - 1)
    };
    let deadlines: Vec<u64> = (0..rng.below(6)).map(|_| rng.below(20)).collect();
    let mut policy = Policy::default();
    let principals = accounts + 1;
    for p in 0..principals {
        policy.controls.insert((p, p));
        for _ in 0..rng.below(3) {
            policy
                .controls
                .insert((p, rng.below(accounts as u64) as u32));
        }
        if rng.below(3) == 0 {
            policy.clock.insert(p);
        }
        for id in 0..(deadlines.len() + 1) {
            for k in [
                Kind::Release,
                Kind::Cancel,
                Kind::Expire,
                Kind::Dispute,
                Kind::Resolve,
            ] {
                if rng.below(2) == 0 {
                    policy.ids.insert((p, k, id));
                }
            }
        }
        for a in 0..accounts {
            for asset in 0..assets {
                for b in 0..accounts {
                    for k in [Kind::Transfer, Kind::Issue, Kind::Open, Kind::Migrate] {
                        if rng.below(2) == 0 {
                            let limit = limit(rng);
                            policy.limits.insert((p, k, a, Some(b), asset), limit);
                        }
                    }
                }
                if rng.below(2) == 0 {
                    let limit = limit(rng);
                    policy.limits.insert((p, Kind::Burn, a, None, asset), limit);
                }
            }
        }
    }
    let migration = if rng.below(4) == 0 {
        None
    } else {
        let src = rng.below(assets as u64) as u32;
        let dst = (src + 1 + rng.below(assets as u64 - 1) as u32) % assets;
        let pick = |rng: &mut Rng| loop {
            let a = rng.below(accounts as u64) as u32;
            if Some(a) != vault {
                return a;
            }
        };
        let holder = pick(rng);
        let recipient = pick(rng);
        let nz = |rng: &mut Rng| loop {
            let v = rng.amount();
            if v != 0 {
                return v;
            }
        };
        Some(MigrationConfig {
            holder,
            recipient,
            src,
            dst,
            num: nz(rng),
            den: nz(rng),
        })
    };
    Machine::new(Config {
        accounts,
        assets,
        vault,
        deadlines,
        now: rng.below(10),
        migration,
        policy,
    })
    .expect("generated configuration is valid")
}

fn op(rng: &mut Rng, accounts: u32, assets: u32, ids: usize, principal: u32) -> Op {
    // Friendly requests (about 70 percent): in-range accounts and assets, the principal on its own account,
    // small amounts. The rest are hostile: out-of-range accounts and assets, boundary amounts.
    let friendly = rng.below(10) < 7;
    let own = principal.min(accounts - 1);
    let acct = |rng: &mut Rng| {
        if friendly {
            rng.below(accounts as u64) as u32
        } else {
            rng.below(accounts as u64 + 2) as u32
        }
    };
    let asset = |rng: &mut Rng| {
        if friendly {
            rng.below(assets as u64) as u32
        } else {
            rng.below(assets as u64 + 1) as u32
        }
    };
    let amount = |rng: &mut Rng| {
        if friendly {
            rng.below(60) as u128
        } else {
            rng.amount()
        }
    };
    let id = |rng: &mut Rng| match rng.below(10) {
        0 => usize::MAX,
        1 => ids + 5,
        _ => rng.below(ids as u64 + 1) as usize,
    };
    match KINDS[rng.below(KINDS.len() as u64) as usize] {
        Kind::Transfer => Op::Transfer {
            src: if friendly { own } else { acct(rng) },
            dst: acct(rng),
            asset: asset(rng),
            amount: amount(rng),
        },
        Kind::Issue => Op::Issue {
            issuer: if friendly { own } else { acct(rng) },
            recipient: acct(rng),
            asset: asset(rng),
            amount: amount(rng),
        },
        Kind::Burn => Op::Burn {
            holder: if friendly { own } else { acct(rng) },
            asset: asset(rng),
            amount: amount(rng),
        },
        Kind::Open => Op::Open {
            id: id(rng),
            depositor: if friendly { own } else { acct(rng) },
            beneficiary: acct(rng),
            asset: asset(rng),
            amount: amount(rng),
        },
        Kind::Release => Op::Release(id(rng)),
        Kind::Cancel => Op::Cancel(id(rng)),
        Kind::Expire => Op::Expire(id(rng)),
        Kind::Dispute => Op::Dispute {
            id: id(rng),
            claimant: if friendly { own } else { acct(rng) },
        },
        Kind::Advance => Op::Advance(match rng.below(4) {
            0 => u64::MAX,
            1 => rng.below(4),
            _ => rng.below(40),
        }),
        Kind::Migrate => Op::Migrate(amount(rng)),
        Kind::Resolve => Op::Resolve {
            id: id(rng),
            to_beneficiary: rng.below(2) == 0,
        },
    }
}

fn run(seed: u64, steps: usize) -> (usize, usize) {
    let mut rng = Rng(seed | 1);
    let mut m = build(&mut rng);
    let accounts = m.config().accounts;
    let assets = m.config().assets;
    let ids = m.config().deadlines.len();
    let mut history: Vec<[u8; 32]> = Vec::new();
    let (mut accepted, mut denied) = (0usize, 0usize);
    for step in 0..steps {
        let principal = rng.below(accounts as u64 + 1) as u32;
        let expected = m.nonce(principal);
        let nonce = match rng.below(20) {
            0 => expected.wrapping_add(1),
            1 => expected.saturating_sub(1),
            2 => u64::MAX,
            3 => rng.next(),
            _ => expected,
        };
        let req = Request {
            principal,
            nonce,
            op: op(&mut rng, accounts, assets, ids, principal),
        };
        let id = if !history.is_empty() && rng.below(10) < 3 {
            history[rng.below(history.len() as u64) as usize]
        } else {
            let mut id = [0u8; 32];
            for chunk in id.chunks_mut(8) {
                chunk.copy_from_slice(&rng.next().to_be_bytes());
            }
            history.push(id);
            id
        };
        let before = m.snapshot();
        let nonces_before = m.nonces().clone();
        let out = m.process(id, req);
        let context = format!("seed {seed} step {step} request {req:?} outcome {out:?}");
        assert!(m.invariant(), "invariant broken: {context}");
        assert!(m.now() >= before.now, "the clock went backwards: {context}");
        match out {
            Outcome::Replay(_) | Outcome::Conflict | Outcome::Stale | Outcome::Future => {
                assert_eq!(
                    m.snapshot(),
                    before,
                    "a non-executing outcome changed the state: {context}"
                );
            }
            Outcome::Done(Stored::Denied { expected_nonce, .. }) => {
                denied += 1;
                assert_eq!(expected_nonce, expected, "{context}");
                assert_eq!(
                    m.snapshot(),
                    before,
                    "a denial changed the state: {context}"
                );
            }
            Outcome::Done(Stored::Accepted {
                nonce: accepted_nonce,
            }) => {
                accepted += 1;
                assert_eq!(accepted_nonce, expected, "{context}");
                assert_eq!(
                    m.nonce(principal),
                    expected + 1,
                    "nonce did not advance by one: {context}"
                );
                for (p, n) in m.nonces() {
                    if *p != principal {
                        assert_eq!(
                            nonces_before.get(p),
                            Some(n),
                            "another nonce changed: {context}"
                        );
                    }
                }
            }
        }
    }
    (accepted, denied)
}

#[test]
fn adversarial_requests_never_panic_and_keep_the_invariants() {
    let (mut accepted, mut denied, mut machines) = (0usize, 0usize, 0usize);
    // 60 seeds in CI; `SIRM_FUZZ_SEEDS=3000` runs the extended search (9 million requests).
    let seeds: u64 = std::env::var("SIRM_FUZZ_SEEDS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(60);
    for seed in 1..=seeds {
        let (a, d) = run(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15), 3000);
        accepted += a;
        denied += d;
        machines += 1;
    }
    // The generator must actually reach both the accepting and the denying paths.
    assert!(
        accepted > 1000,
        "too few accepted requests ({accepted}): the test would prove little"
    );
    assert!(
        denied > 1000,
        "too few denied requests ({denied}): the test would prove little"
    );
    println!("machines {machines}, accepted {accepted}, denied {denied}");
}
