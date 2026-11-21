//! Differential check of the `u128` ceiling against the Lean model `SIRM/BoundedAmounts.lean`.
//!
//! The Lean predicate `fitsB` is re-implemented here independently of the machine, with checked
//! arithmetic, and compared with what `integrated::Machine` does on seeded random runs that push
//! supply counters, migration totals and the carried remainder towards `u128::MAX`.
//!
//! For every authorized issue and every authorized migration with `0 < amount <= balance`:
//! the machine accepts exactly when `fitsB` holds; a denial for overflow never happens when
//! `fitsB` holds (so the extra balance checks of the machine are redundant on reachable states, as
//! conservation implies); a denied request changes nothing; the machine invariant holds after every
//! request. This is differential evidence on the stated runs, not a refinement proof, and it only
//! covers the conditions that `fitsB` states (not the clock or ids).

use sirm_codec::integrated::*;

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
    fn wide(&mut self) -> u128 {
        ((self.next() as u128) << 64) | self.next() as u128
    }
}

const MAX: u128 = u128::MAX;
const VAULT: u32 = 3;

fn extreme(r: &mut Rng) -> u128 {
    match r.below(12) {
        0 => 0,
        1 => 1,
        2 => 2,
        3 => 7,
        4 => MAX,
        5 => MAX - 1,
        6 => MAX / 2,
        7 => MAX / 2 + 1,
        8 => 1u128 << 64,
        9 => MAX - r.below(1000) as u128,
        10 => r.wide() >> r.below(128),
        _ => r.wide(),
    }
}

fn config(m: Option<MigrationConfig>) -> Config {
    let mut p = Policy::default();
    for a in 0..3 {
        p.controls.insert((0, a));
    }
    for asset in 0..2u32 {
        for i in 0..3u32 {
            for j in 0..3u32 {
                p.limits.insert((0, Kind::Issue, i, Some(j), asset), MAX);
                p.limits.insert((0, Kind::Transfer, i, Some(j), asset), MAX);
            }
            p.limits.insert((0, Kind::Burn, i, None, asset), MAX);
        }
    }
    if let Some(m) = m {
        p.limits
            .insert((0, Kind::Migrate, m.holder, Some(m.recipient), m.src), MAX);
    }
    Config {
        accounts: 4,
        assets: 2,
        vault: Some(VAULT),
        deadlines: vec![10, 10],
        now: 0,
        migration: m,
        policy: p,
    }
}

/// The Lean `fitsB`, with checked arithmetic.
fn fits(mc: &Machine, op: &Op) -> bool {
    match *op {
        Op::Issue { asset, amount, .. } => {
            mc.ledger.supply(asset).minted.checked_add(amount).is_some()
        }
        Op::Migrate(amount) => {
            let m = mc.config().migration.expect("migration configured");
            let (tsrc, ttgt, dust) = mc.migration_totals();
            let step = (|| {
                let acc = amount.checked_mul(m.num)?.checked_add(dust)?;
                let rel = acc / m.den;
                tsrc.checked_add(amount)?;
                ttgt.checked_add(rel)?;
                mc.ledger.supply(m.dst).minted.checked_add(rel)?;
                Some(())
            })();
            step.is_some()
        }
        _ => true,
    }
}

#[derive(Default)]
struct Seen {
    issue_ok: u64,
    issue_overflow: u64,
    migrate_ok: u64,
    migrate_overflow: u64,
    near_max: u64,
}

fn run(seed: u64, seen: &mut Seen) {
    let mut r = Rng(seed);
    let migrating = r.below(4) != 0;
    let m = migrating.then(|| MigrationConfig {
        holder: 1,
        recipient: 2,
        src: 0,
        dst: 1,
        num: match r.below(5) {
            0 => 1,
            1 => 3,
            2 => MAX / 2,
            3 => 1u128 << 100,
            _ => 1 + r.wide() % 1000,
        },
        den: match r.below(5) {
            0 => 1,
            1 => 2,
            2 => 7,
            3 => MAX,
            _ => 1 + r.wide() % 1000,
        },
    });
    let mut mc = Machine::new(config(m)).expect("valid config");
    for step in 0..300u64 {
        let mut op = match r.below(10) {
            0..=4 => Op::Issue {
                issuer: 0,
                recipient: r.below(3) as u32,
                asset: r.below(2) as u32,
                amount: extreme(&mut r),
            },
            5 => Op::Burn {
                holder: r.below(3) as u32,
                asset: r.below(2) as u32,
                amount: extreme(&mut r),
            },
            6 => Op::Transfer {
                src: r.below(3) as u32,
                dst: r.below(3) as u32,
                asset: r.below(2) as u32,
                amount: extreme(&mut r),
            },
            _ => Op::Migrate(extreme(&mut r)),
        };
        if let Op::Migrate(_) = op {
            match m {
                None => {
                    op = Op::Issue {
                        issuer: 0,
                        recipient: 1,
                        asset: 0,
                        amount: extreme(&mut r),
                    };
                }
                Some(mm) => {
                    let bal = mc.ledger.balance(mm.holder, mm.src);
                    op = Op::Migrate(match r.below(4) {
                        0 => bal,
                        1 => bal.saturating_sub(1),
                        2 => 1.min(bal),
                        _ => op_amount(&op).min(bal),
                    });
                }
            }
        }
        let predicted = fits(&mc, &op);
        let before = mc.snapshot();
        let nonce = mc.nonce(0);
        let mut id = [0u8; 32];
        id[..8].copy_from_slice(&seed.to_be_bytes());
        id[8..16].copy_from_slice(&step.to_be_bytes());
        let out = mc.process(
            id,
            Request {
                principal: 0,
                nonce,
                op,
            },
        );
        let stored = match out {
            Outcome::Done(s) => s,
            other => panic!("seed {seed} step {step}: unexpected outcome {other:?}"),
        };
        let accepted = matches!(stored, Stored::Accepted { .. });
        let overflow_denied = matches!(
            stored,
            Stored::Denied {
                denial: Denial {
                    cause: Cause::VaultOrOverflow,
                    ..
                },
                ..
            }
        );
        if !accepted {
            assert_eq!(
                before,
                mc.snapshot(),
                "seed {seed} step {step}: denial changed state"
            );
        }
        match op {
            Op::Issue { .. } => {
                // authorized, in range, not the vault: only the ceiling can deny
                assert_eq!(
                    accepted, predicted,
                    "seed {seed} step {step}: issue vs fitsB {op:?}"
                );
                if accepted {
                    seen.issue_ok += 1;
                } else {
                    assert!(overflow_denied && !predicted);
                    seen.issue_overflow += 1;
                }
            }
            Op::Migrate(a) => {
                let mm = m.expect("migration");
                let bal = before.ledger.balance(mm.holder, mm.src);
                if a > 0 && a <= bal {
                    assert_eq!(
                        accepted, predicted,
                        "seed {seed} step {step}: migrate vs fitsB {op:?}"
                    );
                    if accepted {
                        seen.migrate_ok += 1;
                    } else {
                        assert!(overflow_denied && !predicted);
                        seen.migrate_overflow += 1;
                    }
                }
            }
            _ => {}
        }
        if overflow_denied {
            assert!(
                !predicted,
                "seed {seed} step {step}: machine denied what fitsB allows {op:?}"
            );
        }
        assert!(mc.invariant(), "seed {seed} step {step}: invariant");
        for asset in 0..2 {
            if mc.ledger.supply(asset).minted > MAX - 1000 {
                seen.near_max += 1;
            }
        }
    }
}

fn op_amount(op: &Op) -> u128 {
    match *op {
        Op::Migrate(a) => a,
        _ => 0,
    }
}

#[test]
fn ceiling_matches_lean_fits_predicate() {
    let mut seen = Seen::default();
    for seed in 0..400u64 {
        run(seed, &mut seen);
    }
    // the runs must actually reach the ceiling, otherwise the check proves nothing
    assert!(seen.issue_ok > 0 && seen.issue_overflow > 0, "issues");
    assert!(
        seen.migrate_ok > 0 && seen.migrate_overflow > 0,
        "migrations"
    );
    assert!(seen.near_max > 0, "near the ceiling");
    println!(
        "issue ok {} overflow {}; migrate ok {} overflow {}; near-max steps {}",
        seen.issue_ok, seen.issue_overflow, seen.migrate_ok, seen.migrate_overflow, seen.near_max
    );
}
