//! Differential test against the independent Python reference
//! (`scripts/migration_reference_trace.py`): 1505 episodes (5 hand-built boundary episodes
//! plus 1500 seeded random ones) of issue/migrate with per-principal nonces, exact dust
//! carry and u128 overflow rejection.

use serde_json::Value;
use sirm_codec::ledger::*;
use sirm_codec::migration::*;

fn u(v: &Value) -> u128 {
    v.as_str().unwrap().parse().unwrap()
}

fn code(r: &Result<(), MigrationError>) -> u8 {
    match r {
        Ok(()) => b'o',
        Err(MigrationError::NonceMismatch) => b'm',
        Err(MigrationError::ZeroAmount) => b'z',
        Err(MigrationError::Insufficient) => b'i',
        Err(MigrationError::Overflow) => b'v',
        Err(MigrationError::Ledger(e)) => panic!("unexpected ledger error {e:?}"),
    }
}

#[test]
fn replay_episodes_match_python_reference() {
    let d: Value = serde_json::from_str(include_str!(
        "../../../engineering/ledger_core/results/migration_trace_v0.json"
    ))
    .unwrap();
    let (accounts, assets) = (
        d["accounts"].as_u64().unwrap() as u32,
        d["assets"].as_u64().unwrap() as u32,
    );
    let (mut overflow_rejections, mut with_dust) = (0, 0);
    for (ei, ep) in d["episodes"].as_array().unwrap().iter().enumerate() {
        let mut m = Migration::new(
            Holdings::new(accounts, assets),
            ep["holder"].as_u64().unwrap() as u32,
            ep["recipient"].as_u64().unwrap() as u32,
            0,
            1,
            u(&ep["num"]),
            u(&ep["den"]),
        )
        .unwrap();
        let outcomes = ep["outcomes"].as_str().unwrap().as_bytes();
        for (i, op) in ep["ops"].as_array().unwrap().iter().enumerate() {
            let before = m.clone();
            let res = match op[0].as_str().unwrap() {
                "issue" => m
                    .holdings
                    .issue(
                        op[1].as_str().unwrap().parse().unwrap(),
                        op[2].as_str().unwrap().parse().unwrap(),
                        u(&op[3]),
                    )
                    .map_err(|e| match e {
                        LedgerError::Overflow => MigrationError::Overflow,
                        o => MigrationError::Ledger(o),
                    }),
                "migrate" => m.migrate(
                    op[1].as_str().unwrap().parse().unwrap(),
                    op[2].as_str().unwrap().parse().unwrap(),
                    u(&op[3]),
                ),
                other => panic!("unknown op {other}"),
            };
            assert_eq!(code(&res), outcomes[i], "episode {ei} op {i}: {op}");
            if res.is_err() {
                assert_eq!(m, before, "rejected op changed state, episode {ei} op {i}");
            }
            if code(&res) == b'v' {
                overflow_rejections += 1;
            }
            assert!(
                m.holdings.invariant(),
                "holdings invariant, episode {ei} op {i}"
            );
            assert!(m.dust_invariant(), "dust equation, episode {ei} op {i}");
            assert_eq!(
                m.holdings.supply(0).burned,
                m.total_source(),
                "source burn equals total source, episode {ei} op {i}"
            );
        }
        let f = &ep["final"];
        assert_eq!(m.total_source(), u(&f["total_source"]), "episode {ei}");
        assert_eq!(m.total_target(), u(&f["total_target"]), "episode {ei}");
        assert_eq!(m.dust(), u(&f["dust"]), "episode {ei}");
        for a in 0..accounts {
            for s in 0..assets {
                assert_eq!(
                    m.holdings.balance(a, s),
                    u(&f["balances"][a as usize][s as usize]),
                    "episode {ei} account {a} asset {s}"
                );
            }
        }
        for s in 0..assets as usize {
            let sup = m.holdings.supply(s as u32);
            assert_eq!(sup.minted, u(&f["minted"][s]));
            assert_eq!(sup.burned, u(&f["burned"][s]));
        }
        for (p, n) in f["nonces"].as_array().unwrap().iter().enumerate() {
            assert_eq!(
                m.nonce(p as u32),
                n.as_u64().unwrap(),
                "episode {ei} principal {p}"
            );
        }
        if m.dust() != 0 {
            with_dust += 1;
        }
    }
    assert!(
        overflow_rejections >= 5,
        "boundary episodes lost: {overflow_rejections}"
    );
    assert!(with_dust > 500, "weak dust coverage: {with_dust}");
}

fn stream(num: u128, den: u128) -> Migration {
    let mut h = Holdings::new(3, 2);
    h.issue(0, 0, 1_000).unwrap();
    Migration::new(h, 0, 1, 0, 1, num, den).unwrap()
}

#[test]
fn constructor_rejects_degenerate_rates_and_equal_assets() {
    let h = || Holdings::new(2, 2);
    assert!(Migration::new(h(), 0, 1, 0, 1, 0, 1).is_none());
    assert!(Migration::new(h(), 0, 1, 0, 1, 1, 0).is_none());
    assert!(Migration::new(h(), 0, 1, 0, 0, 1, 1).is_none());
    assert!(Migration::new(h(), 0, 1, 0, 1, 1, 1).is_some());
}

#[test]
fn dust_is_carried_never_rounded_away() {
    // 1 source unit at 1/3: a target unit is released on every third migration.
    let mut m = stream(1, 3);
    let mut released = vec![];
    for n in 0..6u64 {
        let before = m.holdings.balance(1, 1);
        m.migrate(0, n, 1).unwrap();
        released.push(m.holdings.balance(1, 1) - before);
    }
    assert_eq!(released, vec![0, 0, 1, 0, 0, 1]);
    assert_eq!((m.total_source(), m.total_target(), m.dust()), (6, 2, 0));
    assert!(m.dust_invariant());
}

#[test]
fn nonces_are_per_principal_and_exact() {
    let mut m = stream(1, 1);
    assert_eq!(m.migrate(0, 1, 5), Err(MigrationError::NonceMismatch));
    m.migrate(0, 0, 5).unwrap();
    assert_eq!(m.migrate(0, 0, 5), Err(MigrationError::NonceMismatch));
    m.migrate(1, 0, 5).unwrap();
    assert_eq!((m.nonce(0), m.nonce(1), m.nonce(2)), (1, 1, 0));
    assert_eq!(m.released(7), Ok(7));
    assert_eq!(m.holdings.balance(0, 0), 990);
    assert_eq!(m.holdings.balance(1, 1), 10);
}

#[test]
fn zero_amount_and_unfunded_requests_do_not_consume_the_nonce() {
    let mut m = stream(2, 1);
    assert_eq!(m.migrate(0, 0, 0), Err(MigrationError::ZeroAmount));
    assert_eq!(m.migrate(0, 0, 1_001), Err(MigrationError::Insufficient));
    assert_eq!(m.nonce(0), 0);
    m.migrate(0, 0, 1_000).unwrap();
    assert_eq!(m.holdings.balance(1, 1), 2_000);
}
