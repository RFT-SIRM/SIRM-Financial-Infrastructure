//! Differential test against the independent Python reference
//! (`scripts/timelock_reference_trace.py`): 1500 seeded episodes of
//! issue/open/release/cancel/expire/advance on a pooled-vault, multi-ID, time-locked escrow.

use serde_json::Value;
use sirm_codec::escrow::Phase;
use sirm_codec::ledger::*;
use sirm_codec::timelock::*;

fn u(v: &Value) -> u128 {
    v.as_str().unwrap().parse().unwrap()
}

fn code(r: &Result<(), TimeLockError>) -> u8 {
    use TimeLockError::*;
    match r {
        Ok(()) => b'o',
        Err(UnknownId) => b'w',
        Err(IdInUse) => b'k',
        Err(NotPending) => b'n',
        Err(DeadlinePassed) => b'd',
        Err(DeadlineNotReached) => b'e',
        Err(VaultIsParty) => b'v',
        Err(ZeroAmount) => b'z',
        Err(TimeNotForward) => b't',
        Err(Ledger(LedgerError::UnknownAccount(_))) | Err(Ledger(LedgerError::UnknownAsset(_))) => {
            b'u'
        }
        Err(Ledger(LedgerError::Insufficient)) => b'i',
        Err(e) => panic!("unexpected {e:?}"),
    }
}

fn phase_name(p: Option<Phase>) -> &'static str {
    match p {
        None => "none",
        Some(Phase::Pending) => "pending",
        Some(Phase::Released) => "released",
        Some(Phase::Cancelled) => "cancelled",
        Some(Phase::Expired) => "expired",
        Some(Phase::Ready) => panic!("ready record in registry"),
    }
}

#[test]
fn replay_episodes_match_python_reference() {
    let d: Value = serde_json::from_str(include_str!(
        "../../../engineering/ledger_core/results/timelock_trace_v0.json"
    ))
    .unwrap();
    let (accounts, assets, ids) = (
        d["accounts"].as_u64().unwrap() as u32,
        d["assets"].as_u64().unwrap() as u32,
        d["ids"].as_u64().unwrap() as usize,
    );
    let mut seen = std::collections::BTreeMap::new();
    for (ei, ep) in d["episodes"].as_array().unwrap().iter().enumerate() {
        let vault = ep["vault"].as_u64().unwrap() as u32;
        let deadlines: Vec<u64> = ep["deadlines"]
            .as_array()
            .unwrap()
            .iter()
            .map(|v| v.as_u64().unwrap())
            .collect();
        let mut e = TimeLockedEscrow::new(
            Holdings::new(accounts, assets),
            vault,
            deadlines,
            ep["start"].as_u64().unwrap(),
        );
        let outcomes = ep["outcomes"].as_str().unwrap().as_bytes();
        for (i, op) in ep["ops"].as_array().unwrap().iter().enumerate() {
            let n = |k: usize| op[k].as_u64().unwrap() as u32;
            let id = |k: usize| op[k].as_u64().unwrap() as usize;
            let before = e.clone();
            let res = match op[0].as_str().unwrap() {
                "issue" => e
                    .holdings
                    .issue(n(1), n(2), u(&op[3]))
                    .map_err(TimeLockError::Ledger),
                "open" => e.open(id(1), n(2), n(3), n(4), u(&op[5])),
                "release" => e.release(id(1)),
                "cancel" => e.cancel(id(1)),
                "expire" => e.expire(id(1)),
                "advance" => e.advance(op[1].as_i64().unwrap().max(0) as u64),
                other => panic!("unknown op {other}"),
            };
            assert_eq!(code(&res), outcomes[i], "episode {ei} op {i}: {op}");
            if res.is_err() {
                assert_eq!(e, before, "rejected op changed state, episode {ei} op {i}");
            }
            assert!(e.invariant(assets), "invariant broken, episode {ei} op {i}");
        }
        assert_eq!(e.now(), ep["now"].as_u64().unwrap(), "episode {ei} clock");
        for a in 0..accounts {
            for s in 0..assets {
                assert_eq!(
                    e.holdings.balance(a, s),
                    u(&ep["final"][a as usize][s as usize]),
                    "episode {ei} account {a} asset {s}"
                );
            }
        }
        for k in 0..ids {
            let name = phase_name(e.record(k).map(|r| r.phase));
            assert_eq!(
                name,
                ep["phases"][k].as_str().unwrap(),
                "episode {ei} id {k}"
            );
            *seen.entry(name).or_insert(0usize) += 1;
        }
    }
    for p in ["pending", "released", "cancelled", "expired"] {
        assert!(
            seen.get(p).copied().unwrap_or(0) > 50,
            "weak coverage {p}: {seen:?}"
        );
    }
}

fn funded() -> TimeLockedEscrow {
    let mut h = Holdings::new(4, 1);
    h.issue(0, 0, 100).unwrap();
    TimeLockedEscrow::new(h, 3, vec![5, 8], 0)
}

#[test]
fn deadline_gates_release_cancel_and_expiry() {
    let mut e = funded();
    e.open(0, 0, 1, 0, 40).unwrap();
    assert_eq!(e.expire(0), Err(TimeLockError::DeadlineNotReached));
    e.advance(5).unwrap();
    assert_eq!(e.release(0), Err(TimeLockError::DeadlinePassed));
    assert_eq!(e.cancel(0), Err(TimeLockError::DeadlinePassed));
    assert_eq!(e.open(1, 0, 1, 0, 1), Ok(()));
    e.expire(0).unwrap();
    assert_eq!(e.record(0).unwrap().phase, Phase::Expired);
    assert_eq!(e.holdings.balance(0, 0), 99);
    assert_eq!(e.expire(0), Err(TimeLockError::NotPending));
    assert_eq!(e.open(0, 0, 1, 0, 1), Err(TimeLockError::IdInUse));
    assert!(e.invariant(1));
}

#[test]
fn clock_is_strictly_monotone_and_ids_are_bounded() {
    let mut e = funded();
    assert_eq!(e.advance(0), Err(TimeLockError::TimeNotForward));
    e.advance(3).unwrap();
    assert_eq!(e.advance(3), Err(TimeLockError::TimeNotForward));
    assert_eq!(e.advance(2), Err(TimeLockError::TimeNotForward));
    assert_eq!(e.open(2, 0, 1, 0, 1), Err(TimeLockError::UnknownId));
    assert_eq!(e.release(2), Err(TimeLockError::UnknownId));
    assert_eq!(e.release(0), Err(TimeLockError::UnknownId));
    assert_eq!(e.now(), 3);
}

#[test]
fn pooled_vault_backs_all_pending_records() {
    let mut e = funded();
    e.open(0, 0, 1, 0, 30).unwrap();
    e.open(1, 0, 2, 0, 20).unwrap();
    assert_eq!(e.holdings.balance(3, 0), 50);
    assert_eq!(e.pooled_reserve(0), Some(50));
    e.release(0).unwrap();
    assert_eq!(e.pooled_reserve(0), Some(20));
    assert_eq!(e.holdings.balance(3, 0), 20);
    e.cancel(1).unwrap();
    assert_eq!(e.holdings.balance(3, 0), 0);
    assert!(e.invariant(1));
}
