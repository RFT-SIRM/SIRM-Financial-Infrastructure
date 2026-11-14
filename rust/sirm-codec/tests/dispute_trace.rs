//! Differential test against the independent Python reference
//! (`scripts/dispute_reference_trace.py`): 1500 seeded episodes of
//! issue/open/release/cancel/expire/advance/dispute with per-ID freeze.

use serde_json::Value;
use sirm_codec::dispute::*;
use sirm_codec::escrow::Phase;
use sirm_codec::ledger::*;
use sirm_codec::timelock::*;

fn u(v: &Value) -> u128 {
    v.as_str().unwrap().parse().unwrap()
}

fn code(r: &Result<(), DisputeError>) -> u8 {
    use TimeLockError::*;
    match r {
        Ok(()) => b'o',
        Err(DisputeError::Disputed) => b'x',
        Err(DisputeError::AlreadyFiled) => b'a',
        Err(DisputeError::ClaimantNotParty) => b'c',
        Err(DisputeError::TimeLock(e)) => match e {
            UnknownId => b'w',
            IdInUse => b'k',
            NotPending => b'n',
            DeadlinePassed => b'd',
            DeadlineNotReached => b'e',
            VaultIsParty => b'v',
            ZeroAmount => b'z',
            TimeNotForward => b't',
            Ledger(LedgerError::UnknownAccount(_)) | Ledger(LedgerError::UnknownAsset(_)) => b'u',
            Ledger(LedgerError::Insufficient) => b'i',
            other => panic!("unexpected {other:?}"),
        },
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
        "../../../engineering/ledger_core/results/dispute_trace_v0.json"
    ))
    .unwrap();
    let (accounts, assets, ids) = (
        d["accounts"].as_u64().unwrap() as u32,
        d["assets"].as_u64().unwrap() as u32,
        d["ids"].as_u64().unwrap() as usize,
    );
    let (mut frozen, mut rejected_after_deadline) = (0usize, 0usize);
    for (ei, ep) in d["episodes"].as_array().unwrap().iter().enumerate() {
        let vault = ep["vault"].as_u64().unwrap() as u32;
        let deadlines: Vec<u64> = ep["deadlines"]
            .as_array()
            .unwrap()
            .iter()
            .map(|v| v.as_u64().unwrap())
            .collect();
        let mut e = DisputedEscrow::new(TimeLockedEscrow::new(
            Holdings::new(accounts, assets),
            vault,
            deadlines.clone(),
            ep["start"].as_u64().unwrap(),
        ));
        let outcomes = ep["outcomes"].as_str().unwrap().as_bytes();
        for (i, op) in ep["ops"].as_array().unwrap().iter().enumerate() {
            let n = |k: usize| op[k].as_u64().unwrap() as u32;
            let id = |k: usize| op[k].as_u64().unwrap() as usize;
            let before = e.clone();
            let res = match op[0].as_str().unwrap() {
                "issue" => e
                    .escrow
                    .holdings
                    .issue(n(1), n(2), u(&op[3]))
                    .map_err(|x| DisputeError::TimeLock(TimeLockError::Ledger(x))),
                "open" => e.open(id(1), n(2), n(3), n(4), u(&op[5])),
                "release" => e.release(id(1)),
                "cancel" => e.cancel(id(1)),
                "expire" => e.expire(id(1)),
                "advance" => e.advance(op[1].as_i64().unwrap().max(0) as u64),
                "dispute" => e.raise(id(1), n(2), n(3)),
                other => panic!("unknown op {other}"),
            };
            assert_eq!(code(&res), outcomes[i], "episode {ei} op {i}: {op}");
            if res.is_err() {
                assert_eq!(e, before, "rejected op changed state, episode {ei} op {i}");
            }
            if code(&res) == b'x' {
                frozen += 1;
                if e.escrow.now() >= deadlines[id(1)] {
                    rejected_after_deadline += 1;
                }
            }
            assert!(e.invariant(assets), "invariant broken, episode {ei} op {i}");
        }
        assert_eq!(e.escrow.now(), ep["now"].as_u64().unwrap());
        for a in 0..accounts {
            for s in 0..assets {
                assert_eq!(
                    e.escrow.holdings.balance(a, s),
                    u(&ep["final"][a as usize][s as usize]),
                    "episode {ei} account {a} asset {s}"
                );
            }
        }
        for k in 0..ids {
            assert_eq!(
                phase_name(e.escrow.record(k).map(|r| r.phase)),
                ep["phases"][k].as_str().unwrap(),
                "episode {ei} id {k}"
            );
            match (e.filing(k), &ep["filings"][k]) {
                (None, Value::Null) => {}
                (Some(f), v) => assert_eq!(
                    (f.principal as u64, f.claimant as u64, f.filed_at),
                    (
                        v[0].as_u64().unwrap(),
                        v[1].as_u64().unwrap(),
                        v[2].as_u64().unwrap()
                    ),
                    "episode {ei} id {k} filing"
                ),
                (a, b) => panic!("filing mismatch {a:?} vs {b}"),
            }
        }
    }
    assert!(frozen > 100, "weak coverage: {frozen} freeze rejections");
    assert!(
        rejected_after_deadline > 0,
        "no frozen rejection after the deadline"
    );
}

fn funded() -> DisputedEscrow {
    let mut h = Holdings::new(4, 1);
    h.issue(0, 0, 100).unwrap();
    DisputedEscrow::new(TimeLockedEscrow::new(h, 3, vec![5, 8], 0))
}

#[test]
fn dispute_freezes_the_id_even_after_the_deadline_and_keeps_funds_in_the_vault() {
    let mut e = funded();
    e.open(0, 0, 1, 0, 40).unwrap();
    e.open(1, 0, 2, 0, 10).unwrap();
    e.raise(0, 7, 1).unwrap();
    assert_eq!(e.raise(0, 7, 0), Err(DisputeError::AlreadyFiled));
    assert_eq!(e.release(0), Err(DisputeError::Disputed));
    assert_eq!(e.cancel(0), Err(DisputeError::Disputed));
    e.advance(6).unwrap();
    assert_eq!(e.expire(0), Err(DisputeError::Disputed));
    // unrelated ID stays operable (its own deadline is 8)
    e.release(1).unwrap();
    assert_eq!(e.escrow.holdings.balance(3, 0), 40);
    assert_eq!(e.escrow.record(0).unwrap().phase, Phase::Pending);
    assert_eq!(
        e.filing(0),
        Some(Filing {
            principal: 7,
            claimant: 1,
            filed_at: 0
        })
    );
    assert!(e.invariant(1));
}

#[test]
fn raise_requires_pending_before_deadline_and_a_party_claimant() {
    let mut e = funded();
    assert_eq!(
        e.raise(0, 0, 0),
        Err(DisputeError::TimeLock(TimeLockError::UnknownId))
    );
    e.open(0, 0, 1, 0, 40).unwrap();
    assert_eq!(e.raise(0, 0, 2), Err(DisputeError::ClaimantNotParty));
    e.advance(5).unwrap();
    assert_eq!(
        e.raise(0, 0, 0),
        Err(DisputeError::TimeLock(TimeLockError::DeadlinePassed))
    );
    e.expire(0).unwrap();
    assert_eq!(
        e.raise(0, 0, 0),
        Err(DisputeError::TimeLock(TimeLockError::NotPending))
    );
    assert!(e.filing(0).is_none());
}
