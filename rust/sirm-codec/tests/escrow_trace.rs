//! Differential test against the independent Python reference
//! (`scripts/escrow_reference_trace.py`): 1500 seeded episodes of
//! issue/open/release/cancel with expected outcome codes and final balances.

use serde_json::Value;
use sirm_codec::escrow::*;
use sirm_codec::ledger::*;

fn u(v: &Value) -> u128 {
    v.as_str().unwrap().parse().unwrap()
}

fn code(r: &Result<(), EscrowError>) -> u8 {
    match r {
        Ok(()) => b'o',
        Err(EscrowError::NotReady) => b'n',
        Err(EscrowError::NotPending) => b'p',
        Err(EscrowError::VaultIsParty) => b'v',
        Err(EscrowError::ZeroAmount) => b'z',
        Err(EscrowError::Ledger(LedgerError::UnknownAccount(_)))
        | Err(EscrowError::Ledger(LedgerError::UnknownAsset(_))) => b'u',
        Err(EscrowError::Ledger(LedgerError::Insufficient)) => b'i',
        Err(e) => panic!("unexpected {e:?}"),
    }
}

#[test]
fn replay_episodes_match_python_reference() {
    let d: Value = serde_json::from_str(include_str!(
        "../../../engineering/ledger_core/results/escrow_trace_v0.json"
    ))
    .unwrap();
    let (accounts, assets) = (
        d["accounts"].as_u64().unwrap() as u32,
        d["assets"].as_u64().unwrap() as u32,
    );
    let mut phases = [0usize; 4];
    for (ei, ep) in d["episodes"].as_array().unwrap().iter().enumerate() {
        let vault = ep["vault"].as_u64().unwrap() as u32;
        let mut e = Escrow::new(Holdings::new(accounts, assets), vault);
        let outcomes = ep["outcomes"].as_str().unwrap().as_bytes();
        for (i, op) in ep["ops"].as_array().unwrap().iter().enumerate() {
            let n = |k: usize| op[k].as_u64().unwrap() as u32;
            let before = e.clone();
            let res = match op[0].as_str().unwrap() {
                "issue" => e
                    .holdings
                    .issue(n(1), n(2), u(&op[3]))
                    .map_err(EscrowError::Ledger),
                "open" => e.open(n(1), n(2), n(3), u(&op[4])),
                "release" => e.release(),
                "cancel" => e.cancel(),
                other => panic!("unknown op {other}"),
            };
            assert_eq!(code(&res), outcomes[i], "episode {ei} op {i}: {op}");
            if res.is_err() {
                assert_eq!(e, before, "rejected op changed state, episode {ei} op {i}");
            }
            assert!(e.invariant(assets), "invariant broken, episode {ei} op {i}");
        }
        for a in 0..accounts {
            for s in 0..assets {
                assert_eq!(
                    e.holdings.balance(a, s),
                    u(&ep["final"][a as usize][s as usize]),
                    "episode {ei} account {a} asset {s}"
                );
            }
        }
        let p = match e.record().phase {
            Phase::Ready => 0,
            Phase::Pending => 1,
            Phase::Released => 2,
            Phase::Cancelled => 3,
            Phase::Expired => panic!("expired is not reachable here"),
        };
        assert_eq!(
            ["ready", "pending", "released", "cancelled"][p],
            ep["phase"].as_str().unwrap()
        );
        phases[p] += 1;
    }
    assert!(phases.iter().all(|&c| c > 50), "weak coverage: {phases:?}");
}

fn funded() -> Escrow {
    let mut h = Holdings::new(4, 1);
    h.issue(0, 0, 100).unwrap();
    Escrow::new(h, 3)
}

#[test]
fn terminal_record_never_reopens() {
    let mut e = funded();
    e.open(0, 1, 0, 40).unwrap();
    e.release().unwrap();
    assert_eq!(e.open(0, 1, 0, 10), Err(EscrowError::NotReady));
    assert_eq!(e.release(), Err(EscrowError::NotPending));
    assert_eq!(e.cancel(), Err(EscrowError::NotPending));
    assert_eq!(
        (e.holdings.balance(0, 0), e.holdings.balance(1, 0)),
        (60, 40)
    );
    assert!(e.invariant(1));
}

#[test]
fn cancel_returns_exactly_the_deposit() {
    let mut e = funded();
    e.open(0, 1, 0, 100).unwrap();
    assert_eq!(e.holdings.balance(3, 0), 100);
    e.cancel().unwrap();
    assert_eq!(
        (e.holdings.balance(0, 0), e.holdings.balance(3, 0)),
        (100, 0)
    );
    assert_eq!(e.record().phase, Phase::Cancelled);
}

#[test]
fn open_checks_are_ordered_and_leave_state_unchanged() {
    let mut e = funded();
    let before = e.clone();
    assert_eq!(e.open(3, 1, 0, 5), Err(EscrowError::VaultIsParty));
    assert_eq!(e.open(0, 3, 0, 5), Err(EscrowError::VaultIsParty));
    assert_eq!(e.open(0, 1, 0, 0), Err(EscrowError::ZeroAmount));
    assert_eq!(
        e.open(0, 9, 0, 5),
        Err(EscrowError::Ledger(LedgerError::UnknownAccount(9)))
    );
    assert_eq!(
        e.open(0, 1, 0, 101),
        Err(EscrowError::Ledger(LedgerError::Insufficient))
    );
    assert_eq!(e, before);
    assert_eq!(e.record().phase, Phase::Ready);
}
