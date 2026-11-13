//! Differential test against the independent Python reference
//! (`scripts/ledger_reference_trace.py`): 3000 seeded operations with expected
//! accept/reject outcomes and state checkpoints, plus founder-allocation vectors.

use serde_json::Value;
use sirm_codec::ledger::*;

fn doc() -> Value {
    serde_json::from_str(include_str!(
        "../../../engineering/ledger_core/results/ledger_trace_v0.json"
    ))
    .unwrap()
}

fn u(v: &Value) -> u128 {
    v.as_str().unwrap().parse().unwrap()
}

fn check_state(h: &Holdings, expected: &Value, accounts: u32, assets: u32) {
    for a in 0..accounts {
        for s in 0..assets {
            assert_eq!(
                h.balance(a, s),
                u(&expected["balances"][a as usize][s as usize])
            );
        }
    }
    for s in 0..assets {
        let sup = h.supply(s);
        let e = &expected["supply"][s as usize];
        assert_eq!(
            (sup.minted, sup.burned, sup.outstanding),
            (u(&e[0]), u(&e[1]), u(&e[2]))
        );
    }
}

#[test]
fn replay_trace_matches_python_reference() {
    let d = doc();
    let t = &d["trace"];
    let (accounts, assets) = (
        t["accounts"].as_u64().unwrap() as u32,
        t["assets"].as_u64().unwrap() as u32,
    );
    let outcomes = t["outcomes"].as_str().unwrap().as_bytes();
    let mut h = Holdings::new(accounts, assets);
    let mut cps = t["checkpoints"].as_array().unwrap().iter();
    let mut next_cp = cps.next();
    for (i, op) in t["ops"].as_array().unwrap().iter().enumerate() {
        let n = |k: usize| op[k].as_u64().unwrap() as u32;
        let before = h.clone();
        let res = match op[0].as_str().unwrap() {
            "transfer" => h.transfer(n(1), n(2), n(3), u(&op[4])),
            "issue" => h.issue(n(1), n(2), u(&op[3])),
            "burn" => h.burn(n(1), n(2), u(&op[3])),
            other => panic!("unknown op {other}"),
        };
        let expected_ok = outcomes[i] == b'o';
        assert_eq!(res.is_ok(), expected_ok, "op {i}: {op}");
        if !expected_ok {
            assert_eq!(res, Err(LedgerError::Insufficient));
            assert_eq!(h, before, "rejected op {i} changed state");
        }
        assert!(h.invariant(), "invariant broken after op {i}");
        if let Some(cp) = next_cp {
            if cp["after"].as_u64().unwrap() as usize == i + 1 {
                check_state(&h, cp, accounts, assets);
                next_cp = cps.next();
            }
        }
    }
    assert!(next_cp.is_none(), "unused checkpoints");
    check_state(&h, &t["final"], accounts, assets);
}

#[test]
fn founder_allocation_matches_python_reference() {
    for v in doc()["founder"].as_array().unwrap() {
        let total = u(&v["total"]);
        if v["fits_u128"].as_bool().unwrap() {
            assert_eq!(founder_allocation(total), Ok(u(&v["founder"])), "{total}");
            assert_eq!(
                remaining_genesis_pool(total),
                Ok(u(&v["remaining"])),
                "{total}"
            );
            assert!(founder_allocation(total).unwrap() <= total);
        } else {
            assert_eq!(
                founder_allocation(total),
                Err(LedgerError::Overflow),
                "{total}"
            );
        }
    }
}

#[test]
fn rate_constants_match_the_lean_identity() {
    // SIRM.FinancialCore: founderRatePpm * 100_000 = ppmScale * 1_309 and founderRatePpm <= ppmScale.
    assert_eq!(FOUNDER_RATE_PPM * 100_000, PPM_SCALE * 1_309);
    const { assert!(FOUNDER_RATE_PPM <= PPM_SCALE) };
}

#[test]
fn self_transfer_is_a_noop_even_when_unfunded() {
    let mut h = Holdings::new(2, 1);
    let before = h.clone();
    assert_eq!(h.transfer(0, 0, 0, 1_000), Ok(()));
    assert_eq!(h, before);
}

#[test]
fn out_of_range_ids_are_rejected_without_writes() {
    let mut h = Holdings::new(2, 1);
    h.issue(0, 0, 5).unwrap();
    let before = h.clone();
    assert_eq!(h.transfer(0, 2, 0, 1), Err(LedgerError::UnknownAccount(2)));
    assert_eq!(h.issue(0, 1, 1), Err(LedgerError::UnknownAsset(1)));
    assert_eq!(h.burn(5, 0, 1), Err(LedgerError::UnknownAccount(5)));
    assert_eq!(h, before);
}

#[test]
fn overflow_is_rejected_without_writes() {
    let mut h = Holdings::new(2, 1);
    h.issue(0, 0, u128::MAX).unwrap();
    let before = h.clone();
    assert_eq!(h.issue(1, 0, 1), Err(LedgerError::Overflow));
    assert_eq!(h, before);
    h.issue(1, 0, 0).unwrap();
    assert!(h.invariant());
}
