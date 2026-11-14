//! Differential test against the independent Python reference
//! (`scripts/fee_reference_trace.py`) plus edge cases of `SIRM.FeeAccounting`.

use serde_json::Value;
use sirm_codec::fees::*;
use sirm_codec::ledger::*;

fn u(v: &Value) -> u128 {
    v.as_str().unwrap().parse().unwrap()
}

fn check(h: &Holdings, expected: &Value, accounts: u32, assets: u32) {
    for a in 0..accounts {
        for s in 0..assets {
            assert_eq!(
                h.balance(a, s),
                u(&expected[a as usize][s as usize]),
                "account {a} asset {s}"
            );
        }
    }
}

#[test]
fn replay_trace_matches_python_reference() {
    let d: Value = serde_json::from_str(include_str!(
        "../../../engineering/ledger_core/results/fee_trace_v0.json"
    ))
    .unwrap();
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
            "issue" => h.issue(n(1), n(2), u(&op[3])),
            "fee" => fee_transfer(&mut h, n(1), n(2), n(3), n(4), u(&op[5]), u(&op[6])),
            other => panic!("unknown op {other}"),
        };
        match outcomes[i] {
            b'o' => assert_eq!(res, Ok(()), "op {i}: {op}"),
            b'e' => assert_eq!(res, Err(LedgerError::FeeExceedsGross), "op {i}: {op}"),
            b'i' => assert_eq!(res, Err(LedgerError::Insufficient), "op {i}: {op}"),
            c => panic!("bad outcome {c}"),
        }
        if res.is_err() {
            assert_eq!(h, before, "rejected op {i} changed state");
        }
        assert!(h.invariant(), "invariant broken after op {i}");
        if let Some(cp) = next_cp {
            if cp["after"].as_u64().unwrap() as usize == i + 1 {
                check(&h, &cp["balances"], accounts, assets);
                next_cp = cps.next();
            }
        }
    }
    assert!(next_cp.is_none(), "unused checkpoints");
    check(&h, &t["final"], accounts, assets);
}

fn funded(amount: u128) -> Holdings {
    let mut h = Holdings::new(3, 1);
    h.issue(0, 0, amount).unwrap();
    h
}

#[test]
fn legs_split_gross_into_net_and_fee() {
    let mut h = funded(100);
    fee_transfer(&mut h, 0, 1, 2, 0, 100, 7).unwrap();
    assert_eq!(
        (h.balance(0, 0), h.balance(1, 0), h.balance(2, 0)),
        (0, 93, 7)
    );
    assert!(h.invariant());
}

#[test]
fn coinciding_roles_follow_lean_leg_semantics() {
    // payer = beneficiary: net leg is a no-op, payer pays only the fee.
    let mut h = funded(100);
    fee_transfer(&mut h, 0, 0, 2, 0, 100, 7).unwrap();
    assert_eq!((h.balance(0, 0), h.balance(2, 0)), (93, 7));
    // payer = collector: fee leg is a no-op, beneficiary gets only the net.
    let mut h = funded(100);
    fee_transfer(&mut h, 0, 1, 0, 0, 100, 7).unwrap();
    assert_eq!((h.balance(0, 0), h.balance(1, 0)), (7, 93));
    // beneficiary = collector: receives the full gross.
    let mut h = funded(100);
    fee_transfer(&mut h, 0, 1, 1, 0, 100, 7).unwrap();
    assert_eq!((h.balance(0, 0), h.balance(1, 0)), (0, 100));
    assert!(h.invariant());
}

#[test]
fn gross_funding_is_required_even_when_all_roles_coincide() {
    let mut h = funded(5);
    let before = h.clone();
    assert_eq!(
        fee_transfer(&mut h, 0, 0, 0, 0, 6, 1),
        Err(LedgerError::Insufficient)
    );
    assert_eq!(h, before);
}

#[test]
fn fee_above_gross_is_rejected_first() {
    let mut h = funded(0);
    let before = h.clone();
    assert_eq!(
        fee_transfer(&mut h, 0, 1, 2, 0, 1, 2),
        Err(LedgerError::FeeExceedsGross)
    );
    assert_eq!(h, before);
    assert_eq!(net_amount(10, 3), Ok(7));
    assert_eq!(net_amount(3, 10), Err(LedgerError::FeeExceedsGross));
}

#[test]
fn unknown_roles_and_credit_overflow_leave_state_unchanged() {
    let mut h = funded(10);
    let before = h.clone();
    assert_eq!(
        fee_transfer(&mut h, 0, 1, 9, 0, 1, 0),
        Err(LedgerError::UnknownAccount(9))
    );
    assert_eq!(
        fee_transfer(&mut h, 0, 1, 2, 3, 1, 0),
        Err(LedgerError::UnknownAsset(3))
    );
    assert_eq!(h, before);
}

#[test]
fn credits_up_to_the_u128_maximum_succeed() {
    // Holdings never exceed minted supply <= u128::MAX, so a credit overflow cannot
    // arise from a reconciled state; the checked arithmetic is defence in depth.
    let mut h = Holdings::new(3, 1);
    h.issue(0, 0, 10).unwrap();
    h.issue(1, 0, u128::MAX - 10).unwrap();
    assert_eq!(fee_transfer(&mut h, 0, 1, 1, 0, 10, 7), Ok(()));
    assert_eq!((h.balance(0, 0), h.balance(1, 0)), (0, u128::MAX));
    assert!(h.invariant());
}
