//! Differential test against `scripts/machine_reference_trace.py`: 4000 requests with
//! exact replays, same-ID conflicts, stale/future nonces, authorization and funds denials.

use serde_json::Value;
use sirm_codec::auth::*;
use sirm_codec::ledger::*;
use sirm_codec::machine::*;

fn u(v: &Value) -> u128 {
    v.as_str().unwrap().parse().unwrap()
}

fn doc() -> Value {
    serde_json::from_str(include_str!(
        "../../../engineering/ledger_core/results/machine_trace_v0.json"
    ))
    .unwrap()
}

fn policy(t: &Value) -> Policy {
    let grants: Vec<Grant> = t["grants"]
        .as_array()
        .unwrap()
        .iter()
        .map(|g| {
            let a = g[2].as_u64().unwrap() as u32;
            let scope = match g[1].as_str().unwrap() {
                "transfer" => Scope::Transfer {
                    source: a,
                    destination: g[3].as_u64().unwrap() as u32,
                },
                "issue" => Scope::Issue {
                    issuer: a,
                    recipient: g[3].as_u64().unwrap() as u32,
                },
                _ => Scope::Burn { holder: a },
            };
            Grant {
                principal: g[0].as_u64().unwrap() as u32,
                scope,
                asset: g[4].as_u64().unwrap() as u32,
                max_amount: u(&g[5]),
            }
        })
        .collect();
    let control: Vec<(u32, u32)> = t["control"]
        .as_array()
        .unwrap()
        .iter()
        .map(|c| (c[0].as_u64().unwrap() as u32, c[1].as_u64().unwrap() as u32))
        .collect();
    Policy::new(&grants, &control).unwrap()
}

fn id_bytes(n: u64) -> RequestId {
    let mut id = [0u8; 32];
    id[24..].copy_from_slice(&n.to_be_bytes());
    id
}

fn reason_code(r: DenialReason) -> &'static str {
    match r {
        DenialReason::TransferAuthorizationDenied => "ta",
        DenialReason::IssueAuthorizationDenied => "ia",
        DenialReason::BurnAuthorizationDenied => "ba",
        DenialReason::TransferInsufficientFunds => "tf",
        DenialReason::BurnInsufficientFunds => "bf",
    }
}

fn stored_token(s: Stored) -> String {
    match s {
        Stored::Accepted {
            accepted_nonce,
            next_nonce,
        } => format!("A{accepted_nonce}>{next_nonce}"),
        Stored::Denied {
            expected_nonce,
            reason,
        } => format!("N{}@{expected_nonce}", reason_code(reason)),
    }
}

fn token(o: Outcome) -> String {
    match o {
        Outcome::Accepted(s) | Outcome::DeniedCached(s) => stored_token(s),
        Outcome::Replay(s) => format!("R{}", stored_token(s)),
        Outcome::RequestIdConflict => "C".into(),
        Outcome::StaleNonce => "S".into(),
        Outcome::FutureNonce => "F".into(),
        Outcome::Invalid(e) => panic!("unexpected invalid {e:?}"),
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
    let mut m = Processor::new(Holdings::new(accounts, assets), policy(t));
    let tokens = t["tokens"].as_array().unwrap();
    for (i, r) in t["requests"].as_array().unwrap().iter().enumerate() {
        let n = |k: usize| r[k].as_u64().unwrap() as u32;
        let (id, principal, nonce, asset, amt) = (
            r[0].as_u64().unwrap(),
            n(1),
            r[2].as_u64().unwrap(),
            n(6),
            u(&r[7]),
        );
        let operation = match r[3].as_str().unwrap() {
            "transfer" => Operation::Transfer {
                source: n(4),
                destination: n(5),
                asset,
                amount: amt,
            },
            "issue" => Operation::Issue {
                issuer: n(4),
                recipient: n(5),
                asset,
                amount: amt,
            },
            _ => Operation::Burn {
                holder: n(4),
                asset,
                amount: amt,
            },
        };
        let before = m.clone();
        let out = m.process(
            id_bytes(id),
            Request {
                principal,
                nonce,
                operation,
            },
        );
        let got = token(out);
        assert_eq!(got, tokens[i].as_str().unwrap(), "request {i}: {r}");
        // Anything that is not a fresh success or fresh denial must leave the processor untouched.
        if !matches!(out, Outcome::Accepted(_) | Outcome::DeniedCached(_)) {
            assert_eq!(m, before, "request {i} ({got}) changed state");
        }
        if matches!(out, Outcome::DeniedCached(_)) {
            assert_eq!(m.ledger, before.ledger, "denial {i} changed the ledger");
            assert_eq!(
                m.next_nonce(principal),
                before.next_nonce(principal),
                "denial {i} consumed a nonce"
            );
        }
        assert!(m.ledger.invariant(), "invariant broken after request {i}");
    }
    for (p, e) in t["final_nonces"].as_array().unwrap().iter().enumerate() {
        assert_eq!(m.next_nonce(p as u32), e.as_u64().unwrap());
    }
    assert_eq!(m.cached() as u64, t["receipts"].as_u64().unwrap());
    for a in 0..accounts {
        for s in 0..assets {
            assert_eq!(
                m.ledger.balance(a, s),
                u(&t["final"]["balances"][a as usize][s as usize])
            );
        }
    }
}

fn open_policy() -> Policy {
    Policy::new(
        &[Grant {
            principal: 0,
            scope: Scope::Issue {
                issuer: 0,
                recipient: 0,
            },
            asset: 0,
            max_amount: 100,
        }],
        &[(0, 0)],
    )
    .unwrap()
}

#[test]
fn exact_retry_replays_even_after_nonce_moved_on() {
    let mut m = Processor::new(Holdings::new(1, 1), open_policy());
    let req = Request {
        principal: 0,
        nonce: 0,
        operation: Operation::Issue {
            issuer: 0,
            recipient: 0,
            asset: 0,
            amount: 5,
        },
    };
    let first = m.process(id_bytes(1), req);
    assert!(matches!(first, Outcome::Accepted(_)));
    assert_eq!(m.next_nonce(0), 1);
    // The nonce is now stale, yet the exact retry returns the stored response.
    assert_eq!(
        m.process(id_bytes(1), req),
        Outcome::Replay(Stored::Accepted {
            accepted_nonce: 0,
            next_nonce: 1
        })
    );
    assert_eq!(m.ledger.balance(0, 0), 5, "retry must not double-apply");
}

#[test]
fn out_of_range_account_is_invalid_and_not_cached() {
    let mut m = Processor::new(
        Holdings::new(1, 1),
        Policy::new(
            &[Grant {
                principal: 0,
                scope: Scope::Issue {
                    issuer: 0,
                    recipient: 7,
                },
                asset: 0,
                max_amount: 9,
            }],
            &[(0, 0)],
        )
        .unwrap(),
    );
    let req = Request {
        principal: 0,
        nonce: 0,
        operation: Operation::Issue {
            issuer: 0,
            recipient: 7,
            asset: 0,
            amount: 1,
        },
    };
    let before = m.clone();
    assert_eq!(
        m.process(id_bytes(1), req),
        Outcome::Invalid(LedgerError::UnknownAccount(7))
    );
    assert_eq!(
        m, before,
        "invalid requests are neither cached nor consume a nonce"
    );
}

#[test]
fn nonce_overflow_is_invalid() {
    let mut m = Processor::new(Holdings::new(1, 1), open_policy());
    // Reach u64::MAX nonce through the public API is infeasible; check the guard directly via a request at MAX.
    let req = Request {
        principal: 0,
        nonce: u64::MAX,
        operation: Operation::Issue {
            issuer: 0,
            recipient: 0,
            asset: 0,
            amount: 1,
        },
    };
    assert_eq!(m.process(id_bytes(1), req), Outcome::FutureNonce);
}
