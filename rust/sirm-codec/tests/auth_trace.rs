//! Differential test against `scripts/auth_reference_trace.py`: 3000 seeded operations
//! by three principals under a random static grant/control registry.

use serde_json::Value;
use sirm_codec::auth::*;
use sirm_codec::ledger::*;

fn u(v: &Value) -> u128 {
    v.as_str().unwrap().parse().unwrap()
}

fn doc() -> Value {
    serde_json::from_str(include_str!(
        "../../../engineering/ledger_core/results/auth_trace_v0.json"
    ))
    .unwrap()
}

fn build_policy(t: &Value) -> Policy {
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
                "burn" => Scope::Burn { holder: a },
                other => panic!("scope {other}"),
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
    Policy::new(&grants, &control).expect("trace registry has no conflicting grants")
}

#[test]
fn replay_trace_matches_python_reference() {
    let d = doc();
    let t = &d["trace"];
    let policy = build_policy(t);
    let (accounts, assets) = (
        t["accounts"].as_u64().unwrap() as u32,
        t["assets"].as_u64().unwrap() as u32,
    );
    let outcomes = t["outcomes"].as_str().unwrap().as_bytes();
    let mut ledger = Holdings::new(accounts, assets);
    let (mut ok, mut unauth, mut insufficient) = (0, 0, 0);
    for (i, op) in t["ops"].as_array().unwrap().iter().enumerate() {
        let n = |k: usize| op[k].as_u64().unwrap() as u32;
        let (p, a, asset, amt) = (n(0), n(2), n(4), u(&op[5]));
        let before = ledger.clone();
        let res = match op[1].as_str().unwrap() {
            "transfer" => policy.transfer(&mut ledger, p, a, n(3), asset, amt),
            "issue" => policy.issue(&mut ledger, p, a, n(3), asset, amt),
            "burn" => policy.burn(&mut ledger, p, a, asset, amt),
            other => panic!("op {other}"),
        };
        let got = match res {
            Ok(()) => {
                ok += 1;
                b'o'
            }
            Err(AuthError::Unauthorized) => {
                unauth += 1;
                b'u'
            }
            Err(AuthError::Ledger(LedgerError::Insufficient)) => {
                insufficient += 1;
                b'i'
            }
            Err(e) => panic!("op {i}: unexpected {e:?}"),
        };
        assert_eq!(got, outcomes[i], "op {i}: {op}");
        if got != b'o' {
            assert_eq!(ledger, before, "rejected op {i} changed state");
        }
        assert!(ledger.invariant(), "invariant broken after op {i}");
    }
    assert!(
        ok > 1000 && unauth > 1000 && insufficient > 100,
        "trace lacks coverage: {ok}/{unauth}/{insufficient}"
    );
    for acc in 0..accounts {
        for s in 0..assets {
            assert_eq!(
                ledger.balance(acc, s),
                u(&t["final"]["balances"][acc as usize][s as usize])
            );
        }
    }
    for s in 0..assets {
        let sup = ledger.supply(s);
        let e = &t["final"]["supply"][s as usize];
        assert_eq!(
            (sup.minted, sup.burned, sup.outstanding),
            (u(&e[0]), u(&e[1]), u(&e[2]))
        );
    }
}

#[test]
fn registry_uniqueness_matches_lean() {
    let g = |max| Grant {
        principal: 0,
        scope: Scope::Burn { holder: 1 },
        asset: 0,
        max_amount: max,
    };
    assert!(
        Policy::new(&[g(5), g(5)], &[]).is_ok(),
        "identical duplicates are allowed"
    );
    assert_eq!(
        Policy::new(&[g(5), g(6)], &[]),
        Err(RegistryError::ConflictingGrant)
    );
}

#[test]
fn authorization_needs_control_and_exact_directional_grant() {
    let grants = [Grant {
        principal: 0,
        scope: Scope::Transfer {
            source: 0,
            destination: 1,
        },
        asset: 0,
        max_amount: 10,
    }];
    let mut ledger = Holdings::new(2, 1);
    let open = Policy::new(
        &[
            grants[0],
            Grant {
                principal: 0,
                scope: Scope::Issue {
                    issuer: 0,
                    recipient: 1,
                },
                asset: 0,
                max_amount: 100,
            },
        ],
        &[(0, 0)],
    )
    .unwrap();
    // Issuer control only; the recipient (account 1) need not be controlled.
    assert_eq!(open.issue(&mut ledger, 0, 0, 1, 0, 50), Ok(()));
    assert_eq!(ledger.balance(1, 0), 50);
    // Control of the source is missing for account 1 -> unauthorized, nothing changes.
    let before = ledger.clone();
    assert_eq!(
        open.transfer(&mut ledger, 0, 1, 0, 0, 1),
        Err(AuthError::Unauthorized)
    );
    assert_eq!(ledger, before);
    // Direction matters: the grant covers 0 -> 1 only.
    assert_eq!(
        open.transfer(&mut ledger, 0, 0, 1, 0, 1),
        Err(AuthError::Ledger(LedgerError::Insufficient))
    );
    // Amount downward closure: a grant for 10 permits 0..=10, not 11.
    assert!(open.allows(
        0,
        Scope::Transfer {
            source: 0,
            destination: 1
        },
        0,
        0
    ));
    assert!(open.allows(
        0,
        Scope::Transfer {
            source: 0,
            destination: 1
        },
        0,
        10
    ));
    assert!(!open.allows(
        0,
        Scope::Transfer {
            source: 0,
            destination: 1
        },
        0,
        11
    ));
    // Wrong asset or wrong principal.
    assert!(!open.allows(
        0,
        Scope::Transfer {
            source: 0,
            destination: 1
        },
        1,
        1
    ));
    assert!(!open.allows(
        1,
        Scope::Transfer {
            source: 0,
            destination: 1
        },
        0,
        1
    ));
}
