//! Differential test against `scripts/registry_gate_reference_trace.py`: 24 random typed
//! registries (statuses, classes, networks) x 500 operations through the registry-aware
//! policy, plus `10^decimals` vectors and registry well-formedness checks.

use serde_json::Value;
use sirm_codec::auth::*;
use sirm_codec::ledger::*;
use sirm_codec::registry::*;

fn u(v: &Value) -> u128 {
    v.as_str().unwrap().parse().unwrap()
}

fn class(s: &str) -> AccountClass {
    use AccountClass::*;
    match s {
        "holder" => Holder,
        "treasury" => Treasury,
        "validatorPool" => ValidatorPool,
        "ecosystemPool" => EcosystemPool,
        "communityPool" => CommunityPool,
        "unallocatedPool" => UnallocatedPool,
        "control" => Control,
        "custody" => Custody,
        "reserve" => Reserve,
        "customerLiability" => CustomerLiability,
        "equity" => Equity,
        "income" => Income,
        "expense" => Expense,
        "fee" => Fee,
        "escrow" => Escrow,
        "clearing" => Clearing,
        other => panic!("class {other}"),
    }
}

fn registry(ep: &Value) -> Registry {
    let accounts = ep["accounts"]
        .as_array()
        .unwrap()
        .iter()
        .map(|a| AccountMeta {
            class: class(a[0].as_str().unwrap()),
            status: match a[1].as_str().unwrap() {
                "active" => AccountStatus::Active,
                "frozen" => AccountStatus::Frozen,
                "closed" => AccountStatus::Closed,
                o => panic!("{o}"),
            },
            network: Network(a[2].as_u64().unwrap() as u32),
        })
        .collect();
    let assets = ep["assets"]
        .as_array()
        .unwrap()
        .iter()
        .map(|a| AssetMeta {
            symbol: a[0].as_str().unwrap().to_string(),
            decimals: a[1].as_u64().unwrap() as u32,
            issuer: a[2].as_u64().unwrap() as u32,
            status: match a[3].as_str().unwrap() {
                "draft" => AssetStatus::Draft,
                "active" => AssetStatus::Active,
                "frozen" => AssetStatus::Frozen,
                "retired" => AssetStatus::Retired,
                o => panic!("{o}"),
            },
            network: Network(a[4].as_u64().unwrap() as u32),
        })
        .collect();
    Registry::new(accounts, assets).expect("trace registries are well formed")
}

fn base_policy(ep: &Value) -> Policy {
    let grants: Vec<Grant> = ep["grants"]
        .as_array()
        .unwrap()
        .iter()
        .map(|g| {
            let a = g[2].as_u64().unwrap() as u32;
            let b = g[3].as_u64().map(|x| x as u32);
            let scope = match g[1].as_str().unwrap() {
                "transfer" => Scope::Transfer {
                    source: a,
                    destination: b.unwrap(),
                },
                "issue" => Scope::Issue {
                    issuer: a,
                    recipient: b.unwrap(),
                },
                "burn" => Scope::Burn { holder: a },
                o => panic!("{o}"),
            };
            Grant {
                principal: g[0].as_u64().unwrap() as u32,
                scope,
                asset: g[4].as_u64().unwrap() as u32,
                max_amount: u(&g[5]),
            }
        })
        .collect();
    let control: Vec<(u32, u32)> = ep["control"]
        .as_array()
        .unwrap()
        .iter()
        .map(|c| (c[0].as_u64().unwrap() as u32, c[1].as_u64().unwrap() as u32))
        .collect();
    Policy::new(&grants, &control).unwrap()
}

#[test]
fn replay_episodes_match_python_reference() {
    let d: Value = serde_json::from_str(include_str!(
        "../../../engineering/ledger_core/results/registry_gate_trace_v0.json"
    ))
    .unwrap();
    let (accounts, assets) = (
        d["accounts"].as_u64().unwrap() as u32,
        d["assets"].as_u64().unwrap() as u32,
    );
    let (mut gated, mut ok, mut en, mut dis) = (0usize, 0usize, 0usize, 0usize);
    for (ei, ep) in d["episodes"].as_array().unwrap().iter().enumerate() {
        let reg = registry(ep);
        for s in 0..assets {
            let want = ep["enabled"][s as usize].as_bool().unwrap();
            assert_eq!(reg.issuance_enabled(s), want, "episode {ei} asset {s}");
            if want {
                en += 1
            } else {
                dis += 1
            }
        }
        let base = base_policy(ep);
        let gp = GatedPolicy::new(base.clone(), reg);
        let outcomes = ep["outcomes"].as_str().unwrap().as_bytes();
        let mut led = Holdings::new(accounts, assets);
        for (i, op) in ep["ops"].as_array().unwrap().iter().enumerate() {
            let n = |k: usize| op[k].as_u64().unwrap() as u32;
            let (p, a, asset, amt) = (n(0), n(2), n(4), u(&op[5]));
            let before = led.clone();
            let res = match op[1].as_str().unwrap() {
                "transfer" => gp.transfer(&mut led, p, a, n(3), asset, amt),
                "issue" => gp.issue(&mut led, p, a, n(3), asset, amt),
                "burn" => gp.burn(&mut led, p, a, asset, amt),
                o => panic!("{o}"),
            };
            let got = match res {
                Ok(()) => b'o',
                Err(AuthError::Ledger(LedgerError::Insufficient)) => b'i',
                Err(AuthError::Unauthorized) => {
                    // gate-only denial: the base policy allows this issue, the registry does not
                    let gate_only = op[1] == "issue"
                        && base.may_issue(p, a, n(3), asset, amt)
                        && !gp.registry().issuance_enabled(asset);
                    if gate_only {
                        b'g'
                    } else {
                        b'u'
                    }
                }
                Err(e) => panic!("episode {ei} op {i}: unexpected {e:?}"),
            };
            assert_eq!(got, outcomes[i], "episode {ei} op {i}: {op}");
            if got == b'g' {
                gated += 1;
            }
            if got == b'o' {
                ok += 1;
            }
            if got != b'o' {
                assert_eq!(
                    led, before,
                    "rejected op changed state, episode {ei} op {i}"
                );
            }
            assert!(led.invariant(), "invariant, episode {ei} op {i}");
        }
        for acc in 0..accounts {
            for s in 0..assets {
                assert_eq!(
                    led.balance(acc, s),
                    u(&ep["final"]["balances"][acc as usize][s as usize]),
                    "episode {ei} account {acc} asset {s}"
                );
            }
        }
    }
    assert!(
        gated > 500 && ok > 1000,
        "weak coverage: gated {gated}, ok {ok}"
    );
    assert!(
        en > 0 && dis > 0,
        "both enabled and disabled assets needed: {en}/{dis}"
    );
}

#[test]
fn base_units_per_whole_matches_reference_and_respects_u128() {
    let d: Value = serde_json::from_str(include_str!(
        "../../../engineering/ledger_core/results/registry_gate_trace_v0.json"
    ))
    .unwrap();
    for (dec, want) in d["base_units"].as_object().unwrap() {
        let meta = AssetMeta {
            symbol: "X".into(),
            decimals: dec.parse().unwrap(),
            issuer: 0,
            status: AssetStatus::Active,
            network: Network(0),
        };
        let expected = want.as_str().map(|s| s.parse::<u128>().unwrap());
        assert_eq!(meta.base_units_per_whole(), expected, "decimals {dec}");
    }
}

fn acc(status: AccountStatus, net: u32) -> AccountMeta {
    AccountMeta {
        class: AccountClass::Holder,
        status,
        network: Network(net),
    }
}

fn asset(issuer: u32, status: AssetStatus, net: u32) -> AssetMeta {
    AssetMeta {
        symbol: "A".into(),
        decimals: 6,
        issuer,
        status,
        network: Network(net),
    }
}

#[test]
fn registry_rejects_unknown_issuer_and_network_mismatch() {
    let accounts = vec![acc(AccountStatus::Active, 1)];
    assert_eq!(
        Registry::new(accounts.clone(), vec![asset(3, AssetStatus::Active, 1)]),
        Err(TypedRegistryError::IssuerOutOfRange(0))
    );
    assert_eq!(
        Registry::new(accounts.clone(), vec![asset(0, AssetStatus::Active, 2)]),
        Err(TypedRegistryError::IssuerNetworkMismatch(0))
    );
    assert!(Registry::new(accounts, vec![asset(0, AssetStatus::Active, 1)]).is_ok());
}

#[test]
fn issuance_needs_active_asset_and_active_issuer_but_not_transfer_or_burn() {
    let reg = |ast, ac| {
        Registry::new(
            vec![acc(ac, 0), acc(AccountStatus::Active, 0)],
            vec![asset(0, ast, 0)],
        )
        .unwrap()
    };
    assert!(reg(AssetStatus::Active, AccountStatus::Active).issuance_enabled(0));
    for ast in [
        AssetStatus::Draft,
        AssetStatus::Frozen,
        AssetStatus::Retired,
    ] {
        assert!(!reg(ast, AccountStatus::Active).issuance_enabled(0));
    }
    for ac in [AccountStatus::Frozen, AccountStatus::Closed] {
        assert!(!reg(AssetStatus::Active, ac).issuance_enabled(0));
    }
    assert!(!reg(AssetStatus::Active, AccountStatus::Active).issuance_enabled(7));
    // Frozen asset: issue is gated, transfer and burn follow the base policy only.
    let grants = [
        Grant {
            principal: 0,
            scope: Scope::Issue {
                issuer: 0,
                recipient: 1,
            },
            asset: 0,
            max_amount: 100,
        },
        Grant {
            principal: 0,
            scope: Scope::Transfer {
                source: 1,
                destination: 0,
            },
            asset: 0,
            max_amount: 100,
        },
        Grant {
            principal: 0,
            scope: Scope::Burn { holder: 1 },
            asset: 0,
            max_amount: 100,
        },
    ];
    let base = Policy::new(&grants, &[(0, 0), (0, 1)]).unwrap();
    let gp = GatedPolicy::new(base, reg(AssetStatus::Frozen, AccountStatus::Active));
    let mut led = Holdings::new(2, 1);
    assert_eq!(
        gp.issue(&mut led, 0, 0, 1, 0, 10),
        Err(AuthError::Unauthorized)
    );
    led.issue(1, 0, 10).unwrap();
    assert_eq!(gp.transfer(&mut led, 0, 1, 0, 0, 4), Ok(()));
    assert_eq!(gp.burn(&mut led, 0, 1, 0, 6), Ok(()));
    assert_eq!((led.balance(0, 0), led.balance(1, 0)), (4, 0));
}
