//! Differential test against the independent Python reference
//! (`scripts/integrated_machine_reference.py`): 402 episodes (two at the u128 boundary) of the
//! integrated state machine, outcome by outcome and final state, with the invariants checked after
//! every step; plus the old integrated processor trace replayed through the new machine.

use serde_json::Value;
use sirm_codec::escrow::Phase;
use sirm_codec::integrated::*;

fn num(v: &Value) -> u128 {
    match v {
        Value::String(s) => s.parse().unwrap(),
        other => other.as_u64().unwrap() as u128,
    }
}

fn kind(s: &str) -> Kind {
    match s {
        "transfer" => Kind::Transfer,
        "issue" => Kind::Issue,
        "burn" => Kind::Burn,
        "open" => Kind::Open,
        "release" => Kind::Release,
        "cancel" => Kind::Cancel,
        "expire" => Kind::Expire,
        "dispute" => Kind::Dispute,
        "advance" => Kind::Advance,
        "migrate" => Kind::Migrate,
        other => panic!("kind {other}"),
    }
}

fn request(row: &[Value]) -> (u64, Request) {
    let n = |k: usize| num(&row[k]) as u32;
    let op = match row[3].as_str().unwrap() {
        "transfer" => Op::Transfer {
            src: n(4),
            dst: n(5),
            asset: n(6),
            amount: num(&row[7]),
        },
        "issue" => Op::Issue {
            issuer: n(4),
            recipient: n(5),
            asset: n(6),
            amount: num(&row[7]),
        },
        "burn" => Op::Burn {
            holder: n(4),
            asset: n(6),
            amount: num(&row[7]),
        },
        "open" => Op::Open {
            id: num(&row[4]) as usize,
            depositor: n(5),
            beneficiary: n(6),
            asset: n(7),
            amount: num(&row[8]),
        },
        "release" => Op::Release(num(&row[4]) as usize),
        "cancel" => Op::Cancel(num(&row[4]) as usize),
        "expire" => Op::Expire(num(&row[4]) as usize),
        "dispute" => Op::Dispute {
            id: num(&row[4]) as usize,
            claimant: n(5),
        },
        "advance" => Op::Advance(num(&row[4]) as u64),
        "migrate" => Op::Migrate(num(&row[4])),
        other => panic!("op {other}"),
    };
    (
        num(&row[0]) as u64,
        Request {
            principal: n(1),
            nonce: num(&row[2]) as u64,
            op,
        },
    )
}

fn limit_key(g: &[Value]) -> (u32, Kind, u32, Option<u32>, u32) {
    (
        num(&g[0]) as u32,
        kind(g[1].as_str().unwrap()),
        num(&g[2]) as u32,
        if g[3].is_null() {
            None
        } else {
            Some(num(&g[3]) as u32)
        },
        num(&g[4]) as u32,
    )
}

fn phase(s: &str) -> Phase {
    match s {
        "pending" => Phase::Pending,
        "released" => Phase::Released,
        "cancelled" => Phase::Cancelled,
        "expired" => Phase::Expired,
        other => panic!("phase {other}"),
    }
}

fn check_final(m: &Machine, f: &Value, accounts: u32, assets: u32, ctx: &str) {
    for a in 0..accounts {
        for s in 0..assets {
            assert_eq!(
                m.ledger.balance(a, s),
                num(&f["balances"][a as usize][s as usize]),
                "{ctx} balance {a},{s}"
            );
        }
    }
    for s in 0..assets {
        let sup = m.ledger.supply(s);
        let want = &f["supply"][s as usize];
        assert_eq!(
            (sup.minted, sup.burned, sup.outstanding),
            (num(&want[0]), num(&want[1]), num(&want[2])),
            "{ctx} supply {s}"
        );
    }
    for (p, n) in f["nonces"].as_array().unwrap().iter().enumerate() {
        assert_eq!(m.nonce(p as u32), n.as_u64().unwrap(), "{ctx} nonce {p}");
    }
    assert_eq!(m.now(), f["now"].as_u64().unwrap(), "{ctx} now");
    assert_eq!(
        m.cached() as u64,
        f["receipts"].as_u64().unwrap(),
        "{ctx} receipts"
    );
}

#[test]
fn episodes_match_python_reference() {
    let d: Value = serde_json::from_str(include_str!(
        "../../../engineering/ledger_core/results/integrated_trace_v0.json"
    ))
    .unwrap();
    let (accounts, assets) = (
        d["accounts"].as_u64().unwrap() as u32,
        d["assets"].as_u64().unwrap() as u32,
    );
    let mut denial_codes = std::collections::BTreeSet::new();
    let mut accepted = 0usize;
    for (ei, ep) in d["episodes"].as_array().unwrap().iter().enumerate() {
        let pol = &ep["policy"];
        let mut policy = Policy::default();
        for c in pol["control"].as_array().unwrap() {
            policy
                .controls
                .insert((num(&c[0]) as u32, num(&c[1]) as u32));
        }
        for g in pol["limits"].as_array().unwrap() {
            policy
                .limits
                .insert(limit_key(g.as_array().unwrap()), num(&g[5]));
        }
        for i in pol["ids"].as_array().unwrap() {
            policy.ids.insert((
                num(&i[0]) as u32,
                kind(i[1].as_str().unwrap()),
                num(&i[2]) as usize,
            ));
        }
        for c in pol["clock"].as_array().unwrap() {
            policy.clock.insert(num(c) as u32);
        }
        let mg = &ep["migration"];
        let mut m = Machine::new(Config {
            accounts,
            assets,
            vault: Some(ep["vault"].as_u64().unwrap() as u32),
            deadlines: ep["deadlines"]
                .as_array()
                .unwrap()
                .iter()
                .map(|v| v.as_u64().unwrap())
                .collect(),
            now: ep["start_now"].as_u64().unwrap(),
            migration: Some(MigrationConfig {
                holder: num(&mg["holder"]) as u32,
                recipient: num(&mg["recipient"]) as u32,
                src: num(&mg["src"]) as u32,
                dst: num(&mg["dst"]) as u32,
                num: num(&mg["num"]),
                den: num(&mg["den"]),
            }),
            policy,
        })
        .expect("valid configuration");
        for (i, (row, tok)) in ep["requests"]
            .as_array()
            .unwrap()
            .iter()
            .zip(ep["tokens"].as_array().unwrap())
            .enumerate()
        {
            let (id, req) = request(row.as_array().unwrap());
            let before = m.snapshot();
            let out = m.process(id, req);
            assert_eq!(
                out.token(),
                tok.as_str().unwrap(),
                "episode {ei} request {i}: {row}"
            );
            if let Outcome::Done(Stored::Denied { denial, .. }) = out {
                denial_codes.insert(denial.code());
            }
            if matches!(out, Outcome::Done(Stored::Accepted { .. })) {
                accepted += 1;
            } else {
                assert_eq!(
                    m.snapshot(),
                    before,
                    "rejected request changed state, episode {ei} request {i}"
                );
            }
            assert!(m.invariant(), "invariant broken, episode {ei} request {i}");
        }
        let f = &ep["final"];
        check_final(&m, f, accounts, assets, &format!("episode {ei}"));
        for (id, rec) in f["records"].as_array().unwrap().iter().enumerate() {
            match (m.record(id), rec.as_array()) {
                (None, None) => {}
                (Some(r), Some(w)) => assert_eq!(
                    (r.depositor, r.beneficiary, r.asset, r.amount, r.phase),
                    (
                        num(&w[0]) as u32,
                        num(&w[1]) as u32,
                        num(&w[2]) as u32,
                        num(&w[3]),
                        phase(w[4].as_str().unwrap())
                    ),
                    "episode {ei} record {id}"
                ),
                other => panic!("episode {ei} record {id}: {other:?}"),
            }
        }
        for (id, fl) in f["filings"].as_array().unwrap().iter().enumerate() {
            match (m.filing(id), fl.as_array()) {
                (None, None) => {}
                (Some(x), Some(w)) => assert_eq!(
                    (x.principal, x.claimant, x.filed_at),
                    (num(&w[0]) as u32, num(&w[1]) as u32, w[2].as_u64().unwrap()),
                    "episode {ei} filing {id}"
                ),
                other => panic!("episode {ei} filing {id}: {other:?}"),
            }
        }
        let t = &f["migration"];
        assert_eq!(
            m.migration_totals(),
            (
                num(&t["total_source"]),
                num(&t["total_target"]),
                num(&t["dust"])
            ),
            "episode {ei} migration"
        );
    }
    assert!(accepted > 4000, "weak coverage: {accepted}");
    for must in [
        "issue:v",
        "migrate:v",
        "transfer:r",
        "burn:r",
        "issue:r",
        "open:v",
        "dispute:a",
        "dispute:auth",
        "expire:e",
    ] {
        assert!(denial_codes.contains(must), "denial {must} not exercised");
    }
}

#[test]
fn old_processor_trace_is_a_special_case() {
    let d: Value = serde_json::from_str(include_str!(
        "../../../engineering/ledger_core/results/machine_trace_v0.json"
    ))
    .unwrap();
    let t = &d["trace"];
    let (accounts, assets) = (
        t["accounts"].as_u64().unwrap() as u32,
        t["assets"].as_u64().unwrap() as u32,
    );
    let mut policy = Policy::default();
    for c in t["control"].as_array().unwrap() {
        policy
            .controls
            .insert((num(&c[0]) as u32, num(&c[1]) as u32));
    }
    for g in t["grants"].as_array().unwrap() {
        policy
            .limits
            .insert(limit_key(g.as_array().unwrap()), num(&g[5]));
    }
    let mut m = Machine::new(Config {
        accounts,
        assets,
        vault: None,
        deadlines: vec![],
        now: 0,
        migration: None,
        policy,
    })
    .unwrap();
    for (i, (row, tok)) in t["requests"]
        .as_array()
        .unwrap()
        .iter()
        .zip(t["tokens"].as_array().unwrap())
        .enumerate()
    {
        let (id, req) = request(row.as_array().unwrap());
        assert_eq!(
            m.process(id, req).token(),
            tok.as_str().unwrap(),
            "request {i}"
        );
        assert!(m.invariant());
    }
    assert_eq!(m.cached() as u64, t["receipts"].as_u64().unwrap());
    for a in 0..accounts {
        for s in 0..assets {
            assert_eq!(
                m.ledger.balance(a, s),
                num(&t["final"]["balances"][a as usize][s as usize])
            );
        }
    }
    for (p, n) in t["final_nonces"].as_array().unwrap().iter().enumerate() {
        assert_eq!(m.nonce(p as u32), n.as_u64().unwrap());
    }
}

#[test]
fn degenerate_migration_and_vault_use_are_rejected_at_construction() {
    let base = |migration| Config {
        accounts: 4,
        assets: 2,
        vault: Some(3),
        deadlines: vec![5],
        now: 0,
        migration,
        policy: Policy::default(),
    };
    let ok = MigrationConfig {
        holder: 0,
        recipient: 1,
        src: 0,
        dst: 1,
        num: 1,
        den: 1,
    };
    assert!(Machine::new(base(Some(ok))).is_some());
    assert!(Machine::new(base(Some(MigrationConfig { num: 0, ..ok }))).is_none());
    assert!(Machine::new(base(Some(MigrationConfig { den: 0, ..ok }))).is_none());
    assert!(Machine::new(base(Some(MigrationConfig { dst: 0, ..ok }))).is_none());
    assert!(Machine::new(base(Some(MigrationConfig { holder: 3, ..ok }))).is_none());
    assert!(Machine::new(base(Some(MigrationConfig { recipient: 3, ..ok }))).is_none());
}
