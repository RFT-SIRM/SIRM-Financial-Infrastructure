//! Differential test of the arbiter operation `resolve` against the independent Python reference
//! (`scripts/integrated_resolve_reference_trace.py`): 300 episodes of the integrated state machine in
//! which a disputed escrow can be settled to the beneficiary or the depositor, outcome by outcome and
//! final state, with the invariants checked after every step and a rejected request required to leave
//! the state unchanged. The base trace (`integrated_trace.rs`) is not affected by `resolve`.

use serde_json::Value;
use sirm_codec::escrow::Phase;
use sirm_codec::integrated::*;

include!("support/integrated_load.rs");

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
fn resolve_episodes_match_python_reference() {
    let d: Value = serde_json::from_str(include_str!(
        "../../../engineering/ledger_core/results/integrated_resolve_trace_v0.json"
    ))
    .unwrap();
    let (accounts, assets) = (
        d["accounts"].as_u64().unwrap() as u32,
        d["assets"].as_u64().unwrap() as u32,
    );
    let mut denial_codes = std::collections::BTreeSet::new();
    let mut accepted = 0usize;
    for (ei, ep) in d["episodes"].as_array().unwrap().iter().enumerate() {
        let mut m = machine_for(ep, accounts, assets);
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
    assert!(accepted > 2500, "weak coverage: {accepted}");
    for must in [
        "resolve:auth",
        "resolve:w",
        "resolve:n",
        "resolve:o",
        "release:x",
        "cancel:x",
        "expire:x",
    ] {
        assert!(denial_codes.contains(must), "denial {must} not exercised");
    }
}

#[test]
fn resolve_has_no_wire_encoding_yet() {
    use sirm_codec::request_v1::{encode, EncodeError, WireRequest};
    let w = WireRequest {
        request_id: [7u8; 32],
        request: Request {
            principal: 0,
            nonce: 0,
            op: Op::Resolve {
                id: 0,
                to_beneficiary: true,
            },
        },
    };
    assert_eq!(encode(&w), Err(EncodeError::UnsupportedOperation));
}

#[test]
fn state_root_is_none_exactly_when_a_resolve_was_cached() {
    use sirm_codec::commit_v5::state_root_v5;
    let d: Value = serde_json::from_str(include_str!(
        "../../../engineering/ledger_core/results/integrated_resolve_trace_v0.json"
    ))
    .unwrap();
    let (accounts, assets) = (
        d["accounts"].as_u64().unwrap() as u32,
        d["assets"].as_u64().unwrap() as u32,
    );
    let (mut some_roots, mut none_roots) = (0, 0);
    for ep in d["episodes"].as_array().unwrap() {
        let mut m = machine_for(ep, accounts, assets);
        let mut saw = false;
        assert!(state_root_v5(&m).is_some(), "empty cache has a root");
        for (k, row) in ep["requests"].as_array().unwrap().iter().enumerate() {
            // only accepted and denied requests enter the cache (stale and future nonces do not)
            let tok = ep["tokens"][k].as_str().unwrap();
            saw |= row[3].as_str() == Some("resolve")
                && (tok.starts_with('A') || tok.starts_with('N'));
            let (id, req) = request(row.as_array().unwrap());
            m.process(id, req);
            if k < 12 {
                assert_eq!(state_root_v5(&m).is_none(), saw, "episode request {k}");
                if saw {
                    none_roots += 1;
                } else {
                    some_roots += 1;
                }
            }
        }
        assert_eq!(state_root_v5(&m).is_none(), saw);
    }
    assert!(
        some_roots > 100 && none_roots > 100,
        "weak: {some_roots} {none_roots}"
    );
}
