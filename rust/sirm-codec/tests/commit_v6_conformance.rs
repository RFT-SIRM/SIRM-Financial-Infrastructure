//! Conformance of the Rust state commitment v6 (v5 plus `resolve`) with the independent Python
//! reference: the final state of each of the 402 integrated episodes and of the 300 episodes of the
//! resolve trace (replayed in Rust) commits to the same root, the components of a rich example of each
//! agree, a cached `resolve` request is bound into the root, and further requests change the root.
#![allow(dead_code)]

use serde_json::Value;
use sha2::{Digest, Sha256};
use sirm_codec::commit_v6::*;
use sirm_codec::escrow::Phase;
use sirm_codec::integrated::*;

include!("support/integrated_load.rs");

fn hexs(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

fn vectors() -> Value {
    serde_json::from_str(include_str!(
        "../../../engineering/canonical_encoding/results/state_commitment_v6_vectors.json"
    ))
    .unwrap()
}

fn trace(resolve: bool) -> Value {
    if resolve {
        serde_json::from_str(include_str!(
            "../../../engineering/ledger_core/results/integrated_resolve_trace_v0.json"
        ))
        .unwrap()
    } else {
        serde_json::from_str(include_str!(
            "../../../engineering/ledger_core/results/integrated_trace_v0.json"
        ))
        .unwrap()
    }
}

fn doc(resolve: bool) -> (Value, Value) {
    (
        trace(resolve),
        vectors()[if resolve { "resolve" } else { "base" }].clone(),
    )
}

fn replay(ep: &Value, accounts: u32, assets: u32) -> Machine {
    let mut m = machine_for(ep, accounts, assets);
    for row in ep["requests"].as_array().unwrap() {
        let (id, r) = request(row.as_array().unwrap());
        m.process(id, r);
    }
    m
}

fn roots_match(resolve: bool) {
    let (d, v) = doc(resolve);
    let (accounts, assets) = (
        d["accounts"].as_u64().unwrap() as u32,
        d["assets"].as_u64().unwrap() as u32,
    );
    let want = v["roots"].as_array().unwrap();
    let eps = d["episodes"].as_array().unwrap();
    assert_eq!(want.len(), eps.len());
    let mut agg = Sha256::new();
    let mut seen = std::collections::BTreeSet::new();
    for (i, ep) in eps.iter().enumerate() {
        let m = replay(ep, accounts, assets);
        let r = state_root_v6(&m).unwrap();
        assert_eq!(hexs(&r), want[i].as_str().unwrap(), "episode {i}");
        agg.update(r);
        seen.insert(r);
    }
    assert_eq!(seen.len(), eps.len());
    assert_eq!(
        hexs(&agg.finalize()),
        v["roots_aggregate_sha256"].as_str().unwrap()
    );
}

#[test]
fn all_base_episode_roots_match_the_python_reference() {
    roots_match(false);
}

#[test]
fn all_resolve_episode_roots_match_the_python_reference() {
    roots_match(true);
}

fn components_match(resolve: bool) -> Machine {
    let (d, v) = doc(resolve);
    let ex = v["example_episode"].as_u64().unwrap() as usize;
    let m = replay(
        &d["episodes"][ex],
        d["accounts"].as_u64().unwrap() as u32,
        d["assets"].as_u64().unwrap() as u32,
    );
    let e = &v["example"];
    let (b, s, n) = trees(&m);
    assert_eq!(hexs(&b), e["balance_root"].as_str().unwrap());
    assert_eq!(hexs(&s), e["supply_root"].as_str().unwrap());
    assert_eq!(hexs(&n), e["nonce_root"].as_str().unwrap());
    assert_eq!(
        hexs(&config_commit(&m).unwrap()),
        e["config"].as_str().unwrap()
    );
    assert_eq!(
        hexs(&cache_commit(&m).unwrap()),
        e["cache"].as_str().unwrap()
    );
    assert_eq!(hexs(&escrow_commit(&m)), e["escrow"].as_str().unwrap());
    assert_eq!(
        hexs(&state_root_v6(&m).unwrap()),
        e["root"].as_str().unwrap()
    );
    assert!(m.migration_totals().2 > 0 && m.nonces().len() >= 2);
    m
}

#[test]
fn base_example_components_match() {
    let m = components_match(false);
    assert!((0..m.config().deadlines.len()).any(|i| m.filing(i).is_some()));
    assert!((0..m.config().deadlines.len())
        .any(|i| m.record(i).is_some_and(|r| r.phase != Phase::Pending)));
}

#[test]
fn resolve_example_components_match_and_the_root_binds_the_cached_resolve() {
    let m = components_match(true);
    // the example has a settled record, and the cache holds an accepted resolve request
    assert!((0..m.config().deadlines.len())
        .any(|i| m.record(i).is_some_and(|r| r.phase != Phase::Pending)));
    let resolves: Vec<_> = m
        .cache_entries()
        .filter(|(_, req, st)| {
            matches!(req.op, Op::Resolve { .. }) && matches!(st, Stored::Accepted { .. })
        })
        .collect();
    assert!(!resolves.is_empty());
    // the root is defined (v5 has none for such a machine) and differs from every variant: the
    // variants are checked in Python; here the cache commitment must exist and change with the entry
    assert!(cache_commit(&m).is_some());
}

#[test]
fn every_further_request_changes_the_root() {
    // accepted, denied and replayed requests each change the committed state (cache or ledger)
    let d = trace(false);
    let (accounts, assets) = (
        d["accounts"].as_u64().unwrap() as u32,
        d["assets"].as_u64().unwrap() as u32,
    );
    let ep = &d["episodes"][5];
    let mut m = machine_for(ep, accounts, assets);
    let mut prev = state_root_v6(&m).unwrap();
    let mut changed = 0;
    for row in ep["requests"].as_array().unwrap() {
        let (id, r) = request(row.as_array().unwrap());
        let out = m.process(id, r);
        let now = state_root_v6(&m).unwrap();
        let t = out.token();
        // stale and future requests and replays are not cached and leave the state alone
        if matches!(t.chars().next(), Some('A') | Some('N')) {
            assert_ne!(now, prev, "{t}");
            changed += 1;
        } else {
            assert_eq!(now, prev, "{t}");
        }
        prev = now;
    }
    assert!(changed > 20);
}

#[test]
fn every_resolve_request_changes_the_root_and_a_rejected_one_only_the_cache() {
    let d = trace(true);
    let (accounts, assets) = (
        d["accounts"].as_u64().unwrap() as u32,
        d["assets"].as_u64().unwrap() as u32,
    );
    let (mut accepted, mut denied) = (0, 0);
    for ep in d["episodes"].as_array().unwrap().iter().take(40) {
        let mut m = machine_for(ep, accounts, assets);
        let mut prev = state_root_v6(&m).unwrap();
        for row in ep["requests"].as_array().unwrap() {
            let (id, r) = request(row.as_array().unwrap());
            let is_resolve = matches!(r.op, Op::Resolve { .. });
            let snap = m.snapshot();
            let out = m.process(id, r);
            let now = state_root_v6(&m).unwrap();
            let t = out.token();
            if matches!(t.chars().next(), Some('A') | Some('N')) {
                assert_ne!(now, prev, "{t}");
                if is_resolve {
                    if t.starts_with('A') {
                        accepted += 1;
                    } else {
                        denied += 1;
                        // a denied resolve changes the cache (a receipt) but not the ledger state
                        let after = m.snapshot();
                        assert_eq!(after.ledger, snap.ledger);
                        assert_eq!(after.records, snap.records);
                        assert_eq!(after.filings, snap.filings);
                        assert_eq!(after.now, snap.now);
                        assert_eq!(after.migration, snap.migration);
                    }
                }
            } else {
                assert_eq!(now, prev, "{t}");
            }
            prev = now;
        }
    }
    assert!(accepted > 10 && denied > 5, "{accepted} {denied}");
}
