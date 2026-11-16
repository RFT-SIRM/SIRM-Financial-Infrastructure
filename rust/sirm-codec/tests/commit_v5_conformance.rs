//! Conformance of the Rust state commitment v5 with the independent Python reference: the final
//! state of each of the 402 integrated episodes (replayed in Rust) commits to the same root, the
//! components of the rich example agree, and further requests change the root.
#![allow(dead_code)]

use serde_json::Value;
use sha2::{Digest, Sha256};
use sirm_codec::commit_v5::*;
use sirm_codec::escrow::Phase;
use sirm_codec::integrated::*;

include!("support/integrated_load.rs");

fn hexs(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

fn doc() -> (Value, Value) {
    (
        serde_json::from_str(include_str!(
            "../../../engineering/ledger_core/results/integrated_trace_v0.json"
        ))
        .unwrap(),
        serde_json::from_str(include_str!(
            "../../../engineering/canonical_encoding/results/state_commitment_v5_vectors.json"
        ))
        .unwrap(),
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

#[test]
fn all_episode_roots_match_the_python_reference() {
    let (d, v) = doc();
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
        let r = state_root_v5(&m).unwrap();
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
fn example_components_match() {
    let (d, v) = doc();
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
        hexs(&state_root_v5(&m).unwrap()),
        e["root"].as_str().unwrap()
    );
    // the example has a settled record, a filing, dust and several principals with nonces
    assert!((0..m.config().deadlines.len()).any(|i| m.filing(i).is_some()));
    assert!((0..m.config().deadlines.len())
        .any(|i| m.record(i).is_some_and(|r| r.phase != Phase::Pending)));
    assert!(m.migration_totals().2 > 0 && m.nonces().len() >= 2);
}

#[test]
fn every_further_request_changes_the_root() {
    // accepted, denied and replayed requests each change the committed state (cache or ledger)
    let (d, _) = doc();
    let (accounts, assets) = (
        d["accounts"].as_u64().unwrap() as u32,
        d["assets"].as_u64().unwrap() as u32,
    );
    let ep = &d["episodes"][5];
    let mut m = machine_for(ep, accounts, assets);
    let mut prev = state_root_v5(&m).unwrap();
    let mut changed = 0;
    for row in ep["requests"].as_array().unwrap() {
        let (id, r) = request(row.as_array().unwrap());
        let out = m.process(id, r);
        let now = state_root_v5(&m).unwrap();
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
