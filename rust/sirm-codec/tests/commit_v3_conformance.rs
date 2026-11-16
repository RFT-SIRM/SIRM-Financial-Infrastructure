//! Conformance of the Rust state commitment v3 with the Python reference vectors: the escrow
//! commitment of the final state of all 1500 dispute episodes (replayed in Rust), the id entry
//! encoding, the full root, and distinctness of single-field changes.

use serde_json::Value;
use sirm_codec::auth::*;
use sirm_codec::commit_v1::*;
use sirm_codec::commit_v3::*;
use sirm_codec::dispute::*;
use sirm_codec::ledger::*;
use sirm_codec::machine::*;
use sirm_codec::registry::*;
use sirm_codec::timelock::*;
use std::collections::BTreeMap;

include!("support/machine_replay.rs");

fn hex(s: &str) -> Vec<u8> {
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

fn h32(s: &str) -> [u8; 32] {
    hex(s).try_into().unwrap()
}

fn height(v: &Value) -> u64 {
    match v {
        Value::String(s) => s.parse().unwrap(),
        v => v.as_u64().unwrap(),
    }
}

fn load() -> (Value, BTreeMap<u16, SuiteEntry>, BTreeMap<u32, KeyAccount>) {
    let d: Value = serde_json::from_str(include_str!(
        "../../../engineering/canonical_encoding/results/state_commitment_v1_vectors.json"
    ))
    .unwrap();
    let kind = |s: &str| match s {
        "sign" => 0u8,
        "kem" => 1,
        "hash" => 2,
        _ => 3,
    };
    let status = |s: &str| match s {
        "proposed" => 0u8,
        "active" => 1,
        "deprecated" => 2,
        _ => 3,
    };
    let suites = d["suites"]
        .as_object()
        .unwrap()
        .iter()
        .map(|(k, e)| {
            (
                k.parse::<u16>().unwrap(),
                SuiteEntry {
                    kind: kind(e["kind"].as_str().unwrap()),
                    status: status(e["status"].as_str().unwrap()),
                    pk_len: e["pk_len"].as_u64().unwrap() as u32,
                    sig_len: e["sig_len"].as_u64().unwrap() as u32,
                    activation: height(&e["activation"]),
                    deprecation: height(&e["deprecation"]),
                    disable: height(&e["disable"]),
                },
            )
        })
        .collect();
    let keys = d["keys"]
        .as_object()
        .unwrap()
        .iter()
        .map(|(k, a)| {
            (
                k.parse::<u32>().unwrap(),
                KeyAccount {
                    suite: a["suite"].as_u64().unwrap() as u16,
                    key_id: h32(a["key_id"].as_str().unwrap()),
                    frozen: a["frozen"].as_bool().unwrap(),
                    revoked: a["revoked"].as_bool().unwrap(),
                    pq_bound: a["pq_bound"].as_bool().unwrap(),
                    recovery: a["recovery"].as_str().map(h32),
                    pending: a["pending"]
                        .as_array()
                        .map(|p| (h32(p[0].as_str().unwrap()), p[1].as_u64().unwrap())),
                },
            )
        })
        .collect();
    (d, suites, keys)
}

fn processor() -> Processor {
    let d: Value = serde_json::from_str(include_str!(
        "../../../engineering/ledger_core/results/machine_trace_v0.json"
    ))
    .unwrap();
    replay_trace(&d["trace"])
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
                _ => AccountStatus::Closed,
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
                _ => AssetStatus::Retired,
            },
            network: Network(a[4].as_u64().unwrap() as u32),
        })
        .collect();
    Registry::new(accounts, assets).expect("trace registries are well formed")
}

fn vectors() -> Value {
    serde_json::from_str(include_str!(
        "../../../engineering/canonical_encoding/results/state_commitment_v3_vectors.json"
    ))
    .unwrap()
}

fn dispute_trace() -> Value {
    serde_json::from_str(include_str!(
        "../../../engineering/ledger_core/results/dispute_trace_v0.json"
    ))
    .unwrap()
}

/// Replay one episode of the dispute trace; operations that the model rejects change nothing.
fn replay_episode(d: &Value, ep: &Value) -> DisputedEscrow {
    let (accounts, assets) = (
        d["accounts"].as_u64().unwrap() as u32,
        d["assets"].as_u64().unwrap() as u32,
    );
    let deadlines: Vec<u64> = ep["deadlines"]
        .as_array()
        .unwrap()
        .iter()
        .map(|v| v.as_u64().unwrap())
        .collect();
    let mut e = DisputedEscrow::new(TimeLockedEscrow::new(
        Holdings::new(accounts, assets),
        ep["vault"].as_u64().unwrap() as u32,
        deadlines,
        ep["start"].as_u64().unwrap(),
    ));
    for op in ep["ops"].as_array().unwrap() {
        let n = |k: usize| op[k].as_u64().unwrap() as u32;
        let id = |k: usize| op[k].as_u64().unwrap() as usize;
        let _ = match op[0].as_str().unwrap() {
            "issue" => e
                .escrow
                .holdings
                .issue(n(1), n(2), u(&op[3]))
                .map_err(|x| DisputeError::TimeLock(TimeLockError::Ledger(x))),
            "open" => e.open(id(1), n(2), n(3), n(4), u(&op[5])),
            "release" => e.release(id(1)),
            "cancel" => e.cancel(id(1)),
            "expire" => e.expire(id(1)),
            "advance" => e.advance(op[1].as_i64().unwrap().max(0) as u64),
            "dispute" => e.raise(id(1), n(2), n(3)),
            other => panic!("unknown op {other}"),
        };
    }
    e
}

#[test]
fn escrow_commit_of_every_episode_matches_python() {
    let v = vectors();
    let d = dispute_trace();
    let want = v["episode_commits"].as_array().unwrap();
    let eps = d["episodes"].as_array().unwrap();
    assert_eq!(eps.len(), want.len());
    for (i, (ep, w)) in eps.iter().zip(want).enumerate() {
        let e = replay_episode(&d, ep);
        assert_eq!(
            escrow_commit(&e).to_vec(),
            hex(w.as_str().unwrap()),
            "episode {i}"
        );
    }
}

#[test]
fn id_entries_and_full_root_match_python() {
    let v = vectors();
    let d = dispute_trace();
    let ex = v["example_episode"].as_u64().unwrap() as usize;
    let e = replay_episode(&d, &d["episodes"][ex]);
    for (i, w) in v["id_entry_example_hex"]
        .as_array()
        .unwrap()
        .iter()
        .enumerate()
    {
        assert_eq!(id_entry(&e, i), hex(w.as_str().unwrap()), "id {i}");
    }
    assert_eq!(
        escrow_commit(&e).to_vec(),
        hex(v["escrow_commit"].as_str().unwrap())
    );
    let rt: Value = serde_json::from_str(include_str!(
        "../../../engineering/ledger_core/results/registry_gate_trace_v0.json"
    ))
    .unwrap();
    let reg = registry(&rt["episodes"][0]);
    let (v1d, suites, keys) = load();
    let header = Header {
        chain_id: v1d["args"]["chain_id"].as_u64().unwrap(),
        version: v1d["args"]["version"].as_u64().unwrap() as u16,
        hash_suite: v1d["args"]["hash_suite"].as_u64().unwrap() as u16,
    };
    let m = processor();
    assert_eq!(
        state_root_v3(&m, &header, &suites, &keys, &reg, &e).to_vec(),
        hex(v["state_root"].as_str().unwrap())
    );
}

#[test]
fn rust_side_changes_change_the_commitment() {
    let v = vectors();
    let d = dispute_trace();
    let ex = v["example_episode"].as_u64().unwrap() as usize;
    let e = replay_episode(&d, &d["episodes"][ex]);
    let base = escrow_commit(&e);
    let mut later = e.clone();
    later.advance(e.escrow.now() + 1).unwrap();
    assert_ne!(base, escrow_commit(&later));
    let mut issued = e.clone();
    issued.escrow.holdings.issue(1, 0, 1).unwrap();
    assert_ne!(base, escrow_commit(&issued));
    // a different episode gives a different commitment
    let other = replay_episode(&d, &d["episodes"][(ex + 1) % 1500]);
    assert_ne!(base, escrow_commit(&other));
}
