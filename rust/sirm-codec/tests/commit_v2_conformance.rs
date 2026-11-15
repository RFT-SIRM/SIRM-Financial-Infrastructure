//! Conformance of the Rust state commitment v2 with the Python reference vectors: entry
//! encodings, cache/policy/registry commitments over the replayed processor and the 24 registry
//! episodes, the full root, and distinctness of single-component changes.

use serde_json::Value;
use sirm_codec::auth::*;
use sirm_codec::commit_v1::*;
use sirm_codec::commit_v2::*;
use sirm_codec::ledger::*;
use sirm_codec::machine::*;
use sirm_codec::registry::*;
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
        "../../../engineering/canonical_encoding/results/state_commitment_v2_vectors.json"
    ))
    .unwrap()
}

fn registry_trace() -> Value {
    serde_json::from_str(include_str!(
        "../../../engineering/ledger_core/results/registry_gate_trace_v0.json"
    ))
    .unwrap()
}

#[test]
fn entry_encodings_match_python() {
    let d = vectors();
    let m = processor();
    let ex: Vec<String> = m
        .cache_entries()
        .take(3)
        .map(|(id, r, s)| cache_entry(id, r, s))
        .map(|e| e.iter().map(|b| format!("{b:02x}")).collect())
        .collect();
    let want: Vec<&str> = d["cache_entry_examples_hex"]
        .as_array()
        .unwrap()
        .iter()
        .map(|v| v.as_str().unwrap())
        .collect();
    assert_eq!(ex, want);
    // the Python example is the first grant of the trace in file order
    let first = {
        let t: Value = serde_json::from_str(include_str!(
            "../../../engineering/ledger_core/results/machine_trace_v0.json"
        ))
        .unwrap();
        policy(&t["trace"])
            .grants()
            .find(|(p, s, asset, _)| {
                *p == 0
                    && *s
                        == (Scope::Transfer {
                            source: 0,
                            destination: 0,
                        })
                    && *asset == 0
            })
            .unwrap()
    };
    assert_eq!(
        first,
        (
            0,
            Scope::Transfer {
                source: 0,
                destination: 0
            },
            0,
            1000
        )
    );
    assert_eq!(
        grant_entry(first.0, first.1, first.2, first.3),
        hex(d["grant_entry_example_hex"].as_str().unwrap())
    );
    let rt = registry_trace();
    let reg = registry(&rt["episodes"][0]);
    assert_eq!(
        account_meta(&reg.accounts()[0]),
        hex(d["account_meta_example_hex"].as_str().unwrap())
    );
    assert_eq!(
        asset_meta(&reg.assets()[0]),
        hex(d["asset_meta_example_hex"].as_str().unwrap())
    );
}

#[test]
fn cache_policy_registry_and_root_match_python() {
    let d = vectors();
    let m = processor();
    assert_eq!(m.cached() as u64, d["cache_entries"].as_u64().unwrap());
    assert_eq!(
        cache_commit(&m).to_vec(),
        hex(d["cache_commit"].as_str().unwrap())
    );
    assert_eq!(
        policy_commit(m.policy()).to_vec(),
        hex(d["policy_commit"].as_str().unwrap())
    );
    let rt = registry_trace();
    let reg = registry(&rt["episodes"][0]);
    assert_eq!(
        registry_commit(&reg).to_vec(),
        hex(d["registry_commit"].as_str().unwrap())
    );
    let (v1d, suites, keys) = load();
    let header = Header {
        chain_id: v1d["args"]["chain_id"].as_u64().unwrap(),
        version: v1d["args"]["version"].as_u64().unwrap() as u16,
        hash_suite: v1d["args"]["hash_suite"].as_u64().unwrap() as u16,
    };
    assert_eq!(
        state_root_v2(&m, &header, &suites, &keys, &reg).to_vec(),
        hex(d["state_root"].as_str().unwrap())
    );
    // empty components are domain separated
    let empty = Processor::new(Holdings::new(1, 1), Policy::default());
    assert_eq!(
        cache_commit(&empty).to_vec(),
        hex(d["empty"]["cache"].as_str().unwrap())
    );
    assert_eq!(
        policy_commit(empty.policy()).to_vec(),
        hex(d["empty"]["policy"].as_str().unwrap())
    );
    let none = Registry::new(vec![], vec![]).unwrap();
    assert_eq!(
        registry_commit(&none).to_vec(),
        hex(d["empty"]["registry"].as_str().unwrap())
    );
}

#[test]
fn every_registry_episode_matches_python() {
    let d = vectors();
    let rt = registry_trace();
    let eps = rt["episodes"].as_array().unwrap();
    let want = d["episodes"].as_array().unwrap();
    assert_eq!(eps.len(), want.len());
    for (i, (ep, w)) in eps.iter().zip(want).enumerate() {
        let grants_ctrl = serde_json::json!({"grants": ep["grants"], "control": ep["control"]});
        assert_eq!(
            policy_commit(&policy(&grants_ctrl)).to_vec(),
            hex(w["policy"].as_str().unwrap()),
            "episode {i} policy"
        );
        assert_eq!(
            registry_commit(&registry(ep)).to_vec(),
            hex(w["registry"].as_str().unwrap()),
            "episode {i} registry"
        );
    }
}

#[test]
fn rust_side_single_component_changes_change_the_root() {
    let m = processor();
    let rt = registry_trace();
    let reg = registry(&rt["episodes"][0]);
    let (v1d, suites, keys) = load();
    let header = Header {
        chain_id: v1d["args"]["chain_id"].as_u64().unwrap(),
        version: 1,
        hash_suite: 1,
    };
    let base = state_root_v2(&m, &header, &suites, &keys, &reg);
    // one more request (a fresh denied or accepted entry) changes the cache and the root
    let mut m2 = m.clone();
    let mut id = [9u8; 32];
    id[0] = 1;
    m2.process(
        id,
        Request {
            principal: 0,
            nonce: m.next_nonce(0),
            operation: Operation::Burn {
                holder: 0,
                asset: 0,
                amount: 0,
            },
        },
    );
    assert_ne!(base, state_root_v2(&m2, &header, &suites, &keys, &reg));
    // changed registry status
    let rt1 = registry(&rt["episodes"][1]);
    assert_ne!(base, state_root_v2(&m, &header, &suites, &keys, &rt1));
}
