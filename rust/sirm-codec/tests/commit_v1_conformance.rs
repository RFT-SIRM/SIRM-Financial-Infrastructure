//! Conformance of the Rust state commitment v1 with the Python reference vectors: value
//! encodings, registry roots, the full root over the replayed integrated processor, and
//! distinctness of every single-field variant.

use serde_json::Value;
use sirm_codec::auth::*;
use sirm_codec::commit_v1::*;
use sirm_codec::ledger::*;
use sirm_codec::machine::*;
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

#[test]
fn encodings_and_roots_match_python() {
    let (d, suites, keys) = load();
    for (s, e) in &suites {
        assert_eq!(
            suite_value(e),
            hex(d["suite_value_hex"][s.to_string()].as_str().unwrap()),
            "suite {s}"
        );
    }
    for (p, a) in &keys {
        assert_eq!(
            key_value(a),
            hex(d["key_value_hex"][p.to_string()].as_str().unwrap()),
            "key {p}"
        );
    }
    assert_eq!(
        suite_root(&suites).to_vec(),
        hex(d["suite_root"].as_str().unwrap())
    );
    assert_eq!(
        key_root(&keys).to_vec(),
        hex(d["key_root"].as_str().unwrap())
    );
    let header = Header {
        chain_id: d["args"]["chain_id"].as_u64().unwrap(),
        version: d["args"]["version"].as_u64().unwrap() as u16,
        hash_suite: d["args"]["hash_suite"].as_u64().unwrap() as u16,
    };
    let m = processor();
    assert_eq!(
        state_root_v1(&m, &header, &suites, &keys).to_vec(),
        hex(d["state_root"].as_str().unwrap())
    );
}

#[test]
fn every_single_field_change_moves_the_root() {
    let (d, suites, keys) = load();
    let header = Header {
        chain_id: 7,
        version: 1,
        hash_suite: 1,
    };
    let m = processor();
    let base = state_root_v1(&m, &header, &suites, &keys);
    let mut roots = vec![base];
    let mut add = |h: &Header, s: &BTreeMap<u16, SuiteEntry>, k: &BTreeMap<u32, KeyAccount>| {
        roots.push(state_root_v1(&m, h, s, k));
    };
    add(
        &Header {
            chain_id: 8,
            ..header
        },
        &suites,
        &keys,
    );
    add(
        &Header {
            version: 2,
            ..header
        },
        &suites,
        &keys,
    );
    add(
        &Header {
            hash_suite: 2,
            ..header
        },
        &suites,
        &keys,
    );
    let mut s = suites.clone();
    s.get_mut(&1).unwrap().status = 3;
    add(&header, &s, &keys);
    let mut s = suites.clone();
    s.get_mut(&2).unwrap().pk_len += 1;
    add(&header, &s, &keys);
    let mut s = suites.clone();
    s.get_mut(&1).unwrap().deprecation += 1;
    add(&header, &s, &keys);
    let mut s = suites.clone();
    s.insert(
        9,
        SuiteEntry {
            kind: 1,
            status: 1,
            pk_len: 1184,
            sig_len: 1088,
            activation: 0,
            deprecation: NO_HEIGHT,
            disable: NO_HEIGHT,
        },
    );
    add(&header, &s, &keys);
    let mut k = keys.clone();
    k.get_mut(&0).unwrap().suite = 0x0101;
    add(&header, &suites, &k);
    let mut k = keys.clone();
    k.get_mut(&0).unwrap().frozen = true;
    add(&header, &suites, &k);
    let mut k = keys.clone();
    k.get_mut(&0).unwrap().revoked = true;
    add(&header, &suites, &k);
    let mut k = keys.clone();
    k.get_mut(&2).unwrap().pq_bound = true;
    add(&header, &suites, &k);
    let mut k = keys.clone();
    k.get_mut(&0).unwrap().recovery = None;
    add(&header, &suites, &k);
    let mut k = keys.clone();
    k.get_mut(&1).unwrap().pending = None;
    add(&header, &suites, &k);
    let mut k = keys.clone();
    k.get_mut(&1).unwrap().pending.as_mut().unwrap().1 += 1;
    add(&header, &suites, &k);
    let mut k = keys.clone();
    k.remove(&2);
    add(&header, &suites, &k);
    let n = roots.len();
    roots.sort();
    roots.dedup();
    assert_eq!(roots.len(), n, "two variants gave the same root");
    // the Python side verified its own 18 variants
    assert_eq!(d["variants"].as_object().unwrap().len(), 18);
}
