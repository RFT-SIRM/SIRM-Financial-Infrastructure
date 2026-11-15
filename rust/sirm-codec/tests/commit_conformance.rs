//! Conformance of the Rust state commitment with the Python reference vectors, plus a
//! processor-level check: the root of the replayed integrated processor equals the root the
//! Python reference computes from the trace's final state, and every accepted state change
//! moves the root while every rejection leaves it unchanged.

use serde_json::Value;
use sirm_codec::auth::*;
use sirm_codec::commit::*;
use sirm_codec::ledger::*;
use sirm_codec::machine::*;
use std::collections::BTreeMap;

fn hex(s: &str) -> Vec<u8> {
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

fn hash(s: &str) -> Hash {
    hex(s).try_into().unwrap()
}

fn vectors() -> Value {
    serde_json::from_str(include_str!(
        "../../../engineering/canonical_encoding/results/state_commitment_vectors_v0.json"
    ))
    .unwrap()
}

#[test]
fn tree_vectors_roots_and_proofs() {
    let d = vectors();
    let e = empty_levels();
    for (i, lv) in [0usize, 1, 2, 64].iter().enumerate() {
        assert_eq!(e[*lv].to_vec(), hex(d["empty_levels"][i].as_str().unwrap()));
    }
    for t in d["trees"].as_array().unwrap() {
        let name = t["name"].as_str().unwrap();
        let entries: BTreeMap<u64, Vec<u8>> = t["entries"]
            .as_array()
            .unwrap()
            .iter()
            .map(|p| {
                (
                    p[0].as_str().unwrap().parse().unwrap(),
                    hex(p[1].as_str().unwrap()),
                )
            })
            .collect();
        let rt = hash(t["root"].as_str().unwrap());
        assert_eq!(root(&entries), rt, "{name}");
        let key: u64 = t["proof_key"].as_str().unwrap().parse().unwrap();
        let sibs: Vec<Hash> = t["proof_siblings"]
            .as_array()
            .unwrap()
            .iter()
            .map(|s| hash(s.as_str().unwrap()))
            .collect();
        assert_eq!(prove(&entries, key), sibs, "{name}: proof");
        let value = t["proof_value"].as_str().map(hex);
        assert!(verify(&rt, key, value.as_deref(), &sibs), "{name}");
        // tampering: wrong value, wrong sibling, wrong key
        let wrong = vec![0xAAu8; 16];
        assert!(
            !verify(&rt, key, Some(&wrong), &sibs),
            "{name}: wrong value"
        );
        for i in [0, 17, 63] {
            let mut bad = sibs.clone();
            bad[i][0] ^= 1;
            assert!(
                !verify(&rt, key, value.as_deref(), &bad),
                "{name}: sibling {i}"
            );
        }
        assert!(
            !verify(&rt, key, value.as_deref(), &sibs[..63]),
            "{name}: short"
        );
        let akey: u64 = t["absent_key"].as_str().unwrap().parse().unwrap();
        let asibs: Vec<Hash> = t["absent_siblings"]
            .as_array()
            .unwrap()
            .iter()
            .map(|s| hash(s.as_str().unwrap()))
            .collect();
        assert_eq!(prove(&entries, akey), asibs, "{name}: absence proof");
        assert!(verify(&rt, akey, None, &asibs), "{name}: absent");
        assert!(
            !verify(&rt, akey, Some(&wrong), &asibs),
            "{name}: absent vs present"
        );
    }
}

fn u(v: &Value) -> u128 {
    v.as_str().unwrap().parse().unwrap()
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

#[test]
fn processor_root_matches_python_and_tracks_changes() {
    let d: Value = serde_json::from_str(include_str!(
        "../../../engineering/ledger_core/results/machine_trace_v0.json"
    ))
    .unwrap();
    let t = &d["trace"];
    let (accounts, assets) = (
        t["accounts"].as_u64().unwrap() as u32,
        t["assets"].as_u64().unwrap() as u32,
    );
    let mut m = Processor::new(Holdings::new(accounts, assets), policy(t));
    let (mut moved, mut still) = (0, 0);
    for r in t["requests"].as_array().unwrap() {
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
        let before = state_root(&m);
        let out = m.process(
            id_bytes(id),
            Request {
                principal,
                nonce,
                operation,
            },
        );
        let after = state_root(&m);
        match out {
            Outcome::Accepted(_) => {
                // a zero-amount transfer to oneself may leave balances alone, but the nonce moves
                assert_ne!(before, after, "accepted request {id} did not move the root");
                moved += 1;
            }
            _ => {
                assert_eq!(before, after, "request {id} ({out:?}) moved the root");
                still += 1;
            }
        }
    }
    assert!(moved > 1000 && still > 1000, "{moved}/{still}");
    let d = vectors();
    assert_eq!(
        state_root(&m).to_vec(),
        hex(d["machine_final_state_root"].as_str().unwrap())
    );
    // proofs against the final trees
    let (bal, sup, non) = state_trees(&m);
    let rb = root(&bal);
    for (k, v) in bal.iter().chain([(&((7u64 << 32) | 9), &vec![])]) {
        let sibs = prove(&bal, *k);
        if v.is_empty() {
            assert!(verify(&rb, *k, None, &sibs));
        } else {
            assert!(verify(&rb, *k, Some(v), &sibs));
            assert!(!verify(&rb, *k, Some(&[0u8; 16]), &sibs));
        }
    }
    let _ = (sup, non);
    assert_eq!(
        combine(
            accounts,
            assets,
            &rb,
            &root(&state_trees(&m).1),
            &root(&state_trees(&m).2)
        ),
        state_root(&m)
    );
}

#[test]
fn sensitivity_vectors() {
    let d = vectors();
    let s = &d["sensitivity_base"];
    assert_eq!(s["variants"].as_object().unwrap().len(), 6);
    // dimensions and trees are bound into the root: all seven roots are distinct
    let mut roots: Vec<String> = s["variants"]
        .as_object()
        .unwrap()
        .values()
        .map(|v| v.as_str().unwrap().to_string())
        .collect();
    roots.push(s["root"].as_str().unwrap().to_string());
    roots.sort();
    roots.dedup();
    assert_eq!(roots.len(), 7);
}
