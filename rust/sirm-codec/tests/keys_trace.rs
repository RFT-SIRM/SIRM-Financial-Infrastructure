//! Differential test of `keys.rs` against the independent Python reference
//! (`scripts/key_registry_reference.py`): per-operation outcomes and final state of three seeded
//! traces (3,600 operations), the legacy-key invariant after every step, and 1,500 threshold cases.

use serde_json::Value;
use sirm_codec::keys::*;

fn is_pq(s: u16) -> bool {
    s == 2 || s == 0x0101
}

fn doc() -> Value {
    serde_json::from_str(include_str!(
        "../../../engineering/ledger_core/results/key_registry_trace_v0.json"
    ))
    .unwrap()
}

fn rec(v: &Value) -> Option<KeyRecord> {
    v.as_array().map(|a| KeyRecord {
        suite: a[0].as_u64().unwrap() as u16,
        key: a[1].as_u64().unwrap(),
    })
}

fn actor(v: &Value) -> Actor {
    if v.as_str().unwrap() == "cur" {
        Actor::Current
    } else {
        Actor::Recovery
    }
}

#[test]
fn traces_match_python_reference() {
    let d = doc();
    let delay = d["delay"].as_u64().unwrap();
    let mut seen = std::collections::BTreeSet::new();
    for t in d["traces"].as_array().unwrap() {
        let mut reg = KeyRegistry::new(is_pq, delay);
        let ops = t["ops"].as_array().unwrap();
        let outs = t["outcomes"].as_array().unwrap();
        for (i, (op, want)) in ops.iter().zip(outs).enumerate() {
            let a = actor(&op["actor"]);
            let p = op["p"].as_u64().unwrap() as u32;
            let now = op["now"].as_u64().unwrap();
            let new = KeyRecord {
                suite: op["suite"].as_u64().unwrap_or(0) as u16,
                key: op["key"].as_u64().unwrap_or(0),
            };
            let before = (reg.accounts.clone(), reg.pending.clone());
            let r = match op["op"].as_str().unwrap() {
                "register" => reg.register(p, new, rec(&op["rec"])),
                "rotate" => reg.rotate(a, p, new),
                "freeze" => reg.freeze(p),
                "revoke" => reg.revoke(a, p),
                "recover" => reg.recover(a, p, new),
                "initiate" => reg.initiate(a, p, new, now),
                "cancel" => reg.cancel(a, p),
                "finalize" => reg.finalize(a, p, now),
                o => panic!("op {o}"),
            };
            let got = match &r {
                Ok(()) => "ok".to_string(),
                Err(e) => e.code(),
            };
            assert_eq!(
                &got,
                want.as_str().unwrap(),
                "trace {} op {i}: {op}",
                t["seed"]
            );
            if r.is_err() {
                assert_eq!(
                    before,
                    (reg.accounts.clone(), reg.pending.clone()),
                    "rejected op changed state at {i}"
                );
            }
            assert!(reg.pq_sound(), "legacy-key invariant broken at {i}");
            seen.insert(got);
        }
        // final state
        let fin = &t["final"];
        let accounts = fin["accounts"].as_object().unwrap();
        assert_eq!(accounts.len(), reg.accounts.len());
        for (p, a) in accounts {
            let ours = &reg.accounts[&p.parse::<u32>().unwrap()];
            assert_eq!(ours.key.suite as u64, a["suite"].as_u64().unwrap());
            assert_eq!(ours.key.key, a["key"].as_u64().unwrap());
            assert_eq!(ours.frozen, a["frozen"].as_bool().unwrap());
            assert_eq!(ours.revoked, a["revoked"].as_bool().unwrap());
            assert_eq!(ours.pq_bound, a["pq"].as_bool().unwrap());
            assert_eq!(ours.recovery, rec(&a["rec"]));
        }
        let pending = fin["pending"].as_object().unwrap();
        assert_eq!(pending.len(), reg.pending.len());
        for (p, v) in pending {
            let (k, start) = reg.pending[&p.parse::<u32>().unwrap()];
            assert_eq!(k.suite as u64, v[0].as_u64().unwrap());
            assert_eq!(k.key, v[1].as_u64().unwrap());
            assert_eq!(start, v[2].as_u64().unwrap());
        }
    }
    assert!(seen.len() >= 12, "{seen:?}");
}

#[test]
fn threshold_cases_match_python_reference() {
    let d = doc();
    let th = &d["threshold"];
    let status = |s: u16| th["statuses"][s.to_string()].as_str().unwrap().to_string();
    let mut accepted = 0;
    for (n, c) in th["cases"].as_array().unwrap().iter().enumerate() {
        let keys: Vec<KeyRecord> = c["keys"]
            .as_array()
            .unwrap()
            .iter()
            .map(|k| rec(k).unwrap())
            .collect();
        let sigs: Vec<(usize, u64)> = c["sigs"]
            .as_array()
            .unwrap()
            .iter()
            .map(|s| (s[0].as_u64().unwrap() as usize, s[1].as_u64().unwrap()))
            .collect();
        let allow = c["allow_deprecated"].as_bool().unwrap();
        let msg = c["msg"].as_u64().unwrap();
        let permits = |s: u16| match status(s).as_str() {
            "active" => true,
            "deprecated" => allow,
            _ => false,
        };
        let verify = |r: &KeyRecord, sig: u64| sig == (r.key * 7 + msg + r.suite as u64) % 101;
        let k = c["k"].as_u64().unwrap() as usize;
        let got = threshold_accepts(&keys, k, permits, verify, &sigs);
        assert_eq!(got, c["accepts"].as_bool().unwrap(), "case {n}");
        let mut doubled = sigs.clone();
        doubled.extend(sigs.iter().copied());
        assert_eq!(
            threshold_accepts(&keys, k, permits, verify, &doubled),
            got,
            "duplicates changed case {n}"
        );
        accepted += usize::from(got);
    }
    assert!(accepted > 50, "{accepted}");
}
