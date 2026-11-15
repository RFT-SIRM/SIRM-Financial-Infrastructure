// Shared by commit_v1_conformance.rs via include!.
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

fn replay_trace(t: &Value) -> Processor {
    let (accounts, assets) = (
        t["accounts"].as_u64().unwrap() as u32,
        t["assets"].as_u64().unwrap() as u32,
    );
    let mut m = Processor::new(Holdings::new(accounts, assets), policy(t));
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
            "transfer" => Operation::Transfer { source: n(4), destination: n(5), asset, amount: amt },
            "issue" => Operation::Issue { issuer: n(4), recipient: n(5), asset, amount: amt },
            _ => Operation::Burn { holder: n(4), asset, amount: amt },
        };
        m.process(id_bytes(id), Request { principal, nonce, operation });
    }
    m
}
