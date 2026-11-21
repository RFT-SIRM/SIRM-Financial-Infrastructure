// Shared loader for the integrated reference trace (included by several test crates).
// Including tests that do not use every helper allow dead code at their crate root.

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
        "resolve" => Kind::Resolve,
        other => panic!("kind {other}"),
    }
}

/// Request ids of the reference traces are small integers: 24 zero bytes then the id, big-endian.
fn rid(n: u64) -> [u8; 32] {
    let mut id = [0u8; 32];
    id[24..].copy_from_slice(&n.to_be_bytes());
    id
}

fn request(row: &[Value]) -> ([u8; 32], Request) {
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
        "resolve" => Op::Resolve {
            id: num(&row[4]) as usize,
            to_beneficiary: num(&row[5]) != 0,
        },
        other => panic!("op {other}"),
    };
    (
        rid(num(&row[0]) as u64),
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

/// Build the machine of one reference episode (policy, vault, deadlines, migration stream).
fn machine_for(ep: &Value, accounts: u32, assets: u32) -> Machine {
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
Machine::new(Config {
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
    .expect("valid configuration")
}

