//! A configuration that names accounts or assets outside the ledger must be refused by
//! `Machine::new`. Before the check existed, a migration to a recipient or destination asset outside
//! the ledger passed the domain check and then panicked in `apply` after the source units were
//! already burned, and a vault outside the ledger panicked in `Open`. This file keeps both
//! scenarios as regression tests: the machine must refuse the configuration, so no request can
//! reach the panic.

use sirm_codec::integrated::*;

const ACCOUNTS: u32 = 4;
const ASSETS: u32 = 2;

fn policy(recipient: u32) -> Policy {
    let mut p = Policy::default();
    for a in 0..ACCOUNTS {
        p.controls.insert((0, a));
    }
    p.limits.insert((0, Kind::Issue, 0, Some(0), 0), 1000);
    p.limits
        .insert((0, Kind::Migrate, 0, Some(recipient), 0), 1000);
    p.limits.insert((0, Kind::Open, 0, Some(1), 0), 1000);
    p
}

fn config(vault: Option<u32>, migration: Option<MigrationConfig>) -> Config {
    let recipient = migration.map(|m| m.recipient).unwrap_or(1);
    Config {
        accounts: ACCOUNTS,
        assets: ASSETS,
        vault,
        deadlines: vec![100],
        now: 0,
        migration,
        policy: policy(recipient),
    }
}

fn mig(holder: u32, recipient: u32, src: u32, dst: u32) -> MigrationConfig {
    MigrationConfig {
        holder,
        recipient,
        src,
        dst,
        num: 1,
        den: 1,
    }
}

#[test]
fn migration_outside_the_ledger_is_refused() {
    // recipient account outside, destination asset outside, holder outside, source asset outside
    for m in [
        mig(0, ACCOUNTS, 0, 1),
        mig(0, 1, 0, ASSETS),
        mig(ACCOUNTS, 1, 0, 1),
        mig(0, 1, ASSETS, 1),
        mig(u32::MAX, 1, 0, 1),
    ] {
        assert!(
            Machine::new(config(Some(3), Some(m))).is_none(),
            "accepted {m:?}"
        );
    }
}

#[test]
fn vault_outside_the_ledger_is_refused() {
    assert!(Machine::new(config(Some(ACCOUNTS), None)).is_none());
    assert!(Machine::new(config(Some(u32::MAX), None)).is_none());
}

#[test]
fn in_range_configurations_are_still_accepted() {
    assert!(Machine::new(config(Some(3), Some(mig(0, 1, 0, 1)))).is_some());
    assert!(Machine::new(config(None, None)).is_some());
    assert!(Machine::new(config(Some(ACCOUNTS - 1), None)).is_some());
}

/// A machine that was accepted never panics on a migration, and the invariant holds afterwards.
#[test]
fn a_machine_that_was_built_never_panics_on_migration() {
    let mut m = Machine::new(config(Some(3), Some(mig(0, 1, 0, 1)))).unwrap();
    let issue = Request {
        principal: 0,
        nonce: 0,
        op: Op::Issue {
            issuer: 0,
            recipient: 0,
            asset: 0,
            amount: 10,
        },
    };
    m.process([1; 32], issue);
    let r = Request {
        principal: 0,
        nonce: 1,
        op: Op::Migrate(5),
    };
    m.process([2; 32], r);
    assert!(m.invariant());
}
