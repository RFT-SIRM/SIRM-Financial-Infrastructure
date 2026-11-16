//! Rust port of the integrated state machine reference (proposal step I2): one shared ledger and
//! one request pipeline for transfer, issue, burn, escrow (open, release, cancel, expire, dispute),
//! time (advance) and asset migration (migrate). Reference: `scripts/integrated_machine_reference.py`;
//! trace: `engineering/ledger_core/results/integrated_trace_v0.json`;
//! design: `docs/INTEGRATED_STATE_MACHINE_PROPOSAL.md`.
//!
//! Pipeline: request-id lookup (replay or conflict); nonce check (stale and future are not
//! cached); authorization, deny by default; domain validation; then the operation, the nonce
//! increment and the cached receipt commit together. Denials are cached and consume no nonce.
//! The vault account is reserved: transfer, issue to it and burn from it are rejected. The rules for
//! the new operations are proposals with no Lean counterpart.

use crate::dispute::Filing;
use crate::escrow::{Phase, Record};
use crate::ledger::Holdings;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Kind {
    Transfer,
    Issue,
    Burn,
    Open,
    Release,
    Cancel,
    Expire,
    Dispute,
    Advance,
    Migrate,
}

impl Kind {
    pub fn name(self) -> &'static str {
        match self {
            Kind::Transfer => "transfer",
            Kind::Issue => "issue",
            Kind::Burn => "burn",
            Kind::Open => "open",
            Kind::Release => "release",
            Kind::Cancel => "cancel",
            Kind::Expire => "expire",
            Kind::Dispute => "dispute",
            Kind::Advance => "advance",
            Kind::Migrate => "migrate",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Op {
    Transfer {
        src: u32,
        dst: u32,
        asset: u32,
        amount: u128,
    },
    Issue {
        issuer: u32,
        recipient: u32,
        asset: u32,
        amount: u128,
    },
    Burn {
        holder: u32,
        asset: u32,
        amount: u128,
    },
    Open {
        id: usize,
        depositor: u32,
        beneficiary: u32,
        asset: u32,
        amount: u128,
    },
    Release(usize),
    Cancel(usize),
    Expire(usize),
    Dispute {
        id: usize,
        claimant: u32,
    },
    Advance(u64),
    Migrate(u128),
}

impl Op {
    pub fn kind(&self) -> Kind {
        match self {
            Op::Transfer { .. } => Kind::Transfer,
            Op::Issue { .. } => Kind::Issue,
            Op::Burn { .. } => Kind::Burn,
            Op::Open { .. } => Kind::Open,
            Op::Release(_) => Kind::Release,
            Op::Cancel(_) => Kind::Cancel,
            Op::Expire(_) => Kind::Expire,
            Op::Dispute { .. } => Kind::Dispute,
            Op::Advance(_) => Kind::Advance,
            Op::Migrate(_) => Kind::Migrate,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Request {
    pub principal: u32,
    pub nonce: u64,
    pub op: Op,
}

/// Why a request was denied (cached, no nonce consumed, no effect).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Cause {
    Auth,
    /// Transfer, issue or burn touches the reserved vault account.
    Reserved,
    /// Overflow of the ledger or migration arithmetic, or the vault is a party (open).
    VaultOrOverflow,
    Frozen,
    UnknownId,
    IdInUse,
    NotPending,
    DeadlinePassed,
    DeadlineNotReached,
    ZeroAmount,
    UnknownAccount,
    Insufficient,
    TimeNotForward,
    AlreadyFiled,
    ClaimantNotParty,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Denial {
    pub kind: Kind,
    pub cause: Cause,
}

impl Denial {
    /// Stable code. The three original operations keep their short codes.
    pub fn code(&self) -> String {
        match (self.kind, self.cause) {
            (Kind::Transfer, Cause::Auth) => "ta".into(),
            (Kind::Issue, Cause::Auth) => "ia".into(),
            (Kind::Burn, Cause::Auth) => "ba".into(),
            (Kind::Transfer, Cause::Insufficient) => "tf".into(),
            (Kind::Burn, Cause::Insufficient) => "bf".into(),
            (k, c) => {
                let s = match c {
                    Cause::Auth => "auth",
                    Cause::Reserved => "r",
                    Cause::VaultOrOverflow => "v",
                    Cause::Frozen => "x",
                    Cause::UnknownId => "w",
                    Cause::IdInUse => "k",
                    Cause::NotPending => "n",
                    Cause::DeadlinePassed => "d",
                    Cause::DeadlineNotReached => "e",
                    Cause::ZeroAmount => "z",
                    Cause::UnknownAccount => "u",
                    Cause::Insufficient => "i",
                    Cause::TimeNotForward => "t",
                    Cause::AlreadyFiled => "a",
                    Cause::ClaimantNotParty => "c",
                };
                format!("{}:{}", k.name(), s)
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Stored {
    Accepted { nonce: u64 },
    Denied { denial: Denial, expected_nonce: u64 },
}

impl Stored {
    pub fn token(&self) -> String {
        match self {
            Stored::Accepted { nonce } => format!("A{}>{}", nonce, nonce + 1),
            Stored::Denied {
                denial,
                expected_nonce,
            } => format!("N{}@{}", denial.code(), expected_nonce),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Outcome {
    Replay(Stored),
    Conflict,
    Stale,
    Future,
    Done(Stored),
}

impl Outcome {
    /// Token of the reference trace: `R<stored>`, `C`, `S`, `F`, or the stored response.
    pub fn token(&self) -> String {
        match self {
            Outcome::Replay(s) => format!("R{}", s.token()),
            Outcome::Conflict => "C".into(),
            Outcome::Stale => "S".into(),
            Outcome::Future => "F".into(),
            Outcome::Done(s) => s.token(),
        }
    }
}

/// Static authorization policy. Everything is explicit; nothing is granted by default.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Policy {
    /// (principal, account): the principal controls the account.
    pub controls: BTreeSet<(u32, u32)>,
    /// (principal, kind, a, b, asset) -> amount limit. For transfer and issue `a, b` are
    /// (source, destination) and (issuer, recipient); burn `(holder, None)`; open
    /// (depositor, beneficiary); migrate (holder, recipient) with the source asset.
    pub limits: BTreeMap<(u32, Kind, u32, Option<u32>, u32), u128>,
    /// (principal, kind, id) for release, cancel, expire and dispute.
    pub ids: BTreeSet<(u32, Kind, usize)>,
    /// Principals that may advance time.
    pub clock: BTreeSet<u32>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MigrationConfig {
    pub holder: u32,
    pub recipient: u32,
    pub src: u32,
    pub dst: u32,
    pub num: u128,
    pub den: u128,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Config {
    pub accounts: u32,
    pub assets: u32,
    pub vault: Option<u32>,
    pub deadlines: Vec<u64>,
    pub now: u64,
    pub migration: Option<MigrationConfig>,
    pub policy: Policy,
}

/// State without the response cache: what a rejected request must leave unchanged.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Snapshot {
    pub ledger: Holdings,
    pub nonces: BTreeMap<u32, u64>,
    pub records: BTreeMap<usize, Record>,
    pub filings: BTreeMap<usize, Filing>,
    pub now: u64,
    pub migration: (u128, u128, u128),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Machine {
    cfg: Config,
    pub ledger: Holdings,
    nonces: BTreeMap<u32, u64>,
    cache: BTreeMap<[u8; 32], (Request, Stored)>,
    now: u64,
    records: BTreeMap<usize, Record>,
    filings: BTreeMap<usize, Filing>,
    total_source: u128,
    total_target: u128,
    dust: u128,
}

impl Machine {
    /// `None` if the migration stream is degenerate or uses the vault.
    pub fn new(cfg: Config) -> Option<Machine> {
        if let Some(m) = cfg.migration {
            if m.num == 0 || m.den == 0 || m.src == m.dst {
                return None;
            }
            if Some(m.holder) == cfg.vault || Some(m.recipient) == cfg.vault {
                return None;
            }
        }
        Some(Machine {
            ledger: Holdings::new(cfg.accounts, cfg.assets),
            nonces: BTreeMap::new(),
            cache: BTreeMap::new(),
            now: cfg.now,
            records: BTreeMap::new(),
            filings: BTreeMap::new(),
            total_source: 0,
            total_target: 0,
            dust: 0,
            cfg,
        })
    }

    pub fn nonce(&self, principal: u32) -> u64 {
        self.nonces.get(&principal).copied().unwrap_or(0)
    }

    pub fn now(&self) -> u64 {
        self.now
    }

    pub fn cached(&self) -> usize {
        self.cache.len()
    }

    pub fn record(&self, id: usize) -> Option<Record> {
        self.records.get(&id).copied()
    }

    pub fn filing(&self, id: usize) -> Option<Filing> {
        self.filings.get(&id).copied()
    }

    /// (total source, total target, dust) of the migration stream.
    pub fn migration_totals(&self) -> (u128, u128, u128) {
        (self.total_source, self.total_target, self.dust)
    }

    pub fn snapshot(&self) -> Snapshot {
        Snapshot {
            ledger: self.ledger.clone(),
            nonces: self.nonces.clone(),
            records: self.records.clone(),
            filings: self.filings.clone(),
            now: self.now,
            migration: self.migration_totals(),
        }
    }

    fn controls(&self, p: u32, a: u32) -> bool {
        self.cfg.policy.controls.contains(&(p, a))
    }

    fn limit(&self, p: u32, k: Kind, a: u32, b: Option<u32>, s: u32) -> Option<u128> {
        self.cfg.policy.limits.get(&(p, k, a, b, s)).copied()
    }

    fn authorized(&self, p: u32, op: &Op) -> bool {
        let within = |l: Option<u128>, amount: u128| l.is_some_and(|l| amount <= l);
        match *op {
            Op::Transfer {
                src,
                dst,
                asset,
                amount,
            } => {
                self.controls(p, src)
                    && within(self.limit(p, Kind::Transfer, src, Some(dst), asset), amount)
            }
            Op::Issue {
                issuer,
                recipient,
                asset,
                amount,
            } => {
                self.controls(p, issuer)
                    && within(
                        self.limit(p, Kind::Issue, issuer, Some(recipient), asset),
                        amount,
                    )
            }
            Op::Burn {
                holder,
                asset,
                amount,
            } => {
                self.controls(p, holder)
                    && within(self.limit(p, Kind::Burn, holder, None, asset), amount)
            }
            Op::Open {
                depositor,
                beneficiary,
                asset,
                amount,
                ..
            } => {
                self.controls(p, depositor)
                    && within(
                        self.limit(p, Kind::Open, depositor, Some(beneficiary), asset),
                        amount,
                    )
            }
            Op::Release(id) => self.cfg.policy.ids.contains(&(p, Kind::Release, id)),
            Op::Cancel(id) => self.cfg.policy.ids.contains(&(p, Kind::Cancel, id)),
            Op::Expire(id) => self.cfg.policy.ids.contains(&(p, Kind::Expire, id)),
            Op::Dispute { id, claimant } => {
                self.cfg.policy.ids.contains(&(p, Kind::Dispute, id)) && self.controls(p, claimant)
            }
            Op::Advance(_) => self.cfg.policy.clock.contains(&p),
            Op::Migrate(amount) => match self.cfg.migration {
                None => false,
                Some(m) => {
                    self.controls(p, m.holder)
                        && within(
                            self.limit(p, Kind::Migrate, m.holder, Some(m.recipient), m.src),
                            amount,
                        )
                }
            },
        }
    }

    fn in_range(&self, accounts: &[u32], assets: &[u32]) -> bool {
        accounts.iter().all(|&a| a < self.cfg.accounts)
            && assets.iter().all(|&s| s < self.cfg.assets)
    }

    /// Domain validation, in the order of the reference.
    fn domain(&self, op: &Op) -> Option<Cause> {
        use Cause::*;
        let v = self.cfg.vault;
        let hit = |a: u32| v == Some(a);
        match *op {
            Op::Transfer {
                src,
                dst,
                asset,
                amount,
            } => {
                if !self.in_range(&[src, dst], &[asset]) {
                    return Some(UnknownAccount);
                }
                if hit(src) || hit(dst) {
                    return Some(Reserved);
                }
                (src != dst && amount > self.ledger.balance(src, asset)).then_some(Insufficient)
            }
            Op::Issue {
                recipient,
                asset,
                amount,
                ..
            } => {
                if !self.in_range(&[recipient], &[asset]) {
                    return Some(UnknownAccount);
                }
                if hit(recipient) {
                    return Some(Reserved);
                }
                let bal = self.ledger.balance(recipient, asset).checked_add(amount);
                let minted = self.ledger.supply(asset).minted.checked_add(amount);
                (bal.is_none() || minted.is_none()).then_some(VaultOrOverflow)
            }
            Op::Burn {
                holder,
                asset,
                amount,
            } => {
                if !self.in_range(&[holder], &[asset]) {
                    return Some(UnknownAccount);
                }
                if hit(holder) {
                    return Some(Reserved);
                }
                (amount > self.ledger.balance(holder, asset)).then_some(Insufficient)
            }
            Op::Open {
                id,
                depositor,
                beneficiary,
                asset,
                amount,
            } => {
                if self.filings.contains_key(&id) {
                    return Some(Frozen);
                }
                if id >= self.cfg.deadlines.len() {
                    return Some(UnknownId);
                }
                if self.records.contains_key(&id) {
                    return Some(IdInUse);
                }
                if self.now >= self.cfg.deadlines[id] {
                    return Some(DeadlinePassed);
                }
                if v.is_none() || hit(depositor) || hit(beneficiary) {
                    return Some(VaultOrOverflow);
                }
                if amount == 0 {
                    return Some(ZeroAmount);
                }
                if !self.in_range(&[depositor, beneficiary], &[asset]) {
                    return Some(UnknownAccount);
                }
                (amount > self.ledger.balance(depositor, asset)).then_some(Insufficient)
            }
            Op::Release(id) | Op::Cancel(id) | Op::Expire(id) => {
                let expire = matches!(op, Op::Expire(_));
                if self.filings.contains_key(&id) {
                    return Some(Frozen);
                }
                let Some(r) = self.records.get(&id) else {
                    return Some(UnknownId);
                };
                if r.phase != Phase::Pending {
                    return Some(NotPending);
                }
                let dl = self.cfg.deadlines[id];
                if expire && self.now < dl {
                    return Some(DeadlineNotReached);
                }
                if !expire && self.now >= dl {
                    return Some(DeadlinePassed);
                }
                None
            }
            Op::Dispute { id, claimant } => {
                let Some(r) = self.records.get(&id) else {
                    return Some(UnknownId);
                };
                if r.phase != Phase::Pending {
                    return Some(NotPending);
                }
                if self.now >= self.cfg.deadlines[id] {
                    return Some(DeadlinePassed);
                }
                if self.filings.contains_key(&id) {
                    return Some(AlreadyFiled);
                }
                (claimant != r.depositor && claimant != r.beneficiary).then_some(ClaimantNotParty)
            }
            Op::Advance(t) => (t <= self.now).then_some(TimeNotForward),
            Op::Migrate(amount) => {
                let m = self.cfg.migration.expect("authorized implies a stream");
                if amount == 0 {
                    return Some(ZeroAmount);
                }
                if amount > self.ledger.balance(m.holder, m.src) {
                    return Some(Insufficient);
                }
                let step = (|| {
                    let acc = amount.checked_mul(m.num)?.checked_add(self.dust)?;
                    let rel = acc / m.den;
                    self.total_source.checked_add(amount)?;
                    self.total_target.checked_add(rel)?;
                    self.ledger.balance(m.recipient, m.dst).checked_add(rel)?;
                    self.ledger.supply(m.dst).minted.checked_add(rel)?;
                    Some(())
                })();
                step.is_none().then_some(VaultOrOverflow)
            }
        }
    }

    fn apply(&mut self, p: u32, op: &Op) {
        let vault = self.cfg.vault;
        match *op {
            Op::Transfer {
                src,
                dst,
                asset,
                amount,
            } => self
                .ledger
                .transfer(src, dst, asset, amount)
                .expect("validated"),
            Op::Issue {
                recipient,
                asset,
                amount,
                ..
            } => self
                .ledger
                .issue(recipient, asset, amount)
                .expect("validated"),
            Op::Burn {
                holder,
                asset,
                amount,
            } => self.ledger.burn(holder, asset, amount).expect("validated"),
            Op::Open {
                id,
                depositor,
                beneficiary,
                asset,
                amount,
            } => {
                let vault = vault.expect("validated");
                self.ledger
                    .transfer(depositor, vault, asset, amount)
                    .expect("validated");
                self.records.insert(
                    id,
                    Record {
                        depositor,
                        beneficiary,
                        asset,
                        amount,
                        phase: Phase::Pending,
                    },
                );
            }
            Op::Release(id) | Op::Cancel(id) | Op::Expire(id) => {
                let vault = vault.expect("a record implies a vault");
                let r = self.records[&id];
                let (to, phase) = match op {
                    Op::Release(_) => (r.beneficiary, Phase::Released),
                    Op::Cancel(_) => (r.depositor, Phase::Cancelled),
                    _ => (r.depositor, Phase::Expired),
                };
                self.ledger
                    .transfer(vault, to, r.asset, r.amount)
                    .expect("validated");
                self.records.insert(id, Record { phase, ..r });
            }
            Op::Dispute { id, claimant } => {
                self.filings.insert(
                    id,
                    Filing {
                        principal: p,
                        claimant,
                        filed_at: self.now,
                    },
                );
            }
            Op::Advance(t) => self.now = t,
            Op::Migrate(amount) => {
                let m = self.cfg.migration.expect("validated");
                let acc = amount * m.num + self.dust;
                let rel = acc / m.den;
                self.ledger
                    .burn(m.holder, m.src, amount)
                    .expect("validated");
                self.ledger
                    .issue(m.recipient, m.dst, rel)
                    .expect("validated");
                self.total_source += amount;
                self.total_target += rel;
                self.dust = acc % m.den;
            }
        }
    }

    pub fn process(&mut self, id: [u8; 32], req: Request) -> Outcome {
        if let Some((prior, stored)) = self.cache.get(&id) {
            return if *prior == req {
                Outcome::Replay(*stored)
            } else {
                Outcome::Conflict
            };
        }
        let expected = self.nonce(req.principal);
        if req.nonce < expected {
            return Outcome::Stale;
        }
        if req.nonce > expected {
            return Outcome::Future;
        }
        let cause = if !self.authorized(req.principal, &req.op) {
            Some(Cause::Auth)
        } else {
            self.domain(&req.op)
        };
        let stored = match cause {
            Some(cause) => Stored::Denied {
                denial: Denial {
                    kind: req.op.kind(),
                    cause,
                },
                expected_nonce: expected,
            },
            None => {
                self.apply(req.principal, &req.op);
                self.nonces.insert(req.principal, expected + 1);
                Stored::Accepted { nonce: expected }
            }
        };
        self.cache.insert(id, (req, stored));
        Outcome::Done(stored)
    }

    /// Conservation, vault equals the pending escrow amounts, the dust equation, every filing has
    /// a record.
    pub fn invariant(&self) -> bool {
        if !self.ledger.invariant() {
            return false;
        }
        if let Some(v) = self.cfg.vault {
            for s in 0..self.cfg.assets {
                let pending: u128 = self
                    .records
                    .values()
                    .filter(|r| r.phase == Phase::Pending && r.asset == s)
                    .map(|r| r.amount)
                    .sum();
                if self.ledger.balance(v, s) != pending {
                    return false;
                }
            }
        }
        if !self.filings.keys().all(|id| self.records.contains_key(id)) {
            return false;
        }
        if let Some(m) = self.cfg.migration {
            let lhs = self.total_source.checked_mul(m.num);
            let rhs = self
                .total_target
                .checked_mul(m.den)
                .and_then(|x| x.checked_add(self.dust));
            if !(self.dust < m.den && lhs.is_some() && lhs == rhs) {
                return false;
            }
        }
        true
    }
}
