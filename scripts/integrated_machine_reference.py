#!/usr/bin/env python3
"""Independent Python reference for the integrated state machine (PROPOSAL, step I1).

One shared ledger and one request pipeline for transfer, issue, burn, escrow (open, release,
cancel, expire, dispute), time (advance) and asset migration (migrate). See
docs/INTEGRATED_STATE_MACHINE_PROPOSAL.md.

Pipeline (the same order as the integrated processor, extended):
 1. request-id lookup: same request -> replay (R + stored response), different -> conflict (C);
 2. nonce must equal the principal's next nonce (stale S, future F; not cached);
 3. authorization, deny by default -> cached denial, no nonce consumed, no effect;
 4. domain validation -> cached denial, no nonce consumed, no effect;
 5. otherwise the operation, the nonce increment and the cached receipt commit together.

Authorization (all explicit in the policy):
 - transfer / issue / burn: control of the account `a` and a limit grant (p, kind, a, b, asset);
 - open: control of the depositor and a limit grant (p, "open", depositor, beneficiary, asset);
 - release / cancel / expire: an id grant (p, kind, id);
 - dispute: an id grant (p, "dispute", id) and control of the claimant;
 - advance: the principal holds the clock grant;
 - migrate: control of the stream's source holder and a limit grant
   (p, "migrate", holder, recipient, source asset).
The vault account is reserved: transfer, issue to it and burn from it are rejected, so the vault
holds exactly the pending escrow amounts. Credit overflow cannot occur in escrow settlement: every
balance is bounded by the supply, and issue is rejected before the supply passes 2^128 - 1.

Denial codes: old operations keep ta, ia, ba (authorization) and tf, bf (funds); every other
code is "<op>:<c>" with c = auth (authorization), r (reserved vault), v (overflow or vault is a
party), and the escrow/time letters of dispute_reference_trace.py
(x frozen, w unknown id or no record, k id used, n not pending, d deadline passed, e deadline not
reached, z zero amount, u unknown account or asset, i insufficient funds, t time not forward,
a already filed, c claimant not a party).
"""
import copy, json, random, sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

U128 = 2**128 - 1
U64 = 2**64 - 1
ACCOUNTS, ASSETS, IDS, PRINCIPALS = 4, 2, 3, 3
OLD = ("transfer", "issue", "burn")


class IM:
    def __init__(self, accounts, assets, controls, lim, idg, clock, vault=None, deadlines=(), now=0,
                 mig=None):
        self.A, self.S = accounts, assets
        self.bal = {(a, s): 0 for a in range(accounts) for s in range(assets)}
        self.sup = {s: [0, 0, 0] for s in range(assets)}          # minted, burned, outstanding
        self.nxt, self.cache = {}, {}
        self.controls, self.lim, self.idg, self.clock = controls, lim, idg, clock
        self.vault, self.dl, self.now = vault, list(deadlines), now
        self.recs, self.files = {}, {}
        self.mig = mig                                              # dict or None
        # the configuration has to fit the ledger, as the operations do (the Rust constructor refuses
        # the same configurations)
        if vault is not None and not 0 <= vault < accounts:
            raise ValueError("vault outside the ledger")
        if mig and not (0 <= mig["holder"] < accounts and 0 <= mig["recipient"] < accounts
                        and 0 <= mig["src"] < assets and 0 <= mig["dst"] < assets):
            raise ValueError("migration outside the ledger")
        if mig:
            self.tsrc = self.ttgt = self.dust = 0
            assert mig["holder"] != vault and mig["recipient"] != vault and mig["src"] != mig["dst"]
            assert mig["num"] > 0 and mig["den"] > 0

    # ---- authorization -------------------------------------------------------------------
    def authorized(self, p, op, a):
        c, L = self.controls, self.lim
        if op in OLD:
            x, y, asset, amt = a
            k = (p, op, x, y, asset)
            return (p, x) in c and k in L and amt <= L[k]
        if op == "open":
            i, dep, ben, asset, amt = a
            k = (p, "open", dep, ben, asset)
            return (p, dep) in c and k in L and amt <= L[k]
        if op in ("release", "cancel", "expire", "resolve"):
            return (p, op, a[0]) in self.idg
        if op == "dispute":
            return (p, "dispute", a[0]) in self.idg and (p, a[1]) in c
        if op == "advance":
            return p in self.clock
        if op == "migrate":
            m = self.mig
            if not m:
                return False
            k = (p, "migrate", m["holder"], m["recipient"], m["src"])
            return (p, m["holder"]) in c and k in L and a[0] <= L[k]
        raise ValueError(op)

    # ---- domain validation (returns a denial code or None) --------------------------------
    def domain(self, op, a):
        v = self.vault
        if op == "transfer":
            x, y, s, amt = a
            if v is not None and v in (x, y):
                return "transfer:r"
            return "tf" if x != y and amt > self.bal[(x, s)] else None
        if op == "issue":
            _, y, s, amt = a
            if v is not None and y == v:
                return "issue:r"
            if self.bal[(y, s)] + amt > U128 or self.sup[s][0] + amt > U128:
                return "issue:v"
            return None
        if op == "burn":
            x, _, s, amt = a
            if v is not None and x == v:
                return "burn:r"
            return "bf" if amt > self.bal[(x, s)] else None
        if op == "open":
            i, dep, ben, s, amt = a
            if i in self.files: return "open:x"
            if i >= len(self.dl): return "open:w"
            if i in self.recs: return "open:k"
            if self.now >= self.dl[i]: return "open:d"
            if v in (dep, ben): return "open:v"
            if amt == 0: return "open:z"
            if dep >= self.A or ben >= self.A or s >= self.S: return "open:u"
            if amt > self.bal[(dep, s)]: return "open:i"
            return None
        if op in ("release", "cancel", "expire"):
            i = a[0]
            if i in self.files: return op + ":x"
            if i >= len(self.dl) or i not in self.recs: return op + ":w"
            dep, ben, s, amt, ph = self.recs[i]
            if ph != "pending": return op + ":n"
            if op == "expire" and self.now < self.dl[i]: return op + ":e"
            if op != "expire" and self.now >= self.dl[i]: return op + ":d"
            return None
        if op == "resolve":
            i = a[0]
            if i >= len(self.dl) or i not in self.recs: return "resolve:w"
            if self.recs[i][4] != "pending": return "resolve:n"
            return None if i in self.files else "resolve:o"
        if op == "dispute":
            i, claimant = a
            if i >= len(self.dl) or i not in self.recs: return "dispute:w"
            dep, ben, s, amt, ph = self.recs[i]
            if ph != "pending": return "dispute:n"
            if self.now >= self.dl[i]: return "dispute:d"
            if i in self.files: return "dispute:a"
            if claimant not in (dep, ben): return "dispute:c"
            return None
        if op == "advance":
            return "advance:t" if a[0] <= self.now else None
        if op == "migrate":
            m, amt = self.mig, a[0]
            if amt == 0: return "migrate:z"
            if amt > self.bal[(m["holder"], m["src"])]: return "migrate:i"
            prod = amt * m["num"]
            acc = self.dust + prod
            rel = acc // m["den"]
            if any(x > U128 for x in (prod, acc, self.tsrc + amt, self.ttgt + rel,
                                      self.bal[(m["recipient"], m["dst"])] + rel,
                                      self.sup[m["dst"]][0] + rel)):
                return "migrate:v"
            return None
        raise ValueError(op)

    # ---- effects --------------------------------------------------------------------------
    def apply(self, p, op, a):
        v = self.vault
        if op == "transfer":
            x, y, s, amt = a
            if x != y:
                self.bal[(x, s)] -= amt; self.bal[(y, s)] += amt
        elif op == "issue":
            _, y, s, amt = a
            self.bal[(y, s)] += amt; self.sup[s][0] += amt; self.sup[s][2] += amt
        elif op == "burn":
            x, _, s, amt = a
            self.bal[(x, s)] -= amt; self.sup[s][1] += amt; self.sup[s][2] -= amt
        elif op == "open":
            i, dep, ben, s, amt = a
            self.bal[(dep, s)] -= amt; self.bal[(v, s)] += amt
            self.recs[i] = [dep, ben, s, amt, "pending"]
        elif op in ("release", "cancel", "expire"):
            r = self.recs[a[0]]
            dep, ben, s, amt, _ = r
            to = ben if op == "release" else dep
            self.bal[(v, s)] -= amt; self.bal[(to, s)] += amt
            r[4] = {"release": "released", "cancel": "cancelled", "expire": "expired"}[op]
        elif op == "resolve":
            i, to_ben = a
            r = self.recs[i]
            dep, ben, s, amt, _ = r
            self.bal[(v, s)] -= amt; self.bal[(ben if to_ben else dep, s)] += amt
            r[4] = "released" if to_ben else "cancelled"
            del self.files[i]
        elif op == "dispute":
            self.files[a[0]] = [p, a[1], self.now]
        elif op == "advance":
            self.now = a[0]
        elif op == "migrate":
            m, amt = self.mig, a[0]
            acc = self.dust + amt * m["num"]
            rel = acc // m["den"]
            self.bal[(m["holder"], m["src"])] -= amt
            self.sup[m["src"]][1] += amt; self.sup[m["src"]][2] -= amt
            self.bal[(m["recipient"], m["dst"])] += rel
            self.sup[m["dst"]][0] += rel; self.sup[m["dst"]][2] += rel
            self.tsrc += amt; self.ttgt += rel; self.dust = acc % m["den"]

    # ---- the pipeline ---------------------------------------------------------------------
    def process(self, rid, p, nonce, op, args):
        req = (p, nonce, op, tuple(args))
        if rid in self.cache:
            prior, stored = self.cache[rid]
            return "R" + stored if prior == req else "C"
        n = self.nxt.get(p, 0)
        if nonce < n: return "S"
        if nonce > n: return "F"
        if n == U64:                       # the counter cannot advance: the nonce is no longer usable
            return "S"                     # (not cached; Rust Machine::process, Lean processCapped)
        code = None
        if not self.authorized(p, op, args):
            code = {"transfer": "ta", "issue": "ia", "burn": "ba"}.get(op, op + ":auth")
        else:
            code = self.domain(op, args)
        if code:
            stored = f"N{code}@{n}"
        else:
            self.apply(p, op, args)
            self.nxt[p] = n + 1
            stored = f"A{nonce}>{nonce + 1}"
        self.cache[rid] = (req, stored)
        return stored

    # ---- invariants -----------------------------------------------------------------------
    def check(self):
        for s in range(self.S):
            mi, bu, out = self.sup[s]
            assert mi == bu + out and sum(self.bal[(a, s)] for a in range(self.A)) == out
        assert all(x >= 0 for x in self.bal.values())
        if self.vault is not None:
            for s in range(self.S):
                assert self.bal[(self.vault, s)] == sum(r[3] for r in self.recs.values()
                                                       if r[4] == "pending" and r[2] == s)
        assert all(i in self.recs for i in self.files)
        if self.mig:
            m = self.mig
            assert self.tsrc * m["num"] == self.ttgt * m["den"] + self.dust and self.dust < m["den"]
            assert self.sup[m["src"]][1] >= self.tsrc

    def state(self):
        d = {"balances": [[str(self.bal[(a, s)]) for s in range(self.S)] for a in range(self.A)],
             "supply": [[str(x) for x in self.sup[s]] for s in range(self.S)],
             "nonces": [self.nxt.get(p, 0) for p in range(PRINCIPALS)],
             "now": self.now, "receipts": len(self.cache)}
        if self.dl:
            d["records"] = [self.recs.get(i) for i in range(len(self.dl))]
            d["filings"] = [self.files.get(i) for i in range(len(self.dl))]
        if self.mig:
            d["migration"] = {"total_source": str(self.tsrc), "total_target": str(self.ttgt),
                              "dust": str(self.dust)}
        return d


# ---- regression: the old integrated processor is a special case -------------------------
def legacy_regression(root):
    t = json.load(open(root / "engineering/ledger_core/results/machine_trace_v0.json"))["trace"]
    lim = {(g[0], g[1], g[2], g[3], g[4]): int(g[5]) for g in t["grants"]}
    m = IM(t["accounts"], t["assets"], {tuple(c) for c in t["control"]}, lim, set(), set())
    toks = []
    for r in t["requests"]:
        toks.append(m.process(r[0], r[1], r[2], r[3], (r[4], r[5], r[6], int(r[7]))))
        m.check()
    assert toks == t["tokens"], "integrated machine differs from the old processor on its own trace"
    st = m.state()
    assert st["balances"] == t["final"]["balances"] and st["supply"] == t["final"]["supply"]
    assert st["nonces"] == t["final_nonces"] and st["receipts"] == t["receipts"]
    return len(toks)


# ---- seeded traces ----------------------------------------------------------------------
def genesis(rnd):
    vault = rnd.randrange(ACCOUNTS)
    others = [a for a in range(ACCOUNTS) if a != vault]
    limits = [0, 10, 100, 1000, 5000]
    lim = {}
    for p in range(PRINCIPALS):
        for s in range(ASSETS):
            for a in range(ACCOUNTS):
                for kind, targets in (("transfer", range(ACCOUNTS)), ("issue", range(ACCOUNTS)),
                                      ("burn", [None]), ("open", range(ACCOUNTS))):
                    for b in targets:
                        if rnd.random() < (0.3 if kind != "open" else 0.5):
                            lim[(p, kind, a, b, s)] = rnd.choice(limits)
    controls = {(p, a) for p in range(PRINCIPALS) for a in range(ACCOUNTS) if rnd.random() < 0.7}
    idg = {(p, k, i) for p in range(PRINCIPALS) for k in ("release", "cancel", "expire", "dispute")
           for i in range(IDS) if rnd.random() < 0.6}
    clock = {rnd.randrange(PRINCIPALS)}
    holder, rcp = rnd.sample(others, 2)
    mig = {"holder": holder, "recipient": rcp, "src": 0, "dst": 1,
           "num": rnd.choice([1, 2, 3, 7, 100, 997]), "den": rnd.choice([1, 2, 3, 5, 10, 1000])}
    for p in range(PRINCIPALS):
        if rnd.random() < 0.8:
            lim[(p, "migrate", holder, rcp, 0)] = rnd.choice(limits[1:])
        controls.add((p, holder)) if rnd.random() < 0.8 else None
    deadlines = [rnd.randrange(4, 22) for _ in range(IDS)]
    return vault, lim, controls, idg, clock, mig, deadlines


def L_ok(m, x):
    """Prefer open grants whose depositor currently holds something."""
    return m.bal[(x[0][2], x[0][4])] > 0


def episode(rnd, n, arbiter=False):
    """One random episode. With `arbiter` the resolve operation is also drawn and granted (its own
    trace, `scripts/integrated_resolve_reference_trace.py`); the default draws are unchanged."""
    vault, lim, controls, idg, clock, mig, deadlines = genesis(rnd)
    if arbiter:
        idg = idg | {(p, "resolve", i) for p in range(PRINCIPALS) for i in range(IDS) if rnd.random() < 0.5}
    m = IM(ACCOUNTS, ASSETS, controls, lim, idg, clock, vault, deadlines, rnd.randrange(0, 3), mig)
    start_now = m.now
    keyed = {}
    for k, L in lim.items():
        keyed.setdefault(k[1], []).append((k, L))
    usable = {op: [(k, L) for k, L in v if (k[0], k[2]) in controls or op == "migrate" and (k[0], k[2]) in controls]
              for op, v in keyed.items()}
    reqs, tokens, issued, next_id = [], [], [], 1
    codes = ["transfer", "transfer", "issue", "burn", "open", "open", "open", "open", "release", "cancel", "expire", "expire", "expire", "expire",
             "dispute", "advance", "advance", "migrate", "migrate"]
    if arbiter:
        codes = codes + ["dispute", "dispute", "resolve", "resolve", "resolve", "resolve"]
    for step in range(n):
        roll = rnd.random()
        if issued and roll < 0.12:
            rid, p, nonce, op, args = rnd.choice(issued)
        elif issued and roll < 0.18:
            rid, p, nonce, op, args = rnd.choice(issued)
            args = (args[0], 1 - args[1]) if op == "resolve" else args[:-1] + (args[-1] + 1,)
        else:
            op = "issue" if step < 6 else rnd.choice(codes)
            p = rnd.randrange(PRINCIPALS)
            pool = [x for x in usable.get(op, []) if x[0][0] == p] if rnd.random() < 0.85 else []
            if op == "open" and pool and rnd.random() < 0.85:
                pool = [x for x in pool if vault not in (x[0][2], x[0][3]) and L_ok(m, x)] or pool
            if op in OLD or op == "open":
                if pool:
                    k, L = rnd.choice(pool)
                    cap = min(L, m.bal[(k[2], k[4])]) if op == "open" and rnd.random() < 0.8 else L
                    amt = rnd.choice([1, rnd.randrange(0, cap + 1), rnd.randrange(1, cap + 2), cap, L + 1] + ([0] if rnd.random() < 0.3 else []))
                    a, b, s = k[2], k[3], k[4]
                else:
                    amt, s = rnd.choice([0, 1, rnd.randrange(1, 800)]), rnd.randrange(ASSETS)
                    a, b = rnd.randrange(ACCOUNTS), rnd.randrange(ACCOUNTS)
                if op == "open":
                    args = (rnd.randrange(IDS + (1 if rnd.random() < 0.05 else 0)), a, b, s, amt)
                else:
                    args = (a, None if op == "burn" else b, s, amt)
            elif op in ("release", "cancel", "expire"):
                pend = [i for i, r in m.recs.items() if r[4] == "pending"]
                if op == "expire":
                    pend = [i for i in pend if m.now >= m.dl[i]] or pend
                i = rnd.choice(pend) if pend and rnd.random() < 0.8 else rnd.randrange(IDS + (1 if rnd.random() < 0.05 else 0))
                holders = [q for q in range(PRINCIPALS) if (q, op, i) in idg]
                if holders and rnd.random() < 0.85: p = rnd.choice(holders)
                args = (i,)
            elif op == "dispute":
                pend = [i for i, r in m.recs.items() if r[4] == "pending"]
                i = rnd.choice(pend) if pend and rnd.random() < 0.8 else rnd.randrange(IDS + (1 if rnd.random() < 0.05 else 0))
                r = m.recs.get(i)
                holders = [q for q in range(PRINCIPALS) if (q, "dispute", i) in idg and r and (q, r[0]) in controls or r and (q, "dispute", i) in idg and (q, r[1]) in controls]
                if holders and rnd.random() < 0.85: p = rnd.choice(holders)
                args = (i, rnd.choice([r[0], r[1]]) if r and rnd.random() < 0.85 else rnd.randrange(ACCOUNTS))
            elif op == "resolve":
                filed = [i for i in m.files if m.recs[i][4] == "pending"]
                i = rnd.choice(filed) if filed and rnd.random() < 0.85 else rnd.randrange(IDS + (1 if rnd.random() < 0.05 else 0))
                holders = [q for q in range(PRINCIPALS) if (q, "resolve", i) in idg]
                if holders and rnd.random() < 0.85: p = rnd.choice(holders)
                args = (i, rnd.randrange(2))
            elif op == "advance":
                if rnd.random() < 0.85: p = next(iter(clock))
                due = [m.dl[i] for i, r in m.recs.items() if r[4] == "pending" and m.dl[i] > m.now]
                if due and rnd.random() < 0.5:
                    args = (min(due),)
                else:
                    args = (m.now + rnd.choice([1, 1, 2, 3]) if rnd.random() < 0.9 else max(0, m.now - rnd.randrange(0, 2)),)
            else:
                lk = lim.get((p, "migrate", mig["holder"], mig["recipient"], 0))
                args = (rnd.choice([0, 1, rnd.randrange(1, (lk or 200) + 1), (lk or 200) + 1]),)
            nn = m.nxt.get(p, 0)
            r2 = rnd.random()
            nonce = nn if r2 < 0.8 else (max(0, nn - 1 - rnd.randrange(2)) if r2 < 0.9 else nn + 1 + rnd.randrange(3))
            rid = next_id; next_id += 1
        before = copy.deepcopy((m.bal, m.sup, m.nxt, m.recs, m.files, m.now))
        tok = m.process(rid, p, nonce, op, args)
        if tok[0] not in "A":                        # rejected, replayed, conflicting, stale, future
            assert before == (m.bal, m.sup, m.nxt, m.recs, m.files, m.now), "a rejected request changed state"
        m.check()
        enc = [str(x) if isinstance(x, int) and x > 10**9 else x for x in args]
        reqs.append([rid, p, nonce, op] + [None if x is None else (str(x) if isinstance(x, int) else x) for x in args])
        tokens.append(tok)
        if tok[0] in "AN":
            issued.append((rid, p, nonce, op, tuple(args)))
    pol = policy_json(lim, idg, clock, controls)
    return {"vault": vault, "deadlines": deadlines, "start_now": start_now, "migration": mig_json(mig),
            "policy": pol, "requests": reqs, "tokens": tokens, "final": m.state()}


def mig_json(m):
    """Rates may exceed 2^53, so they are written as decimal strings."""
    return {**m, "num": str(m["num"]), "den": str(m["den"])}


def policy_json(lim, idg, clock, controls):
    return {"limits": [[*k, str(L)] for k, L in sorted(lim.items(), key=str)],
            "ids": sorted(map(list, idg)), "clock": sorted(clock), "control": sorted(map(list, controls))}


def boundary():
    """Hand-built episodes at the u128 boundary (issue and migration overflow)."""
    eps = []
    holder, rcp, vault = 0, 1, 3
    for num, den in ((2**127, 1), (3, 2)):
        lim = {(0, "issue", 0, 0, 0): U128, (0, "issue", 0, 0, 1): U128, (0, "migrate", holder, rcp, 0): U128}
        controls = {(0, a) for a in range(ACCOUNTS)}
        mig = {"holder": holder, "recipient": rcp, "src": 0, "dst": 1, "num": num, "den": den}
        m = IM(ACCOUNTS, ASSETS, controls, lim, set(), set(), vault, [10, 10, 10], 0, mig)
        script = [("issue", (0, 0, 0, U128)), ("issue", (0, 0, 0, 1)), ("migrate", (1,)), ("migrate", (1,)),
                  ("migrate", (U128,)), ("issue", (0, 1, 1, U128)), ("issue", (0, 2, 1, 1)), ("burn", (0, None, 0, 1))]
        lim[(0, "burn", 0, None, 0)] = 5
        reqs, toks = [], []
        for i, (op, args) in enumerate(script):
            nonce = m.nxt.get(0, 0)
            toks.append(m.process(i + 1, 0, nonce, op, args)); m.check()
            reqs.append([i + 1, 0, nonce, op] + [None if x is None else str(x) for x in args])
        eps.append({"vault": vault, "deadlines": [10, 10, 10], "start_now": 0, "migration": mig_json(mig),
                    "policy": policy_json(lim, set(), set(), controls), "requests": reqs, "tokens": toks,
                    "final": m.state()})
    return eps


def selftest():
    """Configuration outside the ledger is refused; the nonce counter stops at 2^64 - 1."""
    def build(**kw):
        base = dict(accounts=ACCOUNTS, assets=ASSETS, controls=set(), lim={}, idg=set(), clock={0},
                    vault=3, deadlines=(100,), now=0, mig=None)
        base.update(kw)
        return IM(**base)
    mig = dict(holder=0, recipient=1, src=0, dst=1, num=1, den=1)
    for bad in (dict(vault=ACCOUNTS), dict(vault=2**32 - 1),
                dict(mig={**mig, "recipient": ACCOUNTS}), dict(mig={**mig, "dst": ASSETS}),
                dict(mig={**mig, "holder": ACCOUNTS}), dict(mig={**mig, "src": ASSETS})):
        try:
            build(**bad)
        except ValueError:
            continue
        raise AssertionError(f"accepted {bad}")
    build(mig=mig); build(vault=None); build(vault=ACCOUNTS - 1)
    m = build(vault=None)
    m.nxt[0] = U64 - 1
    assert m.process(1, 0, U64 - 1, "advance", [5]) == f"A{U64 - 1}>{U64}"
    assert m.nxt[0] == U64
    cached = dict(m.cache)
    assert m.process(2, 0, U64, "advance", [6]) == "S"
    assert m.nxt[0] == U64 and m.now == 5 and m.cache == cached


def main():
    selftest()
    root = Path(__file__).resolve().parent.parent
    n_legacy = legacy_regression(root)
    rnd = random.Random(20261116)
    eps = boundary() + [episode(rnd, rnd.randrange(50, 90)) for _ in range(400)]
    from collections import Counter
    ok, den = Counter(), Counter()
    for e in eps:
        for r, t in zip(e["requests"], e["tokens"]):
            if t[0] == "A": ok[r[3]] += 1
            elif t[0] == "N": den[t[1:].split("@")[0]] += 1
    for op in ("transfer", "issue", "burn", "open", "release", "cancel", "expire", "dispute", "advance", "migrate"):
        if ok[op] < 30: print("LOW", op, ok[op], dict(ok), dict(den)); raise SystemExit(1)
    assert den["issue:v"] >= 2 and den["migrate:v"] >= 1, "boundary episodes lost"
    path = Path(sys.argv[1] if len(sys.argv) > 1 else root / "engineering/ledger_core/results/integrated_trace_v0.json")
    doc = {"format": "SIRM integrated state machine reference trace v0", "accounts": ACCOUNTS, "assets": ASSETS,
           "ids": IDS, "principals": PRINCIPALS, "episodes": eps}
    path.write_text(json.dumps(doc, sort_keys=True, separators=(",", ":")) + "\n")
    print("LEGACY_REGRESSION_REQUESTS=%d EPISODES=%d" % (n_legacy, len(eps)))
    print("ACCEPTED=" + " ".join(f"{k}={v}" for k, v in sorted(ok.items())))
    print("DENIALS=" + " ".join(f"{k}={v}" for k, v in sorted(den.items())))
    print("RESULT_JSON=" + str(path))


if __name__ == "__main__":
    main()
