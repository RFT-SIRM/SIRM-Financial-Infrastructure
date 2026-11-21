#!/usr/bin/env python3
"""Reference trace of the integrated state machine with the arbiter operation `resolve`.

`resolve(id, to_beneficiary)` settles a disputed escrow: the vault pays the escrowed amount to the
beneficiary (phase `released`) or the depositor (phase `cancelled`) and the filing is consumed.
It is authorized by an explicit grant `(principal, "resolve", id)`, applies only to a pending escrow
that has a filing, and its denial codes are `resolve:auth`, `resolve:w` (unknown id), `resolve:n`
(not pending) and `resolve:o` (not disputed).

The machine, the pipeline and every other operation are the ones of
`scripts/integrated_machine_reference.py`, loaded from that file; its own trace is unchanged. This
trace is replayed by `rust/sirm-codec/tests/integrated_resolve_trace.rs`. Not adopted, and the
operation has no wire encoding yet.
"""
import importlib.util
import json
import random
import sys
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("integrated_machine_reference", HERE / "integrated_machine_reference.py")
im = importlib.util.module_from_spec(spec)
spec.loader.exec_module(im)


def main():
    root = HERE.parent
    rnd = random.Random(20261121)
    eps = [im.episode(rnd, rnd.randrange(60, 110), arbiter=True) for _ in range(300)]
    ok, den, sides = Counter(), Counter(), Counter()
    for e in eps:
        for r, t in zip(e["requests"], e["tokens"]):
            if t[0] == "A":
                ok[r[3]] += 1
                if r[3] == "resolve":
                    sides[r[5]] += 1
            elif t[0] == "N":
                den[t[1:].split("@")[0]] += 1
    assert ok["resolve"] >= 100 and sides["0"] >= 30 and sides["1"] >= 30, (dict(ok), dict(sides))
    for code in ("resolve:auth", "resolve:w", "resolve:n", "resolve:o", "release:x", "cancel:x", "expire:x"):
        assert den[code] >= 1, ("denial not exercised", code)
    path = Path(sys.argv[1] if len(sys.argv) > 1 else root / "engineering/ledger_core/results/integrated_resolve_trace_v0.json")
    doc = {"format": "SIRM integrated state machine with resolve, reference trace v0", "accounts": im.ACCOUNTS,
           "assets": im.ASSETS, "ids": im.IDS, "principals": im.PRINCIPALS, "episodes": eps}
    path.write_text(json.dumps(doc, sort_keys=True, separators=(",", ":")) + "\n")
    print("EPISODES=%d" % len(eps))
    print("ACCEPTED=" + " ".join(f"{k}={v}" for k, v in sorted(ok.items())))
    print("RESOLVE_ACCEPTED_TO_BENEFICIARY=%d TO_DEPOSITOR=%d" % (sides["1"], sides["0"]))
    print("DENIALS=" + " ".join(f"{k}={v}" for k, v in sorted(den.items()) if k.startswith("resolve")))
    print("RESULT_JSON=" + str(path))


if __name__ == "__main__":
    main()
