"""Exhaustive single-state deletion search (engine-level folds) on a K215-style dense table.

Candidate (Y, X, c): delete state Y, redirect every transition into Y to X, and give X the row
for read 0 from {X, Y}[c & 1] and for read 1 from {X, Y}[c >> 1] (targets equal to Y become X).
c = 0 keeps X unchanged. This covers every fold where one existing state takes over another's role
with no new helper. 215 * 214 * 4 = 184,040 candidates.

Filter: a fixed bank of concrete site cases (one sample per guarded case, 6,176 cases). For a
candidate only cases that visit X or Y can change; they are run first, shortest first, stopping at
the first mismatch. A survivor of all touched cases is re-run on the full bank with fresh samples
and then belongs in the upstream checker.

  python -m src.bbzfc.foldsearch --workers 8 --out results/foldsearch-k215.json
"""
from __future__ import annotations

import argparse
import json
import random
import time
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path
from typing import Dict, List, Tuple

from . import siterun, tmio

K = Path("vendor/ProveIt/Computability/BusyBeaver/Research/ZFC/candidate-k215")
DISPATCH = 83
HALT = 215

_G: dict = {}


def build_bank(m: tmio.Machine, sites, seed: int = 77):
    """Cases with the set of states they visit and their length."""
    rng = random.Random(seed)
    bank = []
    for i, site in enumerate(sites):
        for pos in ((False, True) if site[1] == "CD" else (None,)):
            logical, spares, gap = siterun.sample_inputs(rng, site, pos)
            res = siterun.run_case(m, DISPATCH, site, logical, spares, gap)
            assert res.ok, (i, site)
            states = frozenset(q for q, _ in res.rows)
            bank.append((res.steps, i, site, logical, spares, gap, states))
    bank.sort(key=lambda b: b[0])
    return bank


def candidate(m: tmio.Machine, y: int, x: int, c: int) -> tmio.Machine:
    rows: Dict[Tuple[int, int], Tuple[int, int, int]] = {}
    for (q, b), (w, mv, z) in m.rows.items():
        if q == y:
            continue
        rows[(q, b)] = (w, mv, x if z == y else z)
    for b in (0, 1):
        src = y if (c >> b) & 1 else x
        w, mv, z = m.rows[(src, b)]
        rows[(x, b)] = (w, mv, x if z == y else z)
    start = x if m.start == y else m.start
    return tmio.Machine(start, rows)


def _init(table_path: str, sites_path: str):
    m = tmio.load(table_path)
    sites = siterun.load_sites(sites_path)
    _G["m"] = m
    _G["bank"] = build_bank(m, sites)
    # blank-start reference: first 95,714 steps must also reproduce
    _G["sites"] = sites


def _startup_ok(cm: tmio.Machine, y: int, x: int) -> bool:
    """The blank run must still reach the calibrated frame. Cheap reject: compare the step count,
    state and head at the end of startup with K215's."""
    from .sim import run

    c, why = run(cm, 95714)
    return why == "max_steps" and c.state == DISPATCH and c.head == -8 and c.ones_count() == 95


def _work(y: int):
    m, bank = _G["m"], _G["bank"]
    out = {"y": y, "tested": 0, "survivors": [], "touched_cases_run": 0}
    for x in sorted(m.states):
        if x == y or x == DISPATCH and y == DISPATCH:
            continue
        for c in range(4):
            cm = candidate(m, y, x, c)
            out["tested"] += 1
            ok = True
            for steps, i, site, logical, spares, gap, states in bank:
                if x not in states and y not in states:
                    continue
                out["touched_cases_run"] += 1
                res = siterun.run_case(cm, x if y == DISPATCH else DISPATCH, site, logical, spares, gap,
                                       limit=max(4 * steps, 5000))
                if not res.ok:
                    ok = False
                    break
            if ok and _startup_ok(cm, y, x):
                out["survivors"].append([y, x, c])
    return out


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--table", default=str(K / "k215.tm"))
    ap.add_argument("--sites", default=str(K / "sites215.json"))
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--states", default="", help="comma list of Y to test (default all)")
    ap.add_argument("--out", default="results/foldsearch-k215.json")
    a = ap.parse_args(argv)
    m = tmio.load(a.table)
    ys = [int(s) for s in a.states.split(",")] if a.states else sorted(m.states)
    t0 = time.time()
    # resumable: one JSON line per finished deleted state Y
    part = Path(a.out + "l")
    results = []
    if part.exists():
        for line in part.read_text(encoding="utf-8").splitlines():
            if line.strip():
                results.append(json.loads(line))
    done = {r["y"] for r in results}
    todo = [y for y in ys if y not in done]
    print(f"resuming: {len(done)} done, {len(todo)} to go", flush=True)
    with ProcessPoolExecutor(max_workers=a.workers, initializer=_init, initargs=(a.table, a.sites)) as ex:
        with part.open("a", encoding="utf-8") as fh:
            for r in ex.map(_work, todo):
                results.append(r)
                fh.write(json.dumps(r) + "\n")
                fh.flush()
                if r["survivors"]:
                    print("SURVIVOR", r["survivors"], flush=True)
                if len(results) % 10 == 0:
                    print(f"{len(results)}/{len(ys)} deleted-state values done, {time.time() - t0:.0f}s",
                          flush=True)
    results = [r for r in results if r["y"] in set(ys)]
    summary = {"candidates": sum(r["tested"] for r in results),
               "survivors": [s for r in results for s in r["survivors"]],
               "touched_cases_run": sum(r["touched_cases_run"] for r in results),
               "seconds": round(time.time() - t0, 1), "per_state": results}
    Path(a.out).write_text(json.dumps(summary))
    print(json.dumps({k: v for k, v in summary.items() if k != "per_state"}))


if __name__ == "__main__":
    main()
