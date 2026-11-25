"""Independent reproduction of K215 (Busy Beaver / ZFC row, 215 states).

  python3 verify.py              about 2 minutes, standard library only
  python3 verify.py --upstream   also replays the author's symbolic checker (about 6 minutes)

Downloads the pinned ProveIt files into ./cache (checking their SHA-256), then checks, with code in
./code written independently of the ProveIt checker: table shape and hashes, the 95,714-step blank
start and its frame, a concrete randomized sweep of all 6,176 guarded site cases, the exact
bisimulation quotient, the decoder map from dispatcher 84, the engine/decoder split, and a
mutation control (dropping one zero-counter state must break exactly the 37 six-zero sites).
Exit status 0 iff every check holds. Writes evidence/run.json.
"""
from __future__ import annotations

import hashlib
import json
import subprocess
import sys
import time
import urllib.request
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE / "code"))

from bbzfc import alloc, decoder, frames, quotient, sim, siterun, tmio  # noqa: E402

COMMIT = "66ce3c04bbc691d753a31a1615d97a93edbf5309"
BASE = f"https://raw.githubusercontent.com/VladimirReshetnikov/ProveIt/{COMMIT}/Computability/BusyBeaver/Research/ZFC/candidate-k215/"
FILES = {
    "k215.tm": "fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090",
    "k215.native.tm": "9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2",
    "sites215.json": "17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba",
    "canonicalization.json": None,
}
UPSTREAM = ["verification/code/validate_native.py", "verification/code/runtime/symbolic_runtime.py",
            "verification/code/runtime/independent_runtime.py", "verification/code/inputs/legacy_mapping.json"]


def fetch(rel: str, want: str | None) -> Path:
    dst = HERE / "cache" / rel
    if not dst.exists():
        dst.parent.mkdir(parents=True, exist_ok=True)
        with urllib.request.urlopen(BASE + rel, timeout=120) as r:
            dst.write_bytes(r.read())
    got = hashlib.sha256(dst.read_bytes()).hexdigest()
    if want and got != want:
        raise SystemExit(f"hash mismatch for {rel}: {got}")
    return dst


def main() -> int:
    t0 = time.time()
    paths = {k: fetch(k, v) for k, v in FILES.items()}
    rep: dict = {"source_commit": COMMIT}
    dense = tmio.load(paths["k215.tm"])
    native = tmio.load(paths["k215.native.tm"])
    tmio.check_dense(dense, 215)
    rep["shape"] = {"states": len(dense.states), "rows": len(dense.rows), "halt": sorted(dense.halt_states),
                    "dense_rewrite_identical": tmio.sha256_hex(tmio.dumps(dense)) == FILES["k215.tm"]}

    # native and dense tables are the same machine under the published relabelling
    canon = json.loads(paths["canonicalization.json"].read_text(encoding="utf-8"))
    n2c = {int(k): v for k, v in canon["native_to_canonical"].items()}
    cd, cn = sim.initial(), sim.initial()
    cd.state, cn.state = dense.start, native.start
    same = True
    for _ in range(20000):
        sim.run(dense, cd.step + 1, cfg=cd)
        sim.run(native, cn.step + 1, cfg=cn)
        if n2c[cn.state] != cd.state or cn.head != cd.head:
            same = False
            break
    rep["native_dense_lockstep_20000"] = same and cn.ones() == cd.ones()

    c, _ = sim.run(dense, 95714)
    _, blocks = frames.one_blocks_after_gap(c)
    rep["startup"] = {"steps": c.step, "state": c.state, "head": c.head, "ones": c.ones_count(),
                      "register_blocks": blocks[1:10], "spares": len(blocks[10:]),
                      "spares_all_value_1": all(b == 2 for b in blocks[10:])}

    sites = siterun.load_sites(paths["sites215.json"])
    sw = siterun.sweep(dense, 83, sites, samples=2, seed=2026)
    rep["site_sweep"] = {"sites": len(sites), "guarded_cases": len(sites) + sum(s[1] == "CD" for s in sites),
                         "random_cases": sw.cases, "failures": len(sw.failures),
                         "rows_used": len(sw.rows_used), "steps_min": sw.min_steps, "steps_max": sw.max_steps}

    rep["exact_quotient_mergeable_pairs"] = quotient.mergeable(dense)
    _, nodes = decoder.build_tree(sites)
    rep["source"] = {"distinct_subtrees": len(nodes), "leaf_kinds": sum(n[0] == "leaf" for n in nodes)}

    tree = alloc.build_tree(sites, alloc.Interner())
    dm = alloc.DecoderMap(native.rows, tree)
    eng = alloc.engine_rows(native, dm, sites, samples=1)
    keep = eng | dm.helper_rows
    pinned = {native.rows[k][2] for k in eng} & set(dm.state_nodes)
    free = [q for q in dm.state_nodes
            if q != 84 and q not in pinned and (q, 0) not in keep and (q, 1) not in keep]
    rows, _ = alloc.allocate(native, sites, sites, eng, dm)
    rep["decoder"] = {"errors": len(dm.errors), "decoder_states": len(dm.state_nodes),
                      "internal_nodes": len(dm.node_states),
                      "shared_states": sum(len(v) > 1 for v in dm.state_nodes.values()),
                      "other_states": len(native.states) - len(dm.state_nodes),
                      "engine_rows": len(eng), "pinned_decoder_states": len(pinned),
                      "free_decoder_states": len(free),
                      "self_allocation_identical": rows == native.rows}

    # mutation control: skip zero-counter state 50 (row (34,0) -> 75)
    mrows = dict(dense.rows)
    mrows[(34, 0)] = (0, -1, 75)
    mutant = tmio.Machine(dense.start, mrows)
    six = [i for i, s in enumerate(sites) if max(len(z) for z in s[0].split("1")) == 6]
    rest = [i for i, s in enumerate(sites) if max(len(z) for z in s[0].split("1")) <= 5]
    r6 = siterun.sweep(mutant, 83, sites, samples=2, seed=1, site_indices=six)
    r5 = siterun.sweep(mutant, 83, sites, samples=1, seed=1, site_indices=rest)
    rep["mutation_drop_state_50"] = {"six_zero_sites": len(six), "cases_six": r6.cases,
                                     "failures_six": len(r6.failures), "cases_rest": r5.cases,
                                     "failures_rest": len(r5.failures)}

    if "--upstream" in sys.argv:
        for rel in UPSTREAM:
            fetch(rel, None)
        out = HERE / "cache" / "upstream-run"
        cmd = [sys.executable, "-B", str(HERE / "cache" / UPSTREAM[0]),
               str(paths["k215.native.tm"].resolve()), str(paths["sites215.json"].resolve()), str(out.resolve())]
        subprocess.run(cmd, capture_output=True, text=True, timeout=3600)
        rt = json.loads((out / "runtime.json").read_text()) if (out / "runtime.json").exists() else {}
        rep["upstream_checker"] = {k: rt.get(k) for k in ("status", "proved_cases", "expected_cases", "seconds")}

    s, d, m = rep["startup"], rep["decoder"], rep["mutation_drop_state_50"]
    ok = (rep["shape"]["dense_rewrite_identical"] and rep["native_dense_lockstep_20000"]
          and (s["steps"], s["state"], s["head"], s["ones"], s["spares"]) == (95714, 83, -8, 95, 40)
          and s["spares_all_value_1"] and rep["site_sweep"]["failures"] == 0
          and rep["site_sweep"]["rows_used"] == 430 and rep["site_sweep"]["guarded_cases"] == 6176
          and rep["exact_quotient_mergeable_pairs"] == [] and rep["source"]["distinct_subtrees"] == 202
          and d["errors"] == 0 and d["self_allocation_identical"]
          and m["failures_six"] == m["cases_six"] > 0 and m["failures_rest"] == 0
          and rep.get("upstream_checker", {}).get("status", "UNIVERSAL_MATHEMATICAL_PASS") == "UNIVERSAL_MATHEMATICAL_PASS")
    rep["status"] = "PASS" if ok else "FAIL"
    rep["seconds"] = round(time.time() - t0, 1)
    (HERE / "evidence").mkdir(exist_ok=True)
    (HERE / "evidence" / "run.json").write_text(json.dumps(rep, indent=1) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps(rep, indent=1))
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
