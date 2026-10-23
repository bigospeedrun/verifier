"""Independent exact recomputation of the Sidorenko residual finite maximum.

This is an independent implementation, written from the written definitions
in the source (proof.tex, section "Sequential basis count for the nondirect
residual", proposition prop:residual-189, and sequential-refinement.md, both
in rohanarun/sidorenko-template-refinements at the pinned commit).  It does
not run, import, or adapt the author's audit_sequential.py; agreement with
the author's saved output was checked only after this computation ran.

Definitions audited (all arithmetic is exact integer / Fraction):

  * The input is a 13-point complex: 22 triangular faces and, per face, a
    3-bit cut vector ("bits").  A pair {i, j} is an *allowed pair* when it
    lies in exactly two faces whose bit vectors differ in exactly one
    coordinate.  This gives the allowed graph (28 pairs), which must be
    connected.
  * For a vertex of active degree d, phi(d, x) = C(x, 2) + (2d - x) x is
    the per-vertex bound on the summed earlier local dimensions, and
    phi(d, x) <= d (2d - 1) with equality exactly at x in {2d - 1, 2d}.
  * A relaxed defect-one stratum is a support S (a vertex subset whose
    induced allowed subgraph has at least one pair and no isolated vertex),
    a span k >= 2, and local dimensions x_i with 2 <= x_i <= min(k, 2 d_i)
    (d_i the induced degree in S) and sum_i x_i = 2k + 1.  Its relaxed
    remainder is
        floor( ( max sum_i phi(d_i, x_i)  +  pair_excess ) / 2 ) - 2m,
    where m is the number of active pairs in S and pair_excess is the
    maximum, over active pairs {a, b}, of min(k, 2 d_a) + min(k, 2 d_b) - 1.
  * The closed form on the full graph is sum_i d_i^2 - 3m + floor(excess/2)
    with excess = max over allowed pairs of 2 d_a + 2 d_b - 1.
  * For defect d >= 2 the source bounds R <= base + (23/2) n1 + (k + 11) n2
    with d = n1 + 2 n2 and k <= 2m - 1; the audit evaluates the resulting
    exact rational ratio bound on the author's grid and beyond it.

The per-stratum maximum of sum_i phi is computed three independent ways
(an integer dynamic program, a marginal-gain greedy allocation, and a
Lagrangian dual certificate) and by brute force wherever the composition
count is small; all must agree exactly.  Standard library only.
"""

import heapq
import json
import random
import time
from fractions import Fraction as Q
from pathlib import Path


# ---------------------------------------------------------------- inputs

def hamming(a, b):
    return sum(x != y for x, y in zip(a, b))


def load_and_check_inputs(data):
    """Validate the taken-as-given complex data; return derived structures.

    The faces/bits are the audit's only inputs.  Everything checked here is
    internal consistency of that data (a closed triangulated sphere with
    well-formed cut bits, and the file's own redundant pair_separations
    record agreeing with faces and bits), so a corrupted input file is
    detected before any counting happens.
    """
    points = data["points"]
    faces = [tuple(f) for f in data["faces"]]
    bits = list(data["bits"])
    problems = []
    if points != 13:
        problems.append("points != 13")
    if len(faces) != 22 or len(bits) != 22:
        problems.append("expected 22 faces and 22 bit vectors")
    for f in faces:
        if len(f) != 3 or len(set(f)) != 3 or not all(0 <= v < points for v in f):
            problems.append("malformed face %r" % (f,))
    for b in bits:
        if len(b) != 3 or any(c not in "01" for c in b):
            problems.append("malformed bit vector %r" % (b,))
    if problems:
        raise ValueError("input consistency: " + "; ".join(problems))

    pair_faces = {}
    for idx, face in enumerate(faces):
        for a, b in ((face[0], face[1]), (face[0], face[2]), (face[1], face[2])):
            pair_faces.setdefault((a, b), []).append(idx)
    counts = {len(v) for v in pair_faces.values()}
    if counts != {2}:
        raise ValueError("not a closed surface: pair face-counts %r" % (counts,))
    n_pairs = len(pair_faces)
    euler = points - n_pairs + len(faces)
    if euler != 2:
        raise ValueError("Euler characteristic %d != 2" % euler)

    seps = {}
    for pair, sep in data["pair_separations"]:
        seps[tuple(pair)] = sep
    if set(seps) != set(pair_faces):
        raise ValueError("pair_separations keys differ from face pairs")
    for pair, (i, j) in pair_faces.items():
        if seps[pair] != hamming(bits[i], bits[j]):
            raise ValueError("pair_separations mismatch at %r" % (pair,))

    allowed = sorted(pair for pair, (i, j) in pair_faces.items()
                     if hamming(bits[i], bits[j]) == 1)
    degrees = [0] * points
    neighbours = {v: set() for v in range(points)}
    for a, b in allowed:
        degrees[a] += 1
        degrees[b] += 1
        neighbours[a].add(b)
        neighbours[b].add(a)
    seen, stack = set(), [0]
    while stack:
        v = stack.pop()
        if v not in seen:
            seen.add(v)
            stack.extend(neighbours[v])
    if seen != set(range(points)):
        raise ValueError("allowed graph is not connected")
    return {
        "points": points,
        "faces": faces,
        "bits": bits,
        "surface_pairs": n_pairs,
        "euler": euler,
        "allowed_edges": [list(e) for e in allowed],
        "allowed_degrees": degrees,
    }


# ---------------------------------------------------------------- phi

def phi(d, x):
    """Per-vertex bound: C(x, 2) + (2d - x) x, exact integer."""
    return x * (x - 1) // 2 + (2 * d - x) * x


def check_vertex_bound(d_max):
    """Exhaustively verify phi(d, x) <= d(2d - 1) for 0 <= d <= d_max and
    0 <= x <= 2d + 2, with equality exactly at x in {2d - 1, 2d} (d >= 1)."""
    for d in range(0, d_max + 1):
        peak = d * (2 * d - 1)
        for x in range(0, 2 * d + 3):
            v = phi(d, x)
            if v > peak:
                return False
            if d >= 1 and (v == peak) != (x in (2 * d - 1, 2 * d)):
                return False
    return True


# ------------------------------------------------------- allocation maxima
# items: tuple of (degree, cap), sorted descending.  Each local dimension
# x_i ranges over [2, cap_i]; the total sum_i x_i is prescribed.

def alloc_dp_table(items):
    """Integer DP over totals: dict total -> max sum phi.  List based."""
    table = {0: 0}
    for d, cap in items:
        values = [phi(d, x) for x in range(2, cap + 1)]
        new = {}
        for total, acc in table.items():
            for off, v in enumerate(values):
                t = total + 2 + off
                nv = acc + v
                if nv > new.get(t, -1):
                    new[t] = nv
        table = new
    return table


def alloc_greedy(items, total):
    """Marginal-gain allocation with a heap.  phi(d, .) has nonincreasing
    integer marginal gains phi(d, x + 1) - phi(d, x) = 2d - x - 1, so the
    greedy allocation is exact for this concave separable problem."""
    xs = [2] * len(items)
    remaining = total - 2 * len(items)
    if remaining < 0:
        return None
    heap = []
    for t, (d, cap) in enumerate(items):
        if xs[t] < cap:
            heap.append((-(phi(d, xs[t] + 1) - phi(d, xs[t])), t))
    heapq.heapify(heap)
    while remaining:
        if not heap:
            return None
        _, t = heapq.heappop(heap)
        d, cap = items[t]
        if xs[t] >= cap:
            continue
        xs[t] += 1
        remaining -= 1
        if xs[t] < cap:
            heapq.heappush(heap, (-(phi(d, xs[t] + 1) - phi(d, xs[t])), t))
    return sum(phi(d, x) for (d, _), x in zip(items, xs))


def alloc_dual(items, total):
    """Lagrangian dual certificate: min over integer lambda of
    sum_i max_x (phi(d_i, x) - lambda x) + lambda * total.  Every lambda
    gives an upper bound on the allocation maximum; for this concave
    separable problem the minimum over integer lambda equals it exactly."""
    gains = [phi(d, x + 1) - phi(d, x)
             for d, cap in items for x in range(2, cap)]
    lo = min(gains + [0]) - 1
    hi = max(gains + [0]) + 1
    best = None
    for lam in range(lo, hi + 1):
        bound = lam * total
        for d, cap in items:
            bound += max(phi(d, x) - lam * x for x in range(2, cap + 1))
        if best is None or bound < best:
            best = bound
    return best


def alloc_bruteforce(items, total):
    """Recursive enumeration of all compositions; small instances only."""
    best = [None]

    def rec(t, remaining, acc):
        if t == len(items):
            if remaining == 0 and (best[0] is None or acc > best[0]):
                best[0] = acc
            return
        d, cap = items[t]
        rest_min = 2 * (len(items) - t - 1)
        rest_max = sum(c for _, c in items[t + 1:])
        for x in range(2, cap + 1):
            r = remaining - x
            if rest_min <= r <= rest_max:
                rec(t + 1, r, acc + phi(d, x))

    rec(0, total, 0)
    return best[0]


def check_allocation_methods(trials=4000, seed=20261023):
    """Random small instances: DP, greedy and dual must agree on every
    feasible total; brute force too wherever the composition count allows.
    Returns (ok, brute_force_checks)."""
    rng = random.Random(seed)
    brute_checked = 0
    for _ in range(trials):
        n = rng.randint(1, 6)
        items = tuple(sorted(
            ((rng.randint(0, 5), rng.randint(2, 9)) for _ in range(n)),
            reverse=True))
        table = alloc_dp_table(items)
        lo = 2 * n
        hi = sum(c for _, c in items)
        for total in range(lo, hi + 1):
            dp = table.get(total)
            if dp is None:
                continue
            if alloc_greedy(items, total) != dp:
                return False, brute_checked
            if alloc_dual(items, total) != dp:
                return False, brute_checked
            leaves = 1
            for _, c in items:
                leaves *= (c - 1)
            if leaves <= 200000:
                if alloc_bruteforce(items, total) != dp:
                    return False, brute_checked
                brute_checked += 1
    return True, brute_checked


# ------------------------------------------------------------- strata

def enumerate_strata(allowed, points, dp_cache, brute_limit=200000,
                     on_support=None):
    """Exhaust the relaxed defect-one strata over all 2^points supports.

    Returns (summary, support_rows, strata_rows).  Every distinct
    (items, total) local-maximum problem is cross-checked by the greedy
    allocation and the dual certificate, and by brute force when the
    composition count is below brute_limit; the checks are pure functions
    of (items, total), so they are memoized and every stratum is covered
    by a triple-checked value.  A disagreement raises.  on_support, if
    given, is called with each support row as it is produced."""
    cases = 0
    supports = 0
    best = None
    maximizers = []
    support_rows = []
    strata_rows = []
    agreement = {"strata_covered": 0,
                 "distinct_triple_checked": 0,
                 "bruteforce_checked": 0}
    verified = {}
    for mask in range(1 << points):
        vertices = [i for i in range(points) if mask & (1 << i)]
        edges = [e for e in allowed if mask & (1 << e[0]) and mask & (1 << e[1])]
        degree = {i: 0 for i in vertices}
        for a, b in edges:
            degree[a] += 1
            degree[b] += 1
        if not edges or any(degree[i] == 0 for i in vertices):
            continue
        supports += 1
        m = len(edges)
        sup_best = None
        sup_cases = 0
        # Completeness of the k scan: feasibility needs
        # 2k + 1 <= sum_i min(k, 2 d_i) <= 2 * sum_i d_i = 4m, hence
        # k <= 2m - 1/2.  Scanning k in [2, 2m] therefore covers every
        # feasible stratum (k = 2m itself is infeasible by the same bound).
        for k in range(2, 2 * m + 1):
            items = tuple(sorted(
                ((degree[i], min(k, 2 * degree[i])) for i in vertices),
                reverse=True))
            total = 2 * k + 1
            if not 2 * len(vertices) <= total <= sum(c for _, c in items):
                continue
            if items not in dp_cache:
                dp_cache[items] = alloc_dp_table(items)
            local = dp_cache[items].get(total)
            if local is None:
                raise ValueError("feasible predicate but DP infeasible")
            key = (items, total)
            if key not in verified:
                if alloc_greedy(items, total) != local:
                    raise ValueError("greedy disagrees with DP")
                if alloc_dual(items, total) != local:
                    raise ValueError("dual certificate disagrees with DP")
                agreement["distinct_triple_checked"] += 1
                leaves = 1
                for _, c in items:
                    leaves *= (c - 1)
                if leaves <= brute_limit:
                    if alloc_bruteforce(items, total) != local:
                        raise ValueError("brute force disagrees with DP")
                    agreement["bruteforce_checked"] += 1
                verified[key] = local
            elif verified[key] != local:
                raise ValueError("memoized value disagrees with DP")
            agreement["strata_covered"] += 1
            pair_excess = max(min(k, 2 * degree[a]) + min(k, 2 * degree[b]) - 1
                              for a, b in edges)
            remainder = (local + pair_excess) // 2 - 2 * m
            cases += 1
            sup_cases += 1
            record = {"support_mask": mask, "vertices": vertices,
                      "active_pairs": m, "span": k,
                      "local_phi_sum": local, "pair_excess": pair_excess,
                      "remainder": remainder}
            strata_rows.append(record)
            if sup_best is None or remainder > sup_best:
                sup_best = remainder
            if best is None or remainder > best:
                best, maximizers = remainder, [record]
            elif remainder == best:
                maximizers.append(record)
        row = {"support_mask": mask, "vertices": vertices,
               "active_pairs": m, "strata": sup_cases,
               "support_max": sup_best}
        support_rows.append(row)
        if on_support is not None:
            on_support(row)
    summary = {"all_support_masks": 1 << points,
               "supports_without_isolates": supports,
               "relaxed_defect_one_cases": cases,
               "refined_remainder": best,
               "maximizers": maximizers,
               "agreement": agreement}
    return summary, support_rows, strata_rows


# ------------------------------------------------------- closed form etc.

def closed_form(degrees, edges):
    vertex_total = sum(d * (2 * d - 1) for d in degrees)
    deg_sq = sum(d * d for d in degrees)
    m = len(edges)
    if vertex_total % 2:
        raise ValueError("vertex total must be even")
    base = vertex_total // 2 - 2 * m
    if base != deg_sq - 3 * m:
        raise ValueError("base identity fails")
    excess = max(2 * degrees[a] + 2 * degrees[b] - 1 for a, b in edges)
    return {"vertex_bound_sum": vertex_total, "sum_deg_sq": deg_sq,
            "base_remainder": base, "pair_excess_max": excess,
            "closed_form_remainder": base + excess // 2}


def higher_defect_ratio(base, excess, m_all):
    """The source's grid for defect d >= 2: d in [2, 4 m_all],
    d = one + 2 * two, span k in [2, 2 m_all - 1],
    value = base + (excess/2) * one + (k + (excess - 1)/2) * two.
    Exact Fractions.  Returns (max ratio, attaining (d, two, k) list)."""
    best = None
    where = []
    for d in range(2, 4 * m_all + 1):
        for two in range(0, d // 2 + 1):
            one = d - 2 * two
            for k in range(2, 2 * m_all):
                value = base + Q(excess, 2) * one + (k + Q(excess - 1, 2)) * two
                ratio = value / d
                if best is None or ratio > best:
                    best, where = ratio, [(d, two, k)]
                elif ratio == best:
                    where.append((d, two, k))
    return best, where


def higher_defect_ratio_extension(base, excess, m_all, d_max=100000):
    """Beyond the source's grid: for fixed d the value is linear in `two`
    with slope (k + (excess-1)/2) - excess, and increasing in k when
    two > 0, so per d only the extreme splits at the maximal span need
    evaluating.  Exact Fractions; returns the max ratio over 2 <= d <= d_max."""
    best = None
    k_max = 2 * m_all - 1
    for d in range(2, d_max + 1):
        for two in (0, d // 2):
            one = d - 2 * two
            value = base + Q(excess, 2) * one + (k_max + Q(excess - 1, 2)) * two
            ratio = value / d
            if best is None or ratio > best:
                best = ratio
    return best


# ------------------------------------------------------- graph controls

def stratum_max_for_graph(edges, points):
    """Run the stratum machinery on an arbitrary small graph (controls)."""
    allowed = sorted(tuple(e) for e in edges)
    summary, _, _ = enumerate_strata(allowed, points, {})
    return summary


def check_graph_controls():
    """Hand-computed small graphs, run through the same machinery.

    Path 0-1-2 (degrees 1, 2, 1; m = 2): the only feasible stratum is the
    full support at span 3, caps (2, 3, 2), total 7, the unique allocation
    (2, 3, 2) with phi sum 1 + 6 + 1 = 8, pair excess 4, remainder
    (8 + 4)/2 - 4 = 2.  Closed form: sum d^2 - 3m = 6 - 6 = 0, excess 5,
    0 + floor(5/2) = 2.  A single pair (m = 1) admits no stratum (span 2
    needs total 5 > 2 + 2).  The triangle (degrees 2, 2, 2; m = 3) is
    checked against a direct brute-force over allocations done here by a
    separate loop.
    """
    s = stratum_max_for_graph([(0, 1), (1, 2)], 3)
    if s["relaxed_defect_one_cases"] != 1 or s["refined_remainder"] != 2:
        return False
    mx = s["maximizers"][0]
    if not (mx["support_mask"] == 0b111 and mx["span"] == 3
            and mx["local_phi_sum"] == 8 and mx["pair_excess"] == 4):
        return False
    s = stratum_max_for_graph([(0, 1)], 2)
    if s["relaxed_defect_one_cases"] != 0:
        return False
    # Triangle, brute-forced independently of enumerate_strata's inner path.
    edges = [(0, 1), (0, 2), (1, 2)]
    s = stratum_max_for_graph(edges, 3)
    brute_best = None
    for k in range(2, 2 * 3 + 1):
        total = 2 * k + 1
        caps = [min(k, 4)] * 3
        if not 6 <= total <= sum(caps):
            continue
        items = tuple(sorted(((2, c) for c in caps), reverse=True))
        local = alloc_bruteforce(items, total)
        pe = max(caps[a] + caps[b] - 1 for a, b in edges)
        rem = (local + pe) // 2 - 6
        if brute_best is None or rem > brute_best:
            brute_best = rem
    if s["refined_remainder"] != brute_best:
        return False
    return True


# ------------------------------------------------------------- driver

def run_audit(data, checkpoint_path=None):
    """Full audit.  If checkpoint_path is given, per-support rows are
    appended to it block by block (one JSON object per line) as the
    enumeration proceeds, so an interrupted run leaves its progress on
    disk; the returned summary is authoritative either way."""
    t0 = time.time()
    phases = {}
    graph = load_and_check_inputs(data)
    phases["inputs"] = time.time() - t0

    t = time.time()
    if not check_vertex_bound(30):
        raise ValueError("vertex bound control failed")
    ok_alloc, brute_n = check_allocation_methods()
    if not ok_alloc:
        raise ValueError("allocation methods disagree on random instances")
    if not check_graph_controls():
        raise ValueError("graph controls failed")
    phases["controls"] = time.time() - t

    t = time.time()
    cf = closed_form(graph["allowed_degrees"],
                     [tuple(e) for e in graph["allowed_edges"]])
    phases["closed_form"] = time.time() - t

    t = time.time()
    ckpt_fh = None
    on_support = None
    if checkpoint_path is not None:
        ckpt_fh = open(checkpoint_path, "w")

        def on_support(row):
            ckpt_fh.write(json.dumps(row, sort_keys=True) + "\n")
            ckpt_fh.flush()
    try:
        summary, support_rows, strata_rows = enumerate_strata(
            [tuple(e) for e in graph["allowed_edges"]], graph["points"], {},
            on_support=on_support)
    finally:
        if ckpt_fh is not None:
            ckpt_fh.close()
    phases["enumeration"] = time.time() - t

    t = time.time()
    ratio, ratio_where = higher_defect_ratio(
        cf["base_remainder"], cf["pair_excess_max"], len(graph["allowed_edges"]))
    ratio_ext = higher_defect_ratio_extension(
        cf["base_remainder"], cf["pair_excess_max"], len(graph["allowed_edges"]))
    phases["higher_defect"] = time.time() - t

    import hashlib
    canonical = json.dumps(strata_rows, sort_keys=True,
                           separators=(",", ":")).encode()
    result = {
        "allowed_edges": graph["allowed_edges"],
        "allowed_degrees": graph["allowed_degrees"],
        "surface_pairs": graph["surface_pairs"],
        "euler": graph["euler"],
        "vertex_bound_sum": cf["vertex_bound_sum"],
        "sum_deg_sq": cf["sum_deg_sq"],
        "base_remainder": cf["base_remainder"],
        "pair_excess_max": cf["pair_excess_max"],
        "closed_form_remainder": cf["closed_form_remainder"],
        "all_support_masks": summary["all_support_masks"],
        "supports_without_isolates": summary["supports_without_isolates"],
        "relaxed_defect_one_cases": summary["relaxed_defect_one_cases"],
        "refined_remainder": summary["refined_remainder"],
        "maximizers": summary["maximizers"],
        "method_agreement": summary["agreement"],
        "random_allocation_bruteforce_checks": brute_n,
        "higher_defect_ratio_max": str(ratio),
        "higher_defect_ratio_attained_at": [list(w) for w in ratio_where],
        "higher_defect_ratio_extension_max": str(ratio_ext),
        "strata_table_sha256": hashlib.sha256(canonical).hexdigest(),
        "support_rows": support_rows,
        "phase_seconds": {k: round(v, 3) for k, v in phases.items()},
        "total_seconds": round(time.time() - t0, 3),
    }
    return result


if __name__ == "__main__":
    import sys
    src = Path(sys.argv[1]) if len(sys.argv) > 1 else None
    out = Path(sys.argv[2]) if len(sys.argv) > 2 else None
    ckpt = Path(sys.argv[3]) if len(sys.argv) > 3 else None
    data = json.loads(src.read_text())
    result = run_audit(data, checkpoint_path=ckpt)
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if out:
        out.write_text(text)
    print(json.dumps({k: result[k] for k in (
        "closed_form_remainder", "refined_remainder",
        "relaxed_defect_one_cases", "supports_without_isolates",
        "higher_defect_ratio_max", "total_seconds")}, indent=2))
