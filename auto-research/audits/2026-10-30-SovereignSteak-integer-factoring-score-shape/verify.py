#!/usr/bin/env python3
"""Arithmetic check for the integer-factoring score audit.

This does not claim a new factoring bound. It checks three calculations
about Isaac Rudich and Louis-Martin Rousseau's proof at commit c91cc3f:

1. The written cutoff in small_zC only fires once the level count is
   linear in the score parameter k. A linear level budget cannot meet
   any positive board score, because the machine only has
   O(log log n) levels.
2. The explicit width decay of 23/24 per level, with the group
   recurrence Kb(d+1) = 9 Kb(d)^16, meets board score
   ln(24/23) / ln(16) after the proof's polynomial blow-up in the
   level count. It does not meet any larger score. Comparisons stay
   in log space so the galactic thresholds do not overflow.
3. SqrtLogLogConjecture has board score 1/2. That is strictly above
   the structural rate of this grouping. Reaching 1/2 with the same
   shrink would need groups to grow by (24/23)^2 per level, not by
   a 16th power.

Run from a clone of bigospeedrun/verifier:

    python3 -I -B auto-research/audits/2026-10-30-SovereignSteak-integer-factoring-score-shape/verify.py
"""

from __future__ import annotations

import math

# Pinned Lean constants. Every derived number is recomputed from these.
K0 = 48
GROUP_MUL = 9
GROUP_POW = 16
LEVEL_POWER = 40
DECAY_NUM = 23
DECAY_DEN = 24
CHARGE_NUM = 14
WIDTH_FACTOR = 2882
# Ntn <= 10350 n on a good pair, from S_le_n and Gs = 3 Kb^8.
# See the README for the arithmetic. The leading piece of W0 is at most
# this constant times (23/24)^ell.
WIDTH_LEADING = 10350
# Pointwise, UniFinal's formulas give log2(machine time) <= 6*log2(B) + O(log n):
# S = 200(n+1)^3(B+1), T = Q(n+k0+S+1)^2, time <= cc(T+n+1)^3.
# B is the engine cost (64(V+1)^3)^(24*ell+84) and V = 2^(16*Z+127), so the
# leading term is 6 * (24*ell+84) * 3 * 16 * Z. The written uni_time_le spends
# 24 in place of this 6; that only multiplies the prefactor. 6 * 3 * 16 = 288.
ENGINE_EXPONENT_FACTOR = 6 * 3 * 16
ENGINE_LEVEL_COEFF = 24
ENGINE_LEVEL_ADD = 84
# ev_W's witness. small_zC calls ev_W, so its inequality is not proved below this.
EV_W_LEVEL = 45451759374148

LN2 = math.log(2)
ALPHA_23 = math.log(DECAY_DEN / DECAY_NUM) / math.log(GROUP_POW)
ALPHA_11 = math.log(12 / 11) / math.log(GROUP_POW)


def kb_closed_parts() -> tuple[float, float]:
    """log2(Kb(d)) = A * 16^d + B, with B the fixed point of x |-> log2(9) + 16x."""
    log_mul = math.log2(GROUP_MUL)
    fixed = -log_mul / (GROUP_POW - 1)
    scale = math.log2(K0) - fixed
    return scale, fixed


def log2_kb(depth: int) -> float:
    value = math.log2(K0)
    for _ in range(depth):
        value = math.log2(GROUP_MUL) + GROUP_POW * value
    return value


def ln_log2_n_right(ell: int) -> float:
    """ln(log2 n) at the right edge of the ell-level bucket.

    The right edge is the last n that still has ellOf n = ell, just below
    Kb(ell+1)^40. Using log2(Kb(ell+1)) = A * 16^{ell+1} (dropping the
    negative fixed point B) overestimates log2 n, which makes every
    positive-score inequality harder. A pass is therefore valid for the
    real, slightly smaller, edge.
    """
    scale, _fixed = kb_closed_parts()
    return math.log(LEVEL_POWER * scale) + (ell + 1) * math.log(GROUP_POW)


def exponent_multiplier(ell: int) -> float:
    return ENGINE_EXPONENT_FACTOR * (ENGINE_LEVEL_COEFF * ell + ENGINE_LEVEL_ADD)


def ln_structural_ratio(ell: int) -> float:
    """ln(log2(time) / n) for the leading 23/24 piece, including the blow-up."""
    return (
        math.log(exponent_multiplier(ell))
        + math.log(WIDTH_LEADING)
        + ell * math.log(DECAY_NUM / DECAY_DEN)
    )


def proof_level_demand(k: int) -> float:
    """Levels small_zC asks for before its sufficient condition can hold.

    D = 80696 k with 80696 = 2 * 14 * 2882. ev_W0 is called at
    a = 2 k 24^D and needs 2 a 2882 (23/24)^ell <= 1, i.e.
    (24/23)^ell >= 4 * 2882 * k * 24^(80696 k).
    """
    if k < 1:
        raise ValueError(k)
    d_coeff = 2 * CHARGE_NUM * WIDTH_FACTOR
    if d_coeff != 80696:
        raise AssertionError(d_coeff)
    ln_base = math.log(4 * WIDTH_FACTOR * k) + d_coeff * k * math.log(DECAY_DEN)
    return ln_base / math.log(DECAY_DEN / DECAY_NUM)


def check_recurrence() -> None:
    scale, fixed = kb_closed_parts()
    for depth in range(0, 12):
        closed = scale * (GROUP_POW ** depth) + fixed
        got = log2_kb(depth)
        if abs(got - closed) > 1e-6 * max(1.0, got):
            raise AssertionError((depth, got, closed))
    one_level_bits = log2_kb(1) * LEVEL_POWER
    if not (3700 < one_level_bits < 3710):
        raise AssertionError(one_level_bits)


def ln_gap_lower(eps: float, ell: int, demand_at_1: float) -> float:
    """Lower bound of ln((log2 n)^eps / k_opt) at the left edge of the bucket.

    log2(Kb(ell)) > log2(48) * 16^ell, so log2 n > 40 * log2(48) * 16^ell.
    Underestimating log2 n makes (log2 n)^eps smaller, so a positive gap
    still witnesses k_opt < (log2 n)^eps. k_opt = ell / demand(1) is the
    optimistic reading of small_zC's linear level demand, ignoring the
    absolute ev_W floor.
    """
    ln_log_lower = math.log(LEVEL_POWER * math.log2(K0)) + ell * math.log(GROUP_POW)
    return eps * ln_log_lower - math.log(ell / demand_at_1)


def check_cutoff_blocks_positive_score() -> None:
    if EV_W_LEVEL != 45451759374148:
        raise AssertionError(EV_W_LEVEL)
    if EV_W_LEVEL < 10**13:
        raise AssertionError(EV_W_LEVEL)
    demand_at_1 = proof_level_demand(1)
    if not (6.0e6 < demand_at_1 < EV_W_LEVEL):
        raise AssertionError(demand_at_1)
    for k in (1, 2, 5, 20):
        if proof_level_demand(k) < 6.0e6 * k:
            raise AssertionError((k, proof_level_demand(k)))
    # On every bucket whose Kb value fits in a float, the optimistic budget
    # k <= ell / demand(1) is already below (log2 n)^eps. The literal proof
    # has not started: ev_W asks for ell >= EV_W_LEVEL.
    for eps in (0.001, 0.01, 0.1):
        for ell in range(1, 12):
            if ell >= EV_W_LEVEL:
                raise AssertionError(ell)
            log2_n = LEVEL_POWER * log2_kb(ell)
            k_opt = ell / demand_at_1
            if k_opt >= log2_n ** eps:
                raise AssertionError((eps, ell, k_opt, log2_n))
    # The gap is not monotone at small ell: d/dell of the log gap is
    # eps*ln(16) - 1/ell, so it decreases until ell ≈ 1/(eps ln 16) and
    # increases after that. Past that threshold the gap keeps growing.
    for eps in (0.001, 0.01, 0.1):
        threshold = 1.0 / (eps * math.log(GROUP_POW))
        start = math.floor(threshold) + 2
        previous = ln_gap_lower(eps, start, demand_at_1)
        if previous <= 0:
            raise AssertionError((eps, start, previous))
        for step in range(1, 41):
            current = ln_gap_lower(eps, start + step, demand_at_1)
            if current <= previous:
                raise AssertionError((eps, start + step, current, previous))
            previous = current


def check_width_constant() -> None:
    """Ntn <= 10350 n on a good pair. See the README for the same steps."""
    if 8 ** 0.75 >= 5:
        raise AssertionError(8 ** 0.75)
    # (2^s)^4 <= 4n+4 <= 8n, so 720 of those is <= 5760 n.
    # G <= 3 n^{1/5} and (2^s)^3 < 5 n^{3/4}, so 306 G (2^s)^3 < 4590 n.
    leading = 720 * 8
    grid = 306 * 3 * 5
    if leading + grid != WIDTH_LEADING:
        raise AssertionError((leading, grid, WIDTH_LEADING))


def check_structural_score() -> int:
    alpha = ALPHA_23
    if not (0.015 < alpha < 0.016):
        raise AssertionError(alpha)
    if not (0.031 < ALPHA_11 < 0.032):
        raise AssertionError(ALPHA_11)
    if not (ALPHA_11 > 2 * alpha):
        raise AssertionError((ALPHA_11, alpha))

    def meets(target: float, eps: float, ell: int) -> bool:
        ln_allowed = -(target - eps) * ln_log2_n_right(ell)
        return ln_structural_ratio(ell) <= ln_allowed

    eps = 0.001
    first = None
    for ell in range(1, 20_001):
        if meets(alpha, eps, ell):
            first = ell
            break
    if first is None:
        raise AssertionError("23/24 decay did not meet its score by ell=20000")
    for ell in (first, first + 10, first + 100, 20_000):
        if not meets(alpha, eps, ell):
            raise AssertionError(ell)
    # One thousandth above the structural score stays false on that range.
    # With eps = 0.001 this asks for the pure power alpha, and the blow-up
    # 288*(24 ell+84)*10350 stays larger than the constant hidden in
    # log2(n) ~ 16^ell.
    for ell in (1, first, 20_000):
        if meets(alpha + 0.001, eps, ell):
            raise AssertionError(ell)

    # The top-level piece O(n^{639/640}) is below the 23/24 piece.
    # At the right edge log2(n) > 20 A 16^{ell+1}, so
    # log2(n)/640 > (ln2 * A * 16^ell) / 2 after converting, which beats
    # ell * ln(24/23) + ln(WIDTH_LEADING).
    scale, _fixed = kb_closed_parts()
    junk_power = (LEVEL_POWER * GROUP_POW - 1) / (LEVEL_POWER * GROUP_POW)
    if abs(junk_power - (639 / 640)) > 1e-12:
        raise AssertionError(junk_power)
    for ell in range(1, 80):
        ln_lower = math.log(LN2 * scale / 2) + ell * math.log(GROUP_POW)
        ln_need = math.log(ell * math.log(DECAY_DEN / DECAY_NUM) + math.log(WIDTH_LEADING))
        if ln_lower <= ln_need:
            raise AssertionError((ell, ln_lower, ln_need))

    # The G^4 term in W0 is 2*ell*(3 P^8)^4 = 162*ell*P^32 <= 162*ell*n^{4/5}.
    # At the left edge this is below the 23/24 piece: n^{1/5} beats
    # ell*(24/23)^ell. log2_kb stays inside the float range on this loop.
    for ell in range(1, 41):
        log2_n = LEVEL_POWER * log2_kb(ell)
        ln_width = 0.2 * LN2 * log2_n
        ln_need = math.log(162 * ell) + ell * math.log(DECAY_DEN / DECAY_NUM)
        if ln_width <= ln_need:
            raise AssertionError((ell, ln_width, ln_need))

    # Level d is charged about 14 N / Kb(d), and the stored invariant gives
    # N <= (24/23)^{d+1} W0. Against the bottom brute-force term W0, the
    # ratio is 14 (24/23)^{d+1} / Kb(d). It is < 1 at d = 0. For d >= 1 the
    # ratio is largest at d = 1 and then falls, because log2(Kb) grows by
    # a factor 16. The check is that this log-gap already exceeds ln(14)+10
    # at d = 1 and keeps growing.
    if 14 * (DECAY_DEN / DECAY_NUM) / K0 >= 1:
        raise AssertionError(14 * (DECAY_DEN / DECAY_NUM) / K0)
    previous_gap = None
    for depth in range(1, 13):
        gap = LN2 * log2_kb(depth) - (depth + 1) * math.log(DECAY_DEN / DECAY_NUM)
        if gap <= math.log(14) + 10:
            raise AssertionError((depth, gap))
        if previous_gap is not None and gap <= previous_gap:
            raise AssertionError((depth, gap, previous_gap))
        previous_gap = gap
    return first


def check_conjecture_score() -> None:
    """C * n / (sqrt(log2 n) + 1) is score 1/2 and not score 0.51."""

    def ln_ratio(ln_log2_n: float, constant: int) -> float:
        # ratio = constant / (sqrt(log2 n) + 1) < constant / sqrt(log2 n)
        # ln(ratio) < ln(constant) - 0.5 * ln_log2_n
        return math.log(constant) - 0.5 * ln_log2_n

    for constant in (1, 10, 10_000):
        # (log2 n)^0.01 >= constant once ln(log2 n) is past ln(constant)/0.01.
        for ln_log in (2000.0, 4000.0):
            eps = 0.01
            ln_allowed = -(0.5 - eps) * ln_log
            if ln_ratio(ln_log, constant) > ln_allowed:
                raise AssertionError((constant, ln_log))
        # Without the eps slack, constant / sqrt(log n) misses score 0.51
        # whenever constant > 1. The conjecture carries such a constant.
        if constant > 1 and ln_ratio(4000.0, constant) <= -0.5 * 4000.0:
            raise AssertionError(constant)


def check_literal_theorem_is_score_zero() -> None:
    """The forall-k theorem is score 0. One fixed k is not.

    Score 0 asks that for every eps > 0, time <= 2^(eps n) for all large n.
    Some k with 1/k <= eps supplies that, once C_k is absorbed. One fixed k
    misses every smaller eps, and it also misses every positive score:
    (log2 n)^alpha eventually exceeds that k. The threshold is galactic for
    small alpha, so the comparison stays in log space.
    """
    for eps in (0.1, 0.01, 0.001):
        k = math.floor(1.0 / eps) + 1
        if 1.0 / k > eps:
            raise AssertionError((eps, k))
    for k in (1, 100, 10_000):
        eps = 1.0 / (k + 1)
        if 1.0 / k <= eps:
            raise AssertionError((k, eps))
    for alpha in (0.001, ALPHA_23, 0.5):
        for k in (1, 100, 10_000):
            ln_log = (math.log(k) + 1.0) / alpha
            if alpha * ln_log <= math.log(k):
                raise AssertionError((k, alpha, ln_log))


def check_half_score_needs_a_different_grouping() -> None:
    r_23 = (DECAY_DEN / DECAY_NUM) ** 2
    r_11 = (12 / 11) ** 2
    if not (1.08 < r_23 < 1.09):
        raise AssertionError(r_23)
    if not (1.18 < r_11 < 1.20):
        raise AssertionError(r_11)
    if GROUP_POW <= r_11:
        raise AssertionError(GROUP_POW)
    # alpha * ln(16) must be exactly ln(24/23).
    if abs(ALPHA_23 * math.log(GROUP_POW) - math.log(DECAY_DEN / DECAY_NUM)) > 1e-12:
        raise AssertionError(ALPHA_23)
    if 0.5 / ALPHA_23 < 16:
        raise AssertionError(0.5 / ALPHA_23)


def check_manifest() -> None:
    import hashlib
    import json
    from pathlib import Path

    here = Path(__file__).resolve().parent
    manifest = json.loads((here / "MANIFEST.json").read_text())
    if manifest.get("algorithm") != "sha256":
        raise AssertionError(manifest.get("algorithm"))
    files: dict[str, str] = {}
    for path in here.rglob("*"):
        if not path.is_file() or path.name == "MANIFEST.json":
            continue
        if "__pycache__" in path.parts:
            continue
        files[path.relative_to(here).as_posix()] = hashlib.sha256(path.read_bytes()).hexdigest()
    if files != manifest["sha256"]:
        raise AssertionError(sorted(set(files) ^ set(manifest["sha256"])))


def main() -> None:
    check_recurrence()
    check_width_constant()
    check_cutoff_blocks_positive_score()
    first = check_structural_score()
    check_conjecture_score()
    check_literal_theorem_is_score_zero()
    check_half_score_needs_a_different_grouping()
    demand = proof_level_demand(1)
    check_manifest()
    print("integer-factoring score audit: all checks passed")
    print(f"proof cutoff: ev_W needs ell >= {EV_W_LEVEL}, and ev_W0 needs ell >= {demand:.0f} at k = 1")
    print(f"structural score from 23/24 and 16-power groups: {ALPHA_23:.6f}")
    print(f"eps=0.001 absorption of the prefactor begins at ell = {first}")
    print(f"sharper score if the 11/12 factor from N_next is kept: {ALPHA_11:.6f}")
    print("SqrtLogLogConjecture scores 1/2 and is above both rates")
    print("literal theorem forall k. C_k * 2^(n/k) scores 0")


if __name__ == "__main__":
    main()
