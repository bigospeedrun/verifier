"""Independent exact-arithmetic audit; no upstream implementation is imported.

SPDX-License-Identifier: Apache-2.0
Mathematical sources and limits are in NOTICE.md and MATHEMATICS.md.
"""

from copy import deepcopy
from dataclasses import dataclass
from decimal import Decimal, localcontext
from fractions import Fraction as F
from functools import lru_cache


TERMS = 64
SCALE = 10**45


class Rejected(ValueError):
    """An audited precondition or strict inequality was not established."""


def need(condition, label):
    if not condition:
        raise Rejected(label)


@dataclass(frozen=True)
class Interval:
    lo: F
    hi: F

    def __post_init__(self):
        need(self.lo <= self.hi, "interval.order")

    def __add__(self, other):
        other = box(other)
        return Interval(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + -box(other)

    def __rsub__(self, other):
        return box(other) + -self

    def __mul__(self, other):
        other = box(other)
        endpoints = [a * b for a in (self.lo, self.hi)
                     for b in (other.lo, other.hi)]
        return Interval(min(endpoints), max(endpoints))

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = box(other)
        need(not other.lo <= 0 <= other.hi, "interval.zero_denominator")
        return self * Interval(1 / other.hi, 1 / other.lo)


def box(value):
    return value if isinstance(value, Interval) else Interval(F(value), F(value))


def floor(value):
    return value.numerator // value.denominator


def ceil(value):
    return -floor(-value)


def decimal_outward(value, upper=False, digits=24):
    scaled = value * 10**digits
    integer = ceil(scaled) if upper else floor(scaled)
    sign = "-" if integer < 0 else ""
    whole, fraction = divmod(abs(integer), 10**digits)
    return f"{sign}{whole}.{fraction:0{digits}d}"


def show(value):
    value = box(value)
    return {"lower": decimal_outward(value.lo),
            "upper": decimal_outward(value.hi, upper=True)}


@lru_cache(maxsize=None)
def log_unit(value):
    """Enclose ln(value), 1 <= value <= 2, using integer-rounded terms.

    For z=(value-1)/(value+1), sum 2*z^(2j+1)/(2j+1).
    Every term is rounded DOWN to an integer multiple of 10^-45.
    Add TERMS units for rounding and a geometric bound for the tail.
    All operations that determine an endpoint are exact.
    """
    need(1 <= value <= 2, "log_unit.domain")
    if value == 1:
        return box(0)
    z = (value - 1) / (value + 1)
    z2 = z * z
    power = z
    units = 0
    for j in range(TERMS):
        units += floor(2 * power * SCALE / (2 * j + 1))
        power *= z2
    tail = 2 * power / ((2 * TERMS + 1) * (1 - z2))
    return Interval(F(units, SCALE),
                    F(units + TERMS + ceil(tail * SCALE), SCALE))


@lru_cache(maxsize=None)
def log2(value):
    value = F(value)
    need(value > 0, "log2.domain")
    k = 0
    while value < 1:
        value *= 2
        k -= 1
    while value >= 2:
        value /= 2
        k += 1
    if value == 1:
        return box(k)
    return k + log_unit(value) / log_unit(F(2))


def entropy(value):
    need(0 < value < 1, "entropy.domain")
    return -value * log2(value) - (1 - value) * log2(1 - value)


def affine_sum(*terms):
    result = {}
    for scalar, coefficients in terms:
        for variable, coefficient in coefficients.items():
            result[variable] = result.get(variable, F(0)) + scalar * coefficient
    return {key: value for key, value in result.items() if value}


def affine_difference(left, right):
    return affine_sum((F(1), left), (F(-1), right))


def audit(data, *, correction_scale=F(1)):
    p = {key: F(value) for key, value in data["parameters"].items()}
    c = {key: F(value) for key, value in data["inherited_constants"].items()}
    tau, eta, a, mu, gamma, ell = (p[key] for key in
                                  ("tau", "eta", "a", "mu", "gamma", "l"))
    eps, zeta = p["epsilon"], p["zeta"]
    need(0 < a < F(1, 4), "domain.a")
    need(0 < mu < 1 and 0 < ell < 1 and gamma > 0, "domain.blocks")
    need(eps > 0 and zeta > 0, "domain.error_budgets")
    guard = p["input_guard_coefficient"]
    need(guard > 0 and guard.denominator == 1, "domain.integer_guard")
    theta = 1 / guard
    s = p["alias_margin"]
    mfin = p["finite_moment_margin"]
    need(s > 0 and mfin > 0, "domain.reserved_margins")
    delta, Gamma = eta - tau, 2 * tau - eta
    Db, Gb, etab = c["delta_b"], c["gamma_b"], c["eta_b"]
    need(delta > 0 and 0 < Gamma < Gb and Db > 0, "domain.transfer_budgets")
    q, A, Ab = Gamma / Gb, delta / Gamma, Db / Gb
    K = delta / q - Db
    need(K > 0 and A < F(1, 4), "domain.transfer_slope")
    need(A - Ab == K / Gb, "identity.slope")

    low = list(map(F, data["filter3"]["low_multipliers"]))
    band = list(map(F, data["filter3"]["band_multipliers"]))
    low_comps = data["filter3"]["low_comparisons"]
    band_comps = data["filter3"]["band_comparisons"]
    need(len(low) == 2 + len(low_comps), "boundary.low_length")
    need(len(band) == 3 + len(band_comps), "boundary.band_length")
    need(all(z >= 0 for z in low + band), "boundary.nonnegative_multipliers")
    need(band[1] == 0, "boundary.zero_lower_multiplier")
    need(low[0] >= 1, "boundary.low_dominates")
    need(band[0] >= 1, "boundary.band_dominates")
    for indices in (low_comps, band_comps):
        need(len(set(indices)) == len(indices) and 3 not in indices
             and all(type(i) is int and 0 <= i < 43 for i in indices),
             "boundary.comparison_indices")
    boundaries = list(map(F, data["old_upper_boundary_factors"]))
    need(boundaries == [F(x) for x in
                       ("1", "1.25", "1.6", "2", "2.6", "3.5", "5", "8", "15")],
         "boundary.source_partition")
    endpoints = [Gamma] + [Gb * b for b in boundaries[1:]]
    need(all(x < y for x, y in zip([F(0)] + endpoints, endpoints)),
         "boundary.strictly_ordered")
    H = boundaries[1]

    def low_form(D, G):
        return affine_sum((low[0], {"1": D, "u": F(-1)}),
                          (low[1], {"1": G, "w": F(-1)}),
                          *((z, {f"comparison_{i}": F(1)})
                            for i, z in zip(low_comps, low[2:])))

    def band_form(slope, upper_multiplier):
        return affine_sum((band[0], {"w": slope, "u": F(-1)}),
                          (band[1], {"w": F(1), "1": -Gb}),
                          (upper_multiplier, {"1": Gb * H, "w": F(-1)}),
                          *((z, {f"comparison_{i}": F(1)})
                            for i, z in zip(band_comps, band[3:])))

    lambda0 = low[0] * (delta - Db) + low[1] * (Gamma - Gb)
    lambda1 = band[0] * H * K
    need(affine_difference(low_form(delta, Gamma), low_form(Db, Gb))
         == {"1": lambda0}, "identity.low_cancellation")
    new_upper = band[2] + correction_scale * band[0] * (A - Ab)
    need(affine_difference(band_form(A, new_upper), band_form(Ab, band[2]))
         == {"1": lambda1}, "identity.band_cancellation")

    r = 1 - mu - ell
    ha, h2a, half = entropy(a), entropy(2 * a), entropy(F(1, 2) - a)
    delta_guard = (eta - mu * log2(3) / 2) / 2
    gaps = {
        "entropy_small": h2a / 2 - gamma,
        "left_list": tau - ell - (ha - gamma) * mu,
        "right_list": tau - r - (1 - gamma) * mu,
        "combined_list": tau - 1 + mu - (ha + half - gamma) * mu + eta,
        "half_block": 2 * tau - F(1, 2) - half * mu,
        "l_cost": tau - ell,
        "r_cost": tau - r,
        "positive_r": r,
        "mask_fits_l": ell - mu * (1 - 2 * a),
        "prime_coverage": eta - mu * log2(3) / 2,
        "mu_cost": tau - mu,
        "sorting_cost": 2 * tau - F(1, 2) - r - zeta,
        "small_prime_cost": 2 * tau - F(1, 2) - zeta - gamma * mu / 2,
        "large_prime_cost": tau - eta / 2,
        "mask_fits_half": F(1, 2) - mu * (1 - 2 * a),
        "entropy_size": 1 - 2 * a - h2a / 2 - ha,
        "entropy_order": half - ha,
        "guard_delta": delta_guard - theta,
        "bad_half_block": delta_guard - (F(1, 2) - tau + zeta),
        "deficiency_limit": F("0.013") - (F(1, 2) - tau + zeta),
    }
    for name, gap in gaps.items():
        need(box(gap).lo > s, "alias." + name)
    need(zeta + theta < s, "alias.reserved_slack")

    moment = {
        "low_other": c["low_moment_margin"] + eta - etab - c["ordinary_low_z0_max"] * K,
        "low_filter3": c["low_moment_margin"] + eta - etab - lambda0,
        "first_bands": c["first_moment_margin"] + eta - etab - c["first_band_z0_max"] * H * K,
        "middle_bands": c["middle_moment_margin"] + eta - etab - c["multiplier_sum_max"] * 15 * K,
        "tail": c["tail_moment_margin"] + eta - etab - c["multiplier_sum_max"] * c["score_bound"] * K / Gb,
    }
    need(c["first_band_z0_max"] >= band[0], "moment.band_coefficient_bound")
    need(c["multiplier_sum_max"] >= max(sum(low), sum(band)), "moment.special_multiplier_bound")
    for name, gap in moment.items():
        need(gap > mfin, "finite_moment." + name)
    Zprime = c["multiplier_sum_max"] * (1 + A - Ab)
    need(Zprime < 419, "moment.rounded_multiplier_bound")
    error_gap = mfin - (18 + 6 * F(419)) * eps
    need(error_gap > 0, "rounding_error")
    beta = tau + 20 * eps
    absorption = p["target_exponent"] - beta
    need(absorption > 0, "advertised_exponent_gap")
    smallest_alias = min(gaps, key=lambda name: box(gaps[name]).lo)
    smallest_moment = min(moment, key=moment.get)
    return {
        "status": "PASS",
        "source_commit": data["source_commit"],
        "scope": "Scalar feasibility and two affine transfer identities only; inherited numerical summaries are assumptions.",
        "logarithm_method": {"terms": TERMS, "fixed_point_decimal_places": 45,
                             "report_decimal_places": 24},
        "alias_gap_count": len(gaps),
        "alias_gap_enclosures": {name: show(value) for name, value in gaps.items()},
        "smallest_alias_gap": smallest_alias,
        "reserved_alias_margin": str(s),
        "unspent_alias_margin": show(s - zeta - theta),
        "conditional_moment_family_count": len(moment),
        "conditional_moment_margins": {name: show(value) for name, value in moment.items()},
        "smallest_moment_family": smallest_moment,
        "moment_slack_above_finite_reservation": show(moment[smallest_moment] - mfin),
        "mean_square_error_exponent_lower_bound": str(error_gap),
        "internal_work_exponent": str(beta),
        "advertised_exponent_gap": str(absorption),
        "transfer": {"delta": str(delta), "Gamma": str(Gamma), "q": str(q),
                     "K": str(K), "lambda0": str(lambda0), "lambda1": str(lambda1),
                     "affine_identities_checked": 2,
                     "zero_lower_multiplier": True,
                     "bounded_region_upper_endpoints": list(map(str, endpoints)),
                     "partition": "[0,e0], (e0,e1], ..., (e7,e8], (e8,infinity)"},
    }


def regression_checks(data):
    """Deliberate failures and independent high-precision arithmetic spot checks."""
    checked = []
    mutations = [
        ("parameters", "target_exponent", "0.48767228002", "advertised_exponent_gap"),
        ("parameters", "finite_moment_margin", "0.000001", "finite_moment.low_other"),
        ("parameters", "alias_margin", "0.00000001", "alias.entropy_small"),
        ("parameters", "epsilon", "0.000000001", "rounding_error"),
        ("parameters", "input_guard_coefficient", "1", "alias.guard_delta"),
        ("parameters", "tau", "0.48767227", "alias.left_list"),
        ("parameters", "a", "0", "domain.a"),
    ]

    def expect_rejected(candidate, label, **kwargs):
        try:
            audit(candidate, **kwargs)
        except Rejected as exc:
            need(str(exc) == label, f"regression.wrong_reason:{label}:{exc}")
        else:
            raise Rejected("regression.accepted:" + label)
        checked.append(label)

    for section, key, value, label in mutations:
        altered = deepcopy(data)
        altered[section][key] = value
        expect_rejected(altered, label)
    for kind, index, value, label in [
        ("band_multipliers", 1, "0.0001", "boundary.zero_lower_multiplier"),
        ("low_multipliers", 0, "0.999", "boundary.low_dominates"),
        ("band_multipliers", 0, "0.9", "boundary.band_dominates"),
    ]:
        altered = deepcopy(data)
        altered["filter3"][kind][index] = value
        expect_rejected(altered, label)
    expect_rejected(data, "identity.band_cancellation", correction_scale=F(0))
    altered = deepcopy(data)
    altered["old_upper_boundary_factors"].pop(3)
    expect_rejected(altered, "boundary.source_partition")

    for k in range(-8, 9):
        need(log2(F(2)**k) == box(k), "regression.exact_power_of_two")
    with localcontext() as context:
        context.prec = 80
        for value in (F(3), F(1, 3), F(data["parameters"]["a"]),
                      2 * F(data["parameters"]["a"]),
                      F(1, 2) - F(data["parameters"]["a"])):
            decimal = Decimal(value.numerator) / Decimal(value.denominator)
            reference = F(decimal.ln() / Decimal(2).ln())
            interval = log2(value)
            need(interval.lo <= reference <= interval.hi, "regression.decimal_log_spot_check")
    try:
        box(1) / Interval(F(-1), F(1))
    except Rejected as exc:
        need(str(exc) == "interval.zero_denominator", "regression.interval_reason")
    else:
        raise Rejected("regression.accepted_zero_denominator")
    return {"rejected_mutations": checked, "rejected_mutation_count": len(checked),
            "exact_power_of_two_cases": 17, "decimal_log_spot_checks": 5,
            "zero_denominator_rejected": True,
            "decimal_spot_check_scope": "Secondary diagnostic only; not the rigorous log enclosure argument."}
