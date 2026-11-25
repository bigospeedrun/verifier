"""Concrete per-site test of a K215-style machine, written from the semantics described in
the K215 verification code (independent_runtime.py, symbolic_runtime.py) and re-derived here.

A frame is a tape in dispatcher state with the head at position 0:
  * a marker 1 at -1 and nothing to its left,
  * the program counter (pc), a bit path, written as ones at positions i where pc[i] == '1'
    (positions 0..len(pc)-1, zeros after),
  * a second marker 1 at 64 + gap,
  * then blocks, each a single 0 followed by (value + 1) ones: nine register blocks in physical
    order (logical register i lives at physical index PHY[i]), then the spare blocks.
A site is (pc path, op, arg) with op in CI, CD, CB, CC, CH. Running the machine from the frame
must return to a clean dispatcher frame whose content is determined by the op:
  CI r: register r += 1, a spare of value 1 is appended, pc -> increment(pc)
  CD r: if register r > 0: register r -= 1, gap += 1, pc -> increment(pc)
        else: pc -> increment(strip(pc, '0', 1))
  CB k: pc -> increment(strip(pc, '0', k))
  CC k: pc -> strip(pc, '1', k)
  CH:   the machine halts
increment(pc) adds one modulo 2^len; on overflow the frame shifts one cell left (head -1, gap+1).
strip(pc, b, k) cuts pc just before its k-th occurrence of b from the right ('' if there are fewer).

This module is a checker for candidate tables. K215 itself must pass every case; if it does not,
the harness is wrong, not the machine.
"""
from __future__ import annotations

import json
import random
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Set, Tuple

from .tmio import Machine

PHY = (6, 2, 0, 4, 3, 7, 8, 5, 1)
Site = Tuple[str, str, Optional[int]]


def load_sites(path) -> List[Site]:
    text = Path(path).read_text(encoding="utf-8")
    return [(pc, op, arg) for pc, op, arg in json.loads(text)]


def inc(pc: str) -> Tuple[str, int]:
    n = len(pc)
    v = (int(pc, 2) if pc else 0) + 1
    return (format(v % (1 << n), "0%db" % n) if n else ""), int(v == (1 << n))


def strip(pc: str, bit: str, count: int) -> str:
    if count == 0:
        return pc
    seen = 0
    for i in range(len(pc) - 1, -1, -1):
        if pc[i] == bit:
            seen += 1
            if seen == count:
                return pc[:i]
    return ""


def frame(pc: str, logical: Sequence[int], spares: Sequence[int], gap: int) -> Set[int]:
    values = [0] * 9
    for i, j in enumerate(PHY):
        values[j] = logical[i]
    ones = {-1, 64 + gap} | {i for i, b in enumerate(pc) if b == "1"}
    pos = 64 + gap + 1
    for v in list(values) + list(spares):
        pos += 1
        ones.update(range(pos, pos + v + 1))
        pos += v + 1
    return ones


def expected(site: Site, logical: List[int], spares: List[int], gap: int):
    """Return None for halt, else (head, ones relative to head) after the site."""
    pc, op, arg = site
    regs = list(logical)
    sp = list(spares)
    delta = 0
    if op == "CH":
        return None
    if op == "CI":
        regs[arg] += 1
        sp.append(1)
        nxt, shift = inc(pc)
    elif op == "CD" and regs[arg] > 0:
        regs[arg] -= 1
        delta = 1
        nxt, shift = inc(pc)
    elif op in ("CD", "CB"):
        nxt, shift = inc(strip(pc, "0", arg if op == "CB" else 1))
    elif op == "CC":
        nxt, shift = strip(pc, "1", arg), 0
    else:
        raise ValueError(site)
    return -shift, frame(nxt, regs, sp, gap + delta + shift)


@dataclass
class CaseResult:
    ok: bool
    steps: int
    rows: Set[Tuple[int, int]]
    reason: str = ""


def _tape_from_ones(ones: Set[int]):
    lo, hi = min(ones), max(ones)
    pad = 4096
    tape = bytearray(hi - lo + 1 + 2 * pad)
    origin = pad - lo
    for x in ones:
        tape[x + origin] = 1
    return tape, origin


def run_case(
    m: Machine,
    dispatcher: int,
    site: Site,
    logical: List[int],
    spares: List[int],
    gap: int,
    limit: int = 400_000,
) -> CaseResult:
    ones = frame(site[0], logical, spares, gap)
    tape, origin = _tape_from_ones(ones)
    n = len(tape)
    state, head, step = dispatcher, 0, 0
    rows = m.rows
    used: Set[Tuple[int, int]] = set()
    exp = expected(site, logical, spares, gap)
    while step <= limit:
        i = head + origin
        if i < 70 or i > n - 70:
            pad = n
            tape = bytearray(pad) + tape + bytearray(pad)
            origin += pad
            n = len(tape)
            i = head + origin
        if step and state == dispatcher and exp is not None:
            first = tape.find(1)
            if first == i - 1:
                # no ones in [head+52, head+64) and some one at >= head+64
                if not any(tape[i + 52 : i + 64]) and tape.find(1, i + 64) != -1:
                    rel = {k - origin - head for k, v in enumerate(tape) if v}
                    ok = exp[0] == head and rel == exp[1]
                    return CaseResult(ok, step, used, "" if ok else "frame mismatch at first clean redispatch")
        r = tape[i]
        row = rows.get((state, r))
        if row is None:
            ok = exp is None
            return CaseResult(ok, step, used, "" if ok else f"undefined row ({state},{r})")
        used.add((state, r))
        w, mv, z = row
        tape[i] = w
        head += mv
        state = z
        step += 1
        if exp is None and (state, 0) not in rows and (state, 1) not in rows:
            return CaseResult(True, step, used, "halted")
    return CaseResult(False, step, used, "step limit")


def sample_inputs(rng: random.Random, site: Site, positive: Optional[bool]):
    """One random concrete frame for the site. positive forces the CD register >0 (True) or ==0."""
    logical = [rng.choice([0, 0, 1, 2, 3, 5]) for _ in range(9)]
    if site[1] == "CD":
        logical[site[2]] = rng.choice([1, 2, 4]) if positive else 0
    spares = [rng.choice([0, 1, 1, 2]) for _ in range(rng.choice([1, 2, 5, 9]))]
    gap = rng.choice([0, 0, 1, 2, 7])
    return logical, spares, gap


@dataclass
class SweepReport:
    cases: int = 0
    failures: List[dict] = field(default_factory=list)
    rows_used: Dict[Tuple[int, int], int] = field(default_factory=dict)
    min_steps: int = 10**9
    max_steps: int = 0
    per_site_rows: Dict[int, Set[Tuple[int, int]]] = field(default_factory=dict)


def sweep(
    m: Machine,
    dispatcher: int,
    sites: Sequence[Site],
    samples: int = 2,
    seed: int = 1,
    site_indices: Optional[Iterable[int]] = None,
    stop_on_fail: bool = False,
) -> SweepReport:
    rng = random.Random(seed)
    rep = SweepReport()
    idxs = list(site_indices) if site_indices is not None else range(len(sites))
    for i in idxs:
        site = sites[i]
        flags = (False, True) if site[1] == "CD" else (None,)
        for pos in flags:
            for _ in range(samples):
                logical, spares, gap = sample_inputs(rng, site, pos)
                res = run_case(m, dispatcher, site, logical, spares, gap)
                rep.cases += 1
                rep.min_steps = min(rep.min_steps, res.steps)
                rep.max_steps = max(rep.max_steps, res.steps)
                rep.per_site_rows.setdefault(i, set()).update(res.rows)
                for row in res.rows:
                    rep.rows_used[row] = rep.rows_used.get(row, 0) + 1
                if not res.ok:
                    rep.failures.append(
                        {"site_index": i, "site": list(site), "positive": pos, "logical": logical,
                         "spares": spares, "gap": gap, "steps": res.steps, "reason": res.reason}
                    )
                    if stop_on_fail:
                        return rep
    return rep
