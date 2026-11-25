"""Decode the tape of a K215-style machine at a dispatch frame into runs.

Layout seen at the K215 startup end (documented in the K215 README and in
independent_runtime.py): a lone marker 1, a gap of zeros, a bit string for the program
counter, then blocks of consecutive ones separated by single zeros. A block of k ones
is a register of value k-1. The nine register blocks come first, then the spare blocks.
This module only reports runs; interpretation lives in the callers.
"""
from __future__ import annotations

from typing import List, Tuple

from .sim import Config

Run = Tuple[int, int, int]  # (symbol, length, start position)


def runs(c: Config) -> List[Run]:
    lo, hi = c.bounds()
    if hi < lo:
        return []
    out: List[Run] = []
    p = lo
    while p <= hi:
        sym = c.read(p)
        q = p
        while q <= hi and c.read(q) == sym:
            q += 1
        out.append((sym, q - p, p))
        p = q
    return out


def one_blocks_after_gap(c: Config, gap_min: int = 32) -> Tuple[int, List[int]]:
    """Return (position of the first 1 after the first run of >= gap_min zeros,
    lengths of the one-runs from there on)."""
    rs = runs(c)
    for i, (sym, n, p) in enumerate(rs):
        if sym == 0 and n >= gap_min:
            tail = [(s, m, q) for s, m, q in rs[i + 1 :]]
            first = tail[0][2]
            return first, [m for s, m, q in tail if s == 1]
    raise ValueError("no long zero gap found")
