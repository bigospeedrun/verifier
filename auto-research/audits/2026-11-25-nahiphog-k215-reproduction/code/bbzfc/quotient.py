"""Exact state quotient: find states of a machine that are bisimilar (indistinguishable).

Two states are bisimilar if for each read symbol they write the same symbol, move the same
direction and go to bisimilar states. Merging bisimilar states never changes the tape history,
so a nontrivial quotient is a free state saving. The halt label is its own class.
"""
from __future__ import annotations

from typing import Dict, List, Tuple

from .tmio import Machine


def classes(m: Machine) -> List[List[int]]:
    states = sorted(m.states)
    halts = sorted(m.halt_states)
    cls: Dict[int, int] = {q: 0 for q in states}
    for h in halts:
        cls[h] = 1 + halts.index(h)  # distinct classes, never merged with working states
    while True:
        sig: Dict[int, tuple] = {}
        for q in states:
            sig[q] = (
                cls[q],
                tuple((m.rows[(q, b)][0], m.rows[(q, b)][1], cls[m.rows[(q, b)][2]]) for b in (0, 1)),
            )
        ids: Dict[tuple, int] = {}
        new: Dict[int, int] = {}
        for q in states:
            new[q] = ids.setdefault(sig[q], len(ids) + len(halts) + 1)
        for h in halts:
            new[h] = cls[h]
        if len(set(new[q] for q in states)) == len(set(cls[q] for q in states)):
            groups: Dict[int, List[int]] = {}
            for q in states:
                groups.setdefault(new[q], []).append(q)
            return [g for g in groups.values()]
        cls = new


def mergeable(m: Machine) -> List[List[int]]:
    return [g for g in classes(m) if len(g) > 1]
