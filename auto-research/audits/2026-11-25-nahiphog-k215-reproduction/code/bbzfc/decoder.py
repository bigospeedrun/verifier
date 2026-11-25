"""Decoder analysis: how the program counter tree maps onto machine states.

The source program is a full binary tree over pc paths; its leaves are instructions
(op, arg). Identical subtrees can share machine states. This module
  * hash-conses the tree and counts distinct subtrees (leaf kinds and internal nodes),
  * records, for each site run, which machine state is reading pc bit i of the path, and
  * checks whether that state depends only on the identity of the subtree at that prefix
    (the DAG hypothesis), and how many distinct states are used for decoding.
"""
from __future__ import annotations

from collections import defaultdict
from typing import Dict, List, Optional, Sequence, Set, Tuple

from . import siterun
from .tmio import Machine

Site = siterun.Site


def build_tree(sites: Sequence[Site]):
    """Hash-cons the full binary tree. Returns (root_id, nodes) where nodes[id] is either
    ('leaf', op, arg) or ('node', child0_id, child1_id), and ids index distinct subtrees."""
    ids: Dict[tuple, int] = {}
    nodes: List[tuple] = []

    def intern(key: tuple) -> int:
        if key not in ids:
            ids[key] = len(nodes)
            nodes.append(key)
        return ids[key]

    # Build from sorted paths recursively.
    by_path = {pc: (op, arg) for pc, op, arg in sites}

    def build(prefix: str) -> int:
        if prefix in by_path:
            op, arg = by_path[prefix]
            return intern(("leaf", op, arg))
        return intern(("node", build(prefix + "0"), build(prefix + "1")))

    root = build("")
    return root, nodes


def subtree_ids(sites: Sequence[Site]) -> Dict[str, int]:
    """Map every proper prefix (internal node path) and leaf path to its distinct-subtree id."""
    by_path = {pc: (op, arg) for pc, op, arg in sites}
    ids: Dict[tuple, int] = {}
    out: Dict[str, int] = {}

    def intern(key):
        return ids.setdefault(key, len(ids))

    def build(prefix: str) -> int:
        if prefix in by_path:
            i = intern(("leaf",) + by_path[prefix])
        else:
            i = intern(("node", build(prefix + "0"), build(prefix + "1")))
        out[prefix] = i
        return i

    build("")
    return out


def decode_trace(m: Machine, dispatcher: int, site: Site, logical, spares, gap, limit: int = 20000):
    """Run a site case and return state_at[i] for i = 0..len(pc): the machine state the first
    time the head stands on pc cell i after the run starts (None if never reached in limit)."""
    pc = site[0]
    ones = siterun.frame(pc, logical, spares, gap)
    tape, origin = siterun._tape_from_ones(ones)
    n = len(tape)
    state, head = dispatcher, 0
    first_state: Dict[int, int] = {0: dispatcher}
    rows = m.rows
    for step in range(limit):
        i = head + origin
        if i < 70 or i > n - 70:
            tape = bytearray(n) + tape + bytearray(n)
            origin += n
            n = len(tape)
            i = head + origin
        row = rows.get((state, tape[i]))
        if row is None:
            break
        w, mv, z = row
        tape[i] = w
        head += mv
        state = z
        if 0 <= head <= len(pc) and head not in first_state:
            first_state[head] = state
        if len(first_state) == len(pc) + 1:
            break
    return first_state


def analyse(m: Machine, dispatcher: int, sites: Sequence[Site], samples: int = 1):
    sub = subtree_ids(sites)
    root, nodes = build_tree(sites)
    leaf_kinds = sum(1 for n in nodes if n[0] == "leaf")
    internal = sum(1 for n in nodes if n[0] == "node")
    prefix_states: Dict[str, Set[int]] = defaultdict(set)
    per_subtree: Dict[int, Set[int]] = defaultdict(set)
    reached_leaf_state: Dict[str, Set[int]] = defaultdict(set)
    import random

    rng = random.Random(5)
    for site in sites:
        for _ in range(samples):
            logical, spares, gap = siterun.sample_inputs(rng, site, True if site[1] == "CD" else None)
            fs = decode_trace(m, dispatcher, site, logical, spares, gap)
            pc = site[0]
            for i, q in fs.items():
                prefix = pc[:i]
                prefix_states[prefix].add(q)
                per_subtree[sub[prefix]].add(q)
    inconsistent = sum(1 for v in per_subtree.values() if len(v) > 1)
    all_decode_states = set()
    for v in prefix_states.values():
        all_decode_states |= v
    return {
        "distinct_subtrees": len(nodes),
        "leaf_kinds": leaf_kinds,
        "internal_nodes": internal,
        "sites": len(sites),
        "decode_states": sorted(all_decode_states),
        "decode_state_count": len(all_decode_states),
        "subtrees_with_several_states": inconsistent,
        "prefix_states": {k: sorted(v) for k, v in prefix_states.items() if len(v) > 1},
        "per_subtree": {str(k): sorted(v) for k, v in per_subtree.items()},
    }
