"""Incremental decoder allocator: turn a new source (same control-flow graph as the parent's) into
a candidate table by reusing the parent machine's states.

Working in native labels (dispatcher 84, halt 254, start 0) as the upstream checker does.

Model, following the ProveIt decoder (build221.decoder_map, allocate-v2.py):
  * The decoder starts in the dispatcher with the head on pc cell 0. A state q "represents" an
    internal node n at prefix p. For child bit b:
      - internal child: the edge is a short walk over the known prefix bits (usually one pure row
        (q,b) -> (b, R, q_child)); it must restore the tape and end at cell len(p)+1;
      - leaf child: the single row (q,b) is the leaf action for that instruction kind and slot.
  * Rows used by decoder edges/leaf slots are decode rows; every row executed afterwards (the
    instruction body, returns, scans) or during the blank-start prefix before the first dispatch
    is an engine row.

Allocation:
  * a node of the new tree that also occurs in the parent tree keeps the parent's states;
  * the free pool holds parent states that represent only vanished nodes and none of whose rows
    is an engine row or a helper row of a retained edge;
  * every new node takes a pool state (the root takes the dispatcher) and gets pure child rows and
    the parent's most common leaf action for each leaf slot.
Nothing here is trusted: the result goes through siterun (fast) and the upstream checker (proof).
"""
from __future__ import annotations

import random
from collections import Counter, defaultdict
from typing import Dict, List, Optional, Sequence, Set, Tuple

from . import siterun
from .tmio import Machine

DISPATCH = 84
HALT = 254
Site = siterun.Site
Node = tuple  # leaf: ('CI', 3) etc.; internal: (left, right)


def is_leaf(n: Node) -> bool:
    return isinstance(n[0], str)


class Interner:
    def __init__(self):
        self.pool: Dict[Node, Node] = {}

    def __call__(self, n: Node) -> Node:
        return self.pool.setdefault(n, n)


def build_tree(sites: Sequence[Site], intern: Interner) -> Node:
    by = {p: (op, arg) for p, op, arg in sites}

    def rec(prefix: str) -> Node:
        if prefix in by:
            return intern(by[prefix])
        return intern((rec(prefix + "0"), rec(prefix + "1")))

    return rec("")


def occurrences(tree: Node):
    """Yield (node, prefix) for every internal occurrence, root first."""
    stack = [(tree, "")]
    while stack:
        n, p = stack.pop()
        if is_leaf(n):
            continue
        yield n, p
        stack.append((n[1], p + "1"))
        stack.append((n[0], p + "0"))


def walk_edge(rows: Dict, q: int, prefix: str, bit: int, limit: int = 100):
    """Edge from q at cell len(prefix) for child bit. Returns (child_state or None, rows used)."""
    tape = {-1: 1, **{i: int(v) for i, v in enumerate(prefix + str(bit))}}
    before = dict(tape)
    h = len(prefix)
    used = []
    for _ in range(limit):
        if h == len(prefix) + 1:
            return (q if tape == before else None), used
        if h not in tape or (q, tape[h]) not in rows:
            return None, used
        k = (q, tape[h])
        used.append(k)
        w, d, q = rows[k]
        tape[h] = w
        h += d
    return None, used


class DecoderMap:
    """Decoder relation of a (table, tree): node -> states, state -> nodes, decode rows."""

    def __init__(self, rows: Dict, tree: Node):
        self.node_states: Dict[Node, Set[int]] = defaultdict(set)
        self.state_nodes: Dict[int, Set[Node]] = defaultdict(set)
        self.decode_rows: Set[Tuple[int, int]] = set()
        self.helper_rows: Set[Tuple[int, int]] = set()
        self.leaf_actions: Dict[Tuple[tuple, int], Counter] = defaultdict(Counter)
        self.errors: List[str] = []
        self.prefix_state: Dict[str, int] = {}
        stack = [(tree, "", DISPATCH)]
        while stack:
            n, p, q = stack.pop()
            self.prefix_state[p] = q
            self.node_states[n].add(q)
            self.state_nodes[q].add(n)
            for b in (0, 1):
                ch = n[b]
                if is_leaf(ch):
                    self.decode_rows.add((q, b))
                    self.leaf_actions[(ch, b)][rows[(q, b)]] += 1
                    continue
                z, used = walk_edge(rows, q, p, b)
                if z is None:
                    self.errors.append(f"edge fails at prefix {p!r} bit {b} from state {q}")
                    continue
                self.decode_rows.update(used)
                self.helper_rows.update(used[1:])
                stack.append((ch, p + str(b), z))

    def decode_steps(self, rows: Dict, pc: str) -> int:
        """Number of steps of the actual run spent decoding pc (up to and including the leaf row)."""
        q, steps = DISPATCH, 0
        for i in range(len(pc) - 1):
            z, used = walk_edge(rows, q, pc[:i], int(pc[i]))
            steps += len(used)
            q = z
        return steps + 1


def engine_rows(m: Machine, dm: DecoderMap, sites: Sequence[Site], samples: int = 2, seed: int = 3,
                startup_first_dispatch: Optional[int] = None) -> Set[Tuple[int, int]]:
    """Rows the engine depends on: rows executed after the decode phase of a site case in any
    context other than re-decoding (state equal to the decoder state of the current pc prefix at
    the head), plus rows of the blank-start prefix before the first arrival at the dispatcher.
    Rows used only for decoding or re-decoding belong to the decoder and may be rewritten."""
    rng = random.Random(seed)
    rows = m.rows
    eng: Set[Tuple[int, int]] = set()
    for site in sites:
        pc = site[0]
        k = dm.decode_steps(rows, pc)
        flags = (False, True) if site[1] == "CD" else (None,)
        for pos in flags:
            for _ in range(samples):
                logical, spares, gap = siterun.sample_inputs(rng, site, pos)
                for key, redecode in _trace_rows(m, site, logical, spares, gap, dm, k):
                    if not redecode:
                        eng.add(key)
    # blank-start prefix
    from .sim import initial
    c = initial()
    c.state = m.start
    state, head = c.state, 0
    tape = c.tape
    origin = c.origin
    for _ in range(10_000):
        if state == DISPATCH:
            break
        r = tape[head + origin]
        eng.add((state, r))
        w, mv, z = rows[(state, r)]
        tape[head + origin] = w
        head += mv
        state = z
    return eng


def _trace_rows(m: Machine, site: Site, logical, spares, gap, dm: "DecoderMap", start_step: int,
                limit: int = 400_000):
    """Yield (row, is_redecode) for every step from start_step until the first clean redispatch."""
    ones = siterun.frame(site[0], logical, spares, gap)
    tape, origin = siterun._tape_from_ones(ones)
    n = len(tape)
    state, head = DISPATCH, 0
    rows = m.rows
    out = []
    exp = siterun.expected(site, logical, spares, gap)
    for step in range(limit):
        i = head + origin
        if i < 70 or i > n - 70:
            tape = bytearray(n) + tape + bytearray(n)
            origin += n
            n = len(tape)
            i = head + origin
        if step and state == DISPATCH and exp is not None and tape.find(1) == i - 1:
            if not any(tape[i + 52 : i + 64]) and tape.find(1, i + 64) != -1:
                break
        k = (state, tape[i])
        row = rows.get(k)
        if row is None:
            break
        if step >= start_step:
            redecode = False
            if k in dm.decode_rows:
                left = tape.find(1)
                pcs = left + 1 - origin
                rel = head - pcs
                if 0 <= rel < 64:
                    pre = "".join("1" if tape[origin + pcs + j] else "0" for j in range(rel))
                    redecode = dm.prefix_state.get(pre) == state
            out.append((k, redecode))
        w, mv, z = row
        tape[i] = w
        head += mv
        state = z
    return out


def allocate(m: Machine, old_sites: Sequence[Site], new_sites: Sequence[Site], engine: Set[Tuple[int, int]],
             dm_old: Optional[DecoderMap] = None):
    """Return (rows, report). rows is None when allocation is impossible."""
    intern = Interner()
    t_old = build_tree(old_sites, intern)
    t_new = build_tree(new_sites, intern)
    dm = dm_old or DecoderMap(m.rows, t_old)
    old_nodes = set(dm.node_states)
    new_nodes_all = {n for n, _ in occurrences(t_new)}
    retained = new_nodes_all & old_nodes
    fresh = [n for n in new_nodes_all if n not in old_nodes]
    vanished = old_nodes - new_nodes_all
    # helper rows of retained edges must stay
    keep_rows = set(engine) | dm.helper_rows
    used_states = set().union(*(dm.node_states[n] for n in retained)) if retained else set()
    all_states = {q for q, _ in m.rows}
    # decoder states that the engine jumps into keep their meaning: never freed
    pinned = {m.rows[k][2] for k in engine if k in m.rows} & set(dm.state_nodes)
    report_pinned_vanished = sorted(q for q in pinned if dm.state_nodes[q] and dm.state_nodes[q] <= vanished)
    pool = []
    for q in sorted(all_states):
        if q in used_states or q == DISPATCH or q in pinned:
            continue
        nodes = dm.state_nodes.get(q, set())
        if not nodes:
            continue  # not a decoder state
        if not nodes <= vanished:
            continue
        if (q, 0) in keep_rows or (q, 1) in keep_rows:
            continue
        pool.append(q)
    report = {"retained": len(retained), "fresh": len(fresh), "vanished": len(vanished), "pool": len(pool),
              "pinned_states": len(pinned), "pinned_with_vanished_node": report_pinned_vanished,
              "decoder_errors_old": len(dm.errors)}
    root_fresh = t_new not in old_nodes
    need = len(fresh) - (1 if root_fresh else 0)
    if root_fresh and ((DISPATCH, 0) in engine or (DISPATCH, 1) in engine):
        report["status"] = "DISPATCHER_ROWS_PROTECTED"
        return None, report
    if need > len(pool):
        report["status"] = "POOL_TOO_SMALL"
        return None, report
    # leaf action defaults: most common direct (moves right, writes the read bit) else most common
    defaults = {}
    for key, acts in dm.leaf_actions.items():
        (ch, b) = key
        direct = [a for a in acts if a[:2] == (b, 1)]
        defaults[key] = max(direct or acts, key=lambda a: acts[a])
    state_of: Dict[Node, int] = {n: min(dm.node_states[n]) for n in retained}
    it = iter(pool)
    for n in fresh:
        state_of[n] = DISPATCH if n is t_new else next(it)
    rows = dict(m.rows)
    for n in fresh:
        q = state_of[n]
        for b in (0, 1):
            ch = n[b]
            if is_leaf(ch):
                if (ch, b) not in defaults:
                    report["status"] = f"MISSING_LEAF_ACTION {ch} slot {b}"
                    return None, report
                rows[(q, b)] = defaults[(ch, b)]
            else:
                rows[(q, b)] = (b, 1, state_of[ch])
    # prune unreachable states from start 0
    reach = {0}
    todo = [0]
    while todo:
        q = todo.pop()
        for b in (0, 1):
            z = rows[(q, b)][2]
            if z != HALT and z not in reach:
                reach.add(z)
                todo.append(z)
    rows = {k: v for k, v in rows.items() if k[0] in reach}
    report["states"] = len(reach)
    report["removed"] = sorted(all_states - reach)
    report["status"] = "ALLOCATED"
    return rows, report
