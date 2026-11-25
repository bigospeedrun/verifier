"""Read and write binary Turing machine tables in the ProveIt row format.

Format (as used by candidate-k215/*.tm): an optional first line `#! start <state>`,
then one row per line: `state read write direction next`, with read and write in
{0, 1} and direction in {L, R}. A state that no row defines (the halt state) has no
outgoing rows. Rows are written sorted by (state, read) so the output bytes are
canonical and can be compared by SHA-256 against published hashes.
"""
from __future__ import annotations

import hashlib
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Tuple

Row = Tuple[int, int, int]  # (write, move, next) with move = +1 for R, -1 for L


@dataclass(frozen=True)
class Machine:
    start: int
    rows: Dict[Tuple[int, int], Row]

    @property
    def states(self) -> frozenset:
        return frozenset(q for q, _ in self.rows)

    @property
    def targets(self) -> frozenset:
        return frozenset(r[2] for r in self.rows.values())

    @property
    def halt_states(self) -> frozenset:
        """States that are entered but have no rows: transitions into them halt."""
        return self.targets - self.states


def parse(text: str) -> Machine:
    start = 0
    rows: Dict[Tuple[int, int], Row] = {}
    for lineno, line in enumerate(text.splitlines(), 1):
        if not line.strip():
            continue
        if line.startswith("#!"):
            parts = line[2:].split()
            if len(parts) == 2 and parts[0] == "start":
                start = int(parts[1])
            continue
        if line.startswith("#"):
            continue
        fields = line.split()
        if len(fields) != 5:
            raise ValueError(f"line {lineno}: expected 5 fields, got {len(fields)}")
        q, b, w, d, z = fields
        q, b, w, z = int(q), int(b), int(w), int(z)
        if b not in (0, 1) or w not in (0, 1) or d not in ("L", "R"):
            raise ValueError(f"line {lineno}: bad symbol or direction")
        if (q, b) in rows:
            raise ValueError(f"line {lineno}: duplicate row for state {q} read {b}")
        rows[(q, b)] = (w, 1 if d == "R" else -1, z)
    return Machine(start, rows)


def load(path) -> Machine:
    return parse(Path(path).read_text(encoding="utf-8"))


def dumps(m: Machine) -> bytes:
    out = [f"#! start {m.start}\n"]
    for (q, b), (w, mv, z) in sorted(m.rows.items()):
        out.append(f"{q} {b} {w} {'R' if mv == 1 else 'L'} {z}\n")
    return "".join(out).encode()


def sha256_hex(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def check_dense(m: Machine, expect_states: int) -> None:
    """Raise unless the machine has exactly expect_states working states, both rows each,
    labelled 0..expect_states-1, and exactly one halt label expect_states."""
    qs = sorted(m.states)
    if qs != list(range(expect_states)):
        raise ValueError("working states are not 0..n-1")
    for q in qs:
        if (q, 0) not in m.rows or (q, 1) not in m.rows:
            raise ValueError(f"state {q} is missing a row")
    if m.halt_states != frozenset({expect_states}):
        raise ValueError(f"halt states are {sorted(m.halt_states)}, expected [{expect_states}]")
