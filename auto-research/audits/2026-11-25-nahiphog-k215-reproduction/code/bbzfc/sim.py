"""Reference simulator for binary Turing machines on a two-way infinite blank tape.

Exact and simple, not fast. The tape is a bytearray window that doubles on demand.
Cell index `origin + position` holds the symbol at `position`; position 0 is where
the head starts. The native lockstep core (later) must agree with this module.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Dict, List, Optional, Tuple

from .tmio import Machine


@dataclass
class Config:
    state: int
    head: int
    step: int
    tape: bytearray
    origin: int  # tape index of position 0

    def ones(self) -> List[int]:
        o = self.origin
        return [i - o for i, v in enumerate(self.tape) if v]

    def ones_count(self) -> int:
        return sum(self.tape)

    def bounds(self) -> Tuple[int, int]:
        """(min, max) positions holding a 1, or (0, -1) if the tape is blank."""
        o = self.origin
        idx = [i for i, v in enumerate(self.tape) if v]
        if not idx:
            return (0, -1)
        return (idx[0] - o, idx[-1] - o)

    def read(self, pos: int) -> int:
        i = pos + self.origin
        return self.tape[i] if 0 <= i < len(self.tape) else 0

    def render(self, lo: Optional[int] = None, hi: Optional[int] = None) -> str:
        a, b = self.bounds()
        lo = a if lo is None else lo
        hi = b if hi is None else hi
        return "".join(str(self.read(p)) for p in range(lo, hi + 1))


def initial(size: int = 1024) -> Config:
    return Config(state=0, head=0, step=0, tape=bytearray(size), origin=size // 2)


def _grow(c: Config) -> None:
    n = len(c.tape)
    c.tape = bytearray(n // 2) + c.tape + bytearray(n // 2)
    # Left padding grew by n // 2 cells.
    c.origin += n // 2


def run(
    m: Machine,
    max_steps: int,
    stop_state: Optional[int] = None,
    cfg: Optional[Config] = None,
    on_step: Optional[Callable[[int, int, int, int, int, int, int], None]] = None,
) -> Tuple[Config, str]:
    """Run until a stop condition. Returns (config, reason).

    reason is one of: 'halt' (entered a state with no rows), 'stop_state' (entered
    stop_state; the config is after that transition), 'max_steps'.
    on_step, if given, is called before each transition as
    on_step(step, state, head, read, write, move, next_state).
    """
    c = cfg if cfg is not None else initial()
    rows: Dict[Tuple[int, int], Tuple[int, int, int]] = m.rows
    if cfg is None:
        c.state = m.start
    tape, origin = c.tape, c.origin
    state, head, step = c.state, c.head, c.step
    n = len(tape)
    reason = "max_steps"
    while step < max_steps:
        i = head + origin
        if i <= 0 or i >= n - 1:
            c.tape, c.origin = tape, origin
            _grow(c)
            tape, origin = c.tape, c.origin
            n = len(tape)
            i = head + origin
        r = tape[i]
        row = rows.get((state, r))
        if row is None:
            reason = "halt"
            break
        w, mv, z = row
        if on_step is not None:
            on_step(step, state, head, r, w, mv, z)
        tape[i] = w
        head += mv
        state = z
        step += 1
        if stop_state is not None and state == stop_state:
            reason = "stop_state"
            break
        if (state, 0) not in rows and (state, 1) not in rows:
            reason = "halt"
            break
    c.tape, c.origin = tape, origin
    c.state, c.head, c.step = state, head, step
    return c, reason
