"""Check the research theorem axiom reports from a successful Lean run."""

from pathlib import Path
import re
import sys

THEOREMS = (
    "strengthened_step", "purity_floor", "interpolation_constants",
    "tail_geometric", "conditional_gap", "invariant_domain",
    "final_tail_comparison", "final_tail_comparison_real",
    "final_exp_upper", "final_exponential_comparison",
)
ALLOWED = {"propext", "Quot.sound", "Classical.choice"}


def main():
    output = Path(sys.argv[1]).read_text()
    if "sorryAx" in output:
        raise SystemExit("FAIL: sorryAx appears in the compiler output")
    for name in THEOREMS:
        full = "HaldaneTail." + name
        pattern = (re.escape("'" + full + "'") +
                   r" (?:depends on axioms: \[([\s\S]*?)\]|does not depend on any axioms)")
        match = re.search(pattern, output)
        if match is None:
            raise SystemExit("FAIL: missing axiom report for " + full)
        axioms = {value.strip() for value in (match.group(1) or "").split(",")
                  if value.strip()}
        if not axioms <= ALLOWED:
            raise SystemExit("FAIL: unapproved axioms for " + full + ": " + repr(axioms))
        print("PASS:", full, "axioms", ", ".join(sorted(axioms)) or "none")


if __name__ == "__main__":
    main()
