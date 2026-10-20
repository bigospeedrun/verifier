#!/usr/bin/env bash
# Builds the Lean file against the pinned Mathlib and checks that every theorem
# uses only propext, Classical.choice and Quot.sound (no sorryAx).
set -euo pipefail
cd "$(dirname "$0")/lean"
lake exe cache get
lake build
out="$(lake env lean Axioms.lean 2>&1)" || { printf '%s\n' "$out"; echo "FAIL: Axioms.lean did not compile"; exit 1; }
printf '%s\n' "$out"
count="$(printf '%s\n' "$out" | grep -c "depends on axioms\|does not depend on any axioms" || true)"
expected="$(grep -c '^#print axioms' Axioms.lean)"
if [ "$count" != "$expected" ]; then
  echo "FAIL: expected $expected axiom reports, got $count"
  exit 1
fi
bad="$(printf '%s\n' "$out" | grep -o 'axioms: \[[^]]*\]' | sed 's/axioms: \[//; s/\]//' | tr ',' '\n' | tr -d ' ' | grep -v -x -e propext -e Classical.choice -e Quot.sound || true)"
if [ -n "$bad" ]; then
  echo "FAIL: disallowed axioms: $bad"
  exit 1
fi
echo "OK: $expected theorems checked; axioms within {propext, Classical.choice, Quot.sound}"
