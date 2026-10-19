#!/usr/bin/env bash
# Reproduce the Heilbronn statement checks from a fresh clone of
# bigospeedrun/verifier. Run from the repository root:
#   bash auto-research/lean-statements/2026-10-19-joshuacortez-heilbronn-triangle/verify.sh
# Needs: git, python3, elan (Lean 4.34.1 is installed from lean-toolchain),
# network access to GitHub and the Mathlib cache. Uses about 6 GB of disk.
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel)"
PKG="$ROOT/auto-research/lean-statements/2026-10-19-joshuacortez-heilbronn-triangle"
CH="$ROOT/challenges/heilbronn-triangle"
UPSTREAM_COMMIT=1581d4cbdd69a0faf34b2089614fe2a814316a6a
UPSTREAM_PATH=lean/OAI/Geometry/HeilbronnTriangle/Definitions.lean
FROZEN="$CH/OAI/Geometry/HeilbronnTriangle/Definitions.lean"

echo "== 1. Package and statement hashes"
python3 - "$PKG" "$CH" <<'PY'
import hashlib, json, os, sys
pkg, ch = sys.argv[1], sys.argv[2]
m = json.load(open(os.path.join(pkg, "MANIFEST.json")))
for rel, want in sorted(m["sha256"].items()):
    path = os.path.join(pkg, rel) if not rel.startswith("challenges/") else os.path.join(ch, rel[len("challenges/heilbronn-triangle/"):])
    got = hashlib.sha256(open(path, "rb").read()).hexdigest()
    assert got == want, f"hash mismatch: {rel}"
p = json.load(open(os.path.join(ch, "provenance.json")))["files"][0]
got = hashlib.sha256(open(os.path.join(ch, p["path"]), "rb").read()).hexdigest()
assert got == p["sha256"], "frozen file differs from provenance.json"
print("manifest and provenance hashes: OK")
PY

echo "== 2. Frozen file is byte-identical to openai/math"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
git -C "$WORK" init -q up
git -C "$WORK/up" fetch -q --depth 1 --filter=blob:none https://github.com/openai/math "$UPSTREAM_COMMIT"
git -C "$WORK/up" show "$UPSTREAM_COMMIT:$UPSTREAM_PATH" > "$WORK/upstream.lean"
cmp "$WORK/upstream.lean" "$FROZEN"
echo "byte-identical to openai/math@$UPSTREAM_COMMIT: OK"

echo "== 3. Build statement and vacuity checks with the pinned profile"
P="$WORK/proj"
mkdir -p "$P"
cp -R "$CH/OAI" "$CH/Statement.lean" "$P/"
cp "$PKG/VacuityCheck.lean" "$PKG/Axioms.lean" "$P/"
echo "leanprover/lean4:v4.34.1" > "$P/lean-toolchain"
python3 - "$ROOT/profiles/lake-manifest.json" "$P/lake-manifest.json" <<'PY'
import json, sys
d = json.load(open(sys.argv[1])); d["name"] = "hbcheck"
json.dump(d, open(sys.argv[2], "w"), indent=1)
PY
cat > "$P/lakefile.toml" <<'TOML'
name = "hbcheck"
defaultTargets = ["Statement", "VacuityCheck"]

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "d13f23b723b8a846827a245b89c10fc7d3f11612"

[[lean_lib]]
name = "OAI"
globs = ["OAI.+"]

[[lean_lib]]
name = "Statement"

[[lean_lib]]
name = "VacuityCheck"
TOML
cd "$P"
lake exe cache get
lake build Statement VacuityCheck
lake env lean Axioms.lean
