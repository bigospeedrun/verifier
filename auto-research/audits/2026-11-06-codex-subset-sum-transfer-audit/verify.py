"""Run from any directory with Python 3.10+; no network or dependencies.

SPDX-License-Identifier: Apache-2.0
"""

import hashlib
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / "code"))


def main():
    manifest = json.loads((ROOT / "MANIFEST.json").read_text(encoding="utf-8"))
    if manifest.get("algorithm") != "sha256":
        raise ValueError("Manifest algorithm must be sha256")
    actual = {}
    for path in ROOT.rglob("*"):
        if path.is_symlink():
            raise ValueError(f"Unexpected symlink: {path}")
        if path.is_file() and path != ROOT / "MANIFEST.json":
            actual[path.relative_to(ROOT).as_posix()] = hashlib.sha256(path.read_bytes()).hexdigest()
    if actual != manifest["sha256"]:
        changed = sorted(key for key in set(actual) | set(manifest["sha256"])
                         if actual.get(key) != manifest["sha256"].get(key))
        raise ValueError("Manifest mismatch: " + ", ".join(changed))
    # The import occurs after the package integrity check.
    from audit_math import audit, regression_checks
    data = json.loads((ROOT / "data" / "inputs.json").read_text(encoding="utf-8"))
    report = {"audit": audit(data), "regression_checks": regression_checks(data)}
    expected = json.loads((ROOT / "evidence" / "expected.json").read_text(encoding="utf-8"))
    if report != expected:
        raise ValueError("Computed report differs from evidence/expected.json")
    print(f"PASS: SHA-256 inventory ({len(actual)} files).")
    print("PASS: 20 alias/auxiliary inequalities and 5 conditional moment families.")
    print("PASS: 2 affine identities and the ordered 10-region partition.")
    print("PASS: 12 invalid mutations rejected; 23 arithmetic diagnostics passed.")
    print("PASS: deterministic report matches evidence/expected.json.")
    print("Scope: partial conditional audit; no Lean verification or full algorithm proof.")
    print("Submission: local draft; see RESULT.json for unresolved publication prerequisites.")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, OSError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        sys.exit(1)
