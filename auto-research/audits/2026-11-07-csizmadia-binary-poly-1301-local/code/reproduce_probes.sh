#!/usr/bin/env bash
# Reproduce the author's two finite certificates on a non-Windows machine.
#
# The shipped probes are Windows-only in two independent ways:
#   1. checks/bounded_chirp_process_limits.hpp installs a Win32 job object and
#      is a no-op elsewhere; both probes FAIL CLOSED when the guard cannot be
#      installed (probe 1: main() returns 2; probe 2: a static EarlyGuard calls
#      ExitProcess(2)).
#   2. probe 2's transitive include of four_bank_five_stage_word_bounded_* does
#      #include <windows.h> / <psapi.h> unconditionally, for a guard() function
#      probe 2 explicitly never calls ((void)&guard).
#
# This script therefore builds a COPY with two disclosed substitutions, from
# code/windows-guard-posix/:
#   - the guard is re-implemented with POSIX rlimits (RLIMIT_CPU = 10s; macOS
#     rejects both RLIMIT_AS and RLIMIT_DATA with EINVAL, so the 64 MiB address
#     space cap is not reproducible here -- the probes use fixed-size static
#     arrays and are run under the 5s wall timeout CERTIFICATES.txt prescribes);
#   - declarations-only stubs satisfy the unconditional <windows.h> include.
# No certificate logic is touched: the patch changes only process-limit code.
#
# usage: bash reproduce_probes.sh <path-to-pinned-paper-dir>
set -euo pipefail
PAPER="${1:-}"
HERE="$(cd "$(dirname "$0")" && pwd)"
SHIM="$HERE/windows-guard-posix"
WORK="$(mktemp -d)"
[ -n "$PAPER" ] || { echo "usage: bash reproduce_probes.sh <papers/03-best-binary/versions/0.2.1>"; exit 64; }
CXX="${CXX:-clang++}"
echo "paper dir : $PAPER"
echo "compiler  : $($CXX --version | head -1)"
echo "work dir  : $WORK"

cp -R "$PAPER/checks" "$WORK/checks"
cp "$SHIM/bounded_chirp_process_limits.hpp" "$WORK/checks/bounded_chirp_process_limits.hpp"
cp "$SHIM/windows.h" "$SHIM/psapi.h" "$WORK/checks/probes/"

# probe 2 calls Win32 ExitProcess(2) from a static initializer; replace by its
# POSIX equivalent. Disclosed, and the only other edit.
python3 - "$WORK/checks/probes/frozen_rectangles.cpp" <<'PY'
import pathlib, sys
p = pathlib.Path(sys.argv[1]); s = p.read_text()
s = s.replace('#include "../bounded_chirp_process_limits.hpp"',
              '#include <cstdlib>\n#include "../bounded_chirp_process_limits.hpp"', 1)
s = s.replace('ExitProcess(2)', 'std::_Exit(2)')
p.write_text(s)
PY

echo
echo "--- A. as shipped: probe 1 refuses to run off Windows ---"
mkdir -p "$WORK/shipped/probes"
cp -R "$PAPER/checks" "$WORK/shipped/checks"
(cd "$WORK/shipped/checks/probes" && "$CXX" -std=c++17 -O2 -Wall -Wextra -Werror \
   -o "$WORK/fc_shipped" finite_certificate.cpp) && echo "compile: OK (clang, -Werror)"
set +e
"$WORK/fc_shipped" >"$WORK/fc_shipped.out" 2>"$WORK/fc_shipped.err"
shipped_rc=$?
set -e
echo "run     : exit=$shipped_rc  stderr=$(cat "$WORK/fc_shipped.err")"
[ "$shipped_rc" -eq 2 ] || { echo "UNEXPECTED: expected the documented fail-closed exit 2"; exit 1; }

echo
echo "--- B. as shipped: probe 2 does not compile off Windows ---"
set +e
(cd "$WORK/shipped/checks/probes" && "$CXX" -std=c++17 -O2 -w -o "$WORK/fr_shipped" frozen_rectangles.cpp) \
  >"$WORK/fr_shipped.log" 2>&1
fr_rc=$?
set -e
echo "compile : exit=$fr_rc"
grep -m2 -E "error:" "$WORK/fr_shipped.log" || true

echo
echo "--- C. with the two disclosed POSIX substitutions: both reproduce ---"
for probe in finite_certificate frozen_rectangles; do
  (cd "$WORK/checks/probes" && "$CXX" -std=c++17 -O2 -Wall -Wextra -Werror \
     -I "$WORK/checks/probes" -o "$WORK/$probe" "$probe.cpp") 2>/dev/null \
    || (cd "$WORK/checks/probes" && "$CXX" -std=c++17 -O2 -w -o "$WORK/$probe" "$probe.cpp")
  start=$(python3 -c 'import time;print(time.time())')
  if command -v timeout >/dev/null 2>&1; then
    timeout 5 "$WORK/$probe" >"$WORK/$probe.out" 2>"$WORK/$probe.err"
  elif command -v gtimeout >/dev/null 2>&1; then
    gtimeout 5 "$WORK/$probe" >"$WORK/$probe.out" 2>"$WORK/$probe.err"
  else
    "$WORK/$probe" >"$WORK/$probe.out" 2>"$WORK/$probe.err"
  fi
  rc=$?
  secs=$(python3 -c "import time;print('%.2f'%(time.time()-$start))")
  exp="$PAPER/checks/expected/$probe.json"
  python3 - "$exp" "$WORK/$probe.out" "$probe" "$rc" "$secs" <<'PY'
import hashlib, pathlib, sys
exp, got, name, rc, secs = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4], sys.argv[5]
e = pathlib.Path(exp).read_bytes().strip(); g = pathlib.Path(got).read_bytes().strip()
print("%-20s exit=%s wall=%ss bytes=%d/%d %s" % (
    name, rc, secs, len(g), len(e), "BYTE_IDENTICAL" if e == g else "DIFFERS"))
print("%-20s sha256(got)=%s" % ("", hashlib.sha256(g).hexdigest()))
sys.exit(0 if e == g else 1)
PY
done

echo
echo "BOTH PROBES REPRODUCED BYTE-IDENTICALLY"
echo "(the author's published expected outputs are not fabricated: a different"
echo " compiler on a different OS regenerates them exactly)"
rm -rf "$WORK"
