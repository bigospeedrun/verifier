#!/usr/bin/env python3
"""Reproduce the local audit of the DFT sota submission 312780997/1e11 (PR #91).

Clones HalitZiyaKARTAL/bigO-dft-verifier at the pinned SHA, stages the verifier's
own build layout (VerifierChallenge with the generated Race.bound target at the
submitted bound, the Submission tree, a VerifierAudit axiom probe), builds with
Lean 4.34.1 / mathlib d13f23b, prints the axiom closure of Race.bound, and
re-runs the comment-stripped textual diff of the computational model.

Read-only with respect to the submission repository.

Usage:
  python3 verify.py [--workdir DIR] [--packages-cache DIR]

--packages-cache may point at a warm .lake/packages tree for the pinned
mathlib (e.g. a previous audit's stage); without it Lake fetches and builds
mathlib itself (hours).
"""
import argparse
import json
import re
import shutil
import subprocess
import sys
import time
from fractions import Fraction
from pathlib import Path

REPO = 'https://github.com/HalitZiyaKARTAL/bigO-dft-verifier.git'
SHA = '524a8af8a277ca50c1237068c2b45430a03f547e'
SUBDIR = 'submissions/dft/halitziyakartal-halitziyav5-pre-pi'
CHALLENGE = 'challenges/dft/UniformFourier233.lean'
BOUND = (312780997, 100000000000)
TOOLCHAIN = 'leanprover/lean4:v4.34.1'
MATHLIB_REV = 'd13f23b723b8a846827a245b89c10fc7d3f11612'
AXIOMS_OK = {'propext', 'Quot.sound', 'Classical.choice'}


def run(args, **kw):
    print('+', ' '.join(map(str, args)), flush=True)
    return subprocess.run([str(a) for a in args], check=True, **kw)


def strip_comments(text):
    """Lean nested block comments and line comments, preserving newlines
    (mirrors the verifier's own strip_comments)."""
    out, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1; out.append('  '); i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1; out.append('  '); i += 2
        elif depth:
            out.append(text[i] if text[i] == '\n' else ' '); i += 1
        elif text.startswith('--', i):
            while i < len(text) and text[i] != '\n':
                i += 1
        else:
            out.append(text[i]); i += 1
    return ''.join(out)


def norm(text):
    return re.sub(r'\s+', ' ', strip_comments(text)).strip()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--workdir', default='audit-dft-91-work')
    ap.add_argument('--packages-cache', default=None)
    opt = ap.parse_args()
    work = Path(opt.workdir).resolve()
    if work.exists():
        sys.exit(f'{work} exists; remove it first')
    clone = work / 'clone'
    run(['git', 'init', clone])
    run(['git', '-C', clone, 'fetch', '--depth=1', REPO, SHA])
    run(['git', '-C', clone, 'checkout', '--detach', 'FETCH_HEAD'])
    assert subprocess.check_output(['git', '-C', clone, 'rev-parse', 'HEAD'],
                                   text=True).strip() == SHA

    stage = work / 'stage'
    stage.mkdir(parents=True)
    sub = clone / SUBDIR
    shutil.copyfile(sub / 'Submission.lean', stage / 'Submission.lean')
    shutil.copytree(sub / 'Submission', stage / 'Submission')
    # VerifierChallenge: the trusted challenge plus the verifier's generated
    # Race.bound target at the submitted bound (scripts/submissions.py
    # challenge_source for problem dft, entrypoint Race.bound).
    n, d = BOUND
    target = (f'\n-- Big O Speedrun exact-bound target; generated from validated integers.\n'
              f'open OAI.PowerSaving Filter Asymptotics\n\n'
              f'theorem Race.bound : ∃ order solve W, DFTProgram order solve W ∧\n'
              f'    (fun n : ℕ => (W n : ℝ)) =O[atTop]\n'
              f'      (fun n : ℕ => (n : ℝ) * (Real.log (n : ℝ)) ^ (1 - ({n} : ℝ) / {d})) := by\n'
              f'  sorry\n')
    (stage / 'VerifierChallenge.lean').write_text(
        (clone / CHALLENGE).read_text() + target)
    (stage / 'VerifierAudit.lean').write_text('import Submission\n#print axioms Race.bound\n')
    (stage / 'lean-toolchain').write_text(TOOLCHAIN + '\n')
    shutil.copyfile(clone / 'profiles/lake-manifest.json', stage / 'lake-manifest.json')
    (stage / 'lakefile.toml').write_text(f'''name = "Verifier"
version = "0.1.0"
[leanOptions]
autoImplicit = false
[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "{MATHLIB_REV}"

[[lean_lib]]
name = "Submission"

[[lean_lib]]
name = "VerifierChallenge"

[[lean_lib]]
name = "VerifierAudit"
''')
    (stage / '.lake/build').mkdir(parents=True)
    if opt.packages_cache:
        shutil.copytree(opt.packages_cache, stage / '.lake/packages')

    # Scope: the RAM model section of the trusted challenge must equal the
    # submission's copy, comment-stripped and whitespace-normalized.
    ch = (clone / CHALLENGE).read_text()
    ram = (stage / 'Submission/OAI/Computability/FourierTransform/RAM.lean').read_text()
    ch_model = re.search(r'namespace PowerSaving.*?end PowerSaving', ch, re.S).group(0)
    s_model = re.search(r'namespace PowerSaving.*?end PowerSaving', ram, re.S).group(0)
    model_ok = norm(ch_model) == norm(s_model)
    print('model section comment-stripped identical:', model_ok)

    t0 = time.time()
    log = work / 'local-build.log'
    with log.open('w') as f:
        run(['lake', 'build', 'VerifierChallenge', 'VerifierAudit'], cwd=stage, stdout=f,
            stderr=subprocess.STDOUT)
    print(f'lake build exit 0 in {time.time() - t0:.0f}s')

    m = re.search(r"'Race.bound' depends on axioms: \[(.*?)\]", log.read_text())
    axioms = {a.strip() for a in m.group(1).split(',')} if m else set()
    print('Race.bound axioms:', sorted(axioms))
    ok = model_ok and axioms <= AXIOMS_OK and axioms
    print('AUDIT', 'PASS' if ok else 'FAIL')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
