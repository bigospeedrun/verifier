"""Reproduce the provenance checks of this package and, with --lean, its Lean checks."""
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import tempfile
from pathlib import Path

PACKAGE = Path(__file__).resolve().parent
ROOT = PACKAGE.parents[2]
CHALLENGE = ROOT / 'challenges/subset-sum'
TOOLCHAIN = 'leanprover/lean4:v4.33.1'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
AUDITED = [
    'BigOSpeedrun.SubsetSum.SolvedInTime', 'bigO_49_100', 'BigO.mono',
    'SolvedInTime.mono', 'accept_correct', 'reject_not_correct',
]
EXPECTED_EVAL = [
    'some true', 'none', 'some false', 'some false', 'some true',
    '8', 'some false', 'some true', '20', '42', '1', '3', '4',
]


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def ceil_log2(m):
    """Smallest k with 2^k >= m, for m >= 1, by direct search."""
    k = 0
    while 2 ** k < m:
        k += 1
    return k


def floor_log2(m):
    """Nat.log2: largest k with 2^k <= m, and 0 for m = 0."""
    k = 0
    while 2 ** (k + 1) <= m:
        k += 1
    return k


def word_length(n, b):
    return 4 * (n + b) + floor_log2((n + 2) ** 4 - 1) + 1


def bits(m):
    return floor_log2(m) + 1


def ceiling_identities():
    values = list(range(0, 5000)) + [2 ** k + d for k in range(13, 300, 7) for d in (-1, 0, 1)]
    for n in range(2, 1500):
        for b in (1, 2, 7, 64, n, n * n):
            # w = ceil(4(n + b + log2(n + 2))) = 4(n + b) + ceil(log2((n + 2)^4))
            require(word_length(n, b) == 4 * (n + b) + ceil_log2((n + 2) ** 4),
                    f'word length identity fails at n={n}, b={b}')
    for m in values:
        expected = max(1, ceil_log2(1 + m))
        require(bits(m) == expected, f'bit length identity fails at m={m}')
        require(m == 0 or bits(m) == m.bit_length(), f'bit length differs from bit_length at m={m}')


def static_checks():
    manifest = json.loads((PACKAGE / 'MANIFEST.json').read_text())
    require(manifest['algorithm'] == 'sha256', 'unexpected hash algorithm')
    files = {p.relative_to(PACKAGE).as_posix(): p for p in PACKAGE.rglob('*')
             if p.is_file() and p != PACKAGE / 'MANIFEST.json'}
    require(files.keys() == manifest['sha256'].keys(), 'manifest file set mismatch')
    for name, path in files.items():
        require(not path.is_symlink(), f'symlink: {name}')
        require(path.stat().st_mode & 0o111 == 0, f'executable file: {name}')
        require(sha256(path) == manifest['sha256'][name], f'package hash mismatch: {name}')
    hashes = json.loads((PACKAGE / 'data/challenge-hashes.json').read_text())
    for name, digest in hashes['challenge'].items():
        require(sha256(ROOT / name) == digest, f'challenge hash mismatch: {name}')
    for name, digest in hashes['pins'].items():
        require(sha256(ROOT / name) == digest, f'pinned file changed: {name}')
    ceiling_identities()
    print('PASS: package manifest, challenge hashes, unchanged 3SUM/APSP statement and profile pins, '
          'ceiling identities')


def lean_command():
    lean = shutil.which('lean')
    require(lean is not None, 'lean not found on PATH')
    for cmd in ([lean, '+' + TOOLCHAIN], [lean]):
        probe = subprocess.run(cmd + ['--version'], capture_output=True, text=True)
        if probe.returncode == 0 and '4.33.1' in probe.stdout:
            return cmd
    raise RuntimeError('Lean 4.33.1 is required; install it with elan')


def lean_checks():
    cmd = lean_command()
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp)
        shutil.copyfile(CHALLENGE / 'Statement.lean', work / 'Statement.lean')
        shutil.copyfile(PACKAGE / 'code/Checks.lean', work / 'Checks.lean')
        env = dict(os.environ, LEAN_PATH=str(work))
        first = subprocess.run(cmd + ['-DwarningAsError=true', '-o', 'Statement.olean', 'Statement.lean'],
                               cwd=work, env=env, capture_output=True, text=True)
        require(first.returncode == 0 and first.stdout.strip() == '' and first.stderr.strip() == '',
                f'Statement.lean failed:\n{first.stdout}{first.stderr}')
        second = subprocess.run(cmd + ['-DwarningAsError=true', 'Checks.lean'],
                                cwd=work, env=env, capture_output=True, text=True)
        require(second.returncode == 0 and second.stderr.strip() == '',
                f'Checks.lean failed:\n{second.stdout}{second.stderr}')
    lines = [line.rstrip() for line in second.stdout.splitlines() if line.strip()]
    evals = [line for line in lines if not line.startswith("'")]
    require(evals == EXPECTED_EVAL, f'unexpected #eval output: {evals}')
    axioms = {}
    for line in lines:
        if line.startswith("'") and ' depends on axioms: ' in line:
            name, rest = line[1:].split("' depends on axioms: ", 1)
            axioms[name] = {a.strip() for a in rest.strip('[]').split(',') if a.strip()}
    for name in AUDITED:
        require(name in axioms, f'no axiom line for {name}')
        require(axioms[name] <= ALLOWED, f'{name} uses axioms {axioms[name]}')
    print('PASS: Lean statement, rational substitution, wrong-bound elaboration check, monotonicity, '
          'correct and incorrect program, executable semantics, allowed axioms')
    print('SCOPE: statement validation only; no production Comparator receipt and no Subset Sum bound')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', action='store_true', help='also compile the statement and checks')
    args = parser.parse_args()
    static_checks()
    if args.lean:
        lean_checks()


if __name__ == '__main__':
    main()
