"""Reproduce provenance checks, and optionally the Lean checks on GitHub Actions."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tarfile
import tempfile
import urllib.request

PACKAGE = Path(__file__).resolve().parent
ROOT = PACKAGE.parents[2]
CHALLENGE = ROOT / 'challenges/matrix-multiplication'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
DECLARATIONS = {
    'BigOSpeedrun.MatrixMultiplication.Bound',
    'BigOSpeedrun.MatrixMultiplication.bound_iff',
    'BigOSpeedrun.MatrixMultiplication.Bound.mono',
    'scalar_correct', 'scalar_cost',
}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def git_blob(path):
    data = path.read_bytes()
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def static_checks():
    inputs = json.loads((PACKAGE / 'data/inputs.json').read_text())
    manifest = json.loads((PACKAGE / 'MANIFEST.json').read_text())
    require(manifest['algorithm'] == 'sha256', 'unexpected hash algorithm')
    # A manifest cannot contain its own digest; every other package file is covered.
    files = {p.relative_to(PACKAGE).as_posix(): p for p in PACKAGE.rglob('*')
             if p.is_file() and p != PACKAGE / 'MANIFEST.json'}
    require(files.keys() == manifest['sha256'].keys(), 'manifest file set mismatch')
    for name, path in files.items():
        require(not path.is_symlink(), f'symlink: {name}')
        require(path.stat().st_mode & 0o111 == 0, f'executable file: {name}')
        require(hashlib.sha256(path.read_bytes()).hexdigest() == manifest['sha256'][name],
                f'package hash mismatch: {name}')
    for path, pin in [
        (CHALLENGE / 'MatrixMultiplication.lean', 'source_git_blob'),
        (CHALLENGE / 'LICENSE', 'upstream_license_git_blob'),
        (ROOT / 'profiles/lake-manifest.json', 'manifest_git_blob'),
    ]:
        require(git_blob(path) == inputs[pin], f'upstream pin mismatch: {path.name}')
    source_pins = json.loads((PACKAGE / 'data/challenge-hashes.json').read_text())
    for name, digest in source_pins.items():
        path = CHALLENGE / name
        require(not path.is_symlink(), f'challenge symlink: {name}')
        require(path.stat().st_mode & 0o111 == 0, f'challenge executable: {name}')
        require(hashlib.sha256(path.read_bytes()).hexdigest() == digest,
                f'challenge hash mismatch: {name}')
    print('PASS: package manifest, unchanged upstream model/license/dependency pins, challenge hashes', flush=True)
    return inputs


def run(args, cwd, env, capture=False):
    print('+ ' + ' '.join(map(str, args)), flush=True)
    result = subprocess.run(list(map(str, args)), cwd=cwd, env=env, text=True,
                            stdout=subprocess.PIPE if capture else None,
                            stderr=subprocess.STDOUT if capture else None)
    if capture:
        print(result.stdout, end='', flush=True)
    require(result.returncode == 0, f'command failed with exit {result.returncode}')
    return result.stdout if capture else ''


def audit_axioms(output):
    seen = set()
    for name, axioms, empty_name in re.findall(
            r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]|'([^']+)' does not depend on any axioms",
            output):
        declaration = name or empty_name
        if declaration not in DECLARATIONS:
            continue
        used = {a.strip() for a in axioms.split(',') if a.strip()}
        require(used <= ALLOWED, f'forbidden axiom in {declaration}: {used - ALLOWED}')
        seen.add(declaration)
    require(seen == DECLARATIONS, f'missing axiom reports: {DECLARATIONS - seen}')


def lean_checks(inputs):
    require(os.environ.get('GITHUB_ACTIONS') == 'true',
            '--lean runs only on GitHub Actions, per this repository AGENTS.md')
    pins = json.loads((PACKAGE / 'data/tools.json').read_text())
    with tempfile.TemporaryDirectory(prefix='bos-matrix-statement-') as folder:
        work = Path(folder)
        archive = work / 'elan.tar.gz'
        url = ('https://github.com/leanprover/elan/releases/download/'
               + pins['elan_version'] + '/elan-x86_64-unknown-linux-gnu.tar.gz')
        with urllib.request.urlopen(url, timeout=60) as response:
            archive.write_bytes(response.read())
        require(hashlib.sha256(archive.read_bytes()).hexdigest() == pins['elan_tar_sha256'],
                'elan archive hash mismatch')
        with tarfile.open(archive) as tar:
            tar.extractall(work, filter='data')
        env = dict(os.environ, ELAN_HOME=str(work / 'elan'), LEAN_NUM_THREADS='2')
        run([work / 'elan-init', '-y', '--no-modify-path', '--default-toolchain', 'none'], work, env)
        run([work / 'elan/bin/elan', 'toolchain', 'install', inputs['lean_toolchain']], work, env)
        env['PATH'] = str(work / 'elan/bin') + os.pathsep + env['PATH']
        (work / 'lean-toolchain').write_text(inputs['lean_toolchain'] + '\n')
        (work / 'lakefile.toml').write_text(
            'name = "Verifier"\nversion = "0.1.0"\n'
            '[leanOptions]\nautoImplicit = false\n'
            '[[require]]\nname = "mathlib"\n'
            'git = "https://github.com/leanprover-community/mathlib4.git"\n'
            'rev = "' + inputs['mathlib_commit'] + '"\n'
            '[[lean_lib]]\nname = "MatrixMultiplication"\n'
            '[[lean_lib]]\nname = "Statement"\n')
        shutil.copyfile(ROOT / 'profiles/lake-manifest.json', work / 'lake-manifest.json')
        packages = work / '.lake/packages'
        packages.mkdir(parents=True)
        manifest = json.loads((work / 'lake-manifest.json').read_text())
        for package in manifest['packages']:
            dest = packages / package['name']
            dest.mkdir()
            run(['git', 'init', '-q'], dest, env)
            run(['git', 'remote', 'add', 'origin', package['url']], dest, env)
            run(['git', 'fetch', '-q', '--depth', '1', 'origin', package['rev']], dest, env)
            run(['git', 'checkout', '-q', '--detach', 'FETCH_HEAD'], dest, env)
            head = run(['git', 'rev-parse', 'HEAD'], dest, env, capture=True).strip()
            require(head == package['rev'], f'dependency revision mismatch: {package["name"]}')
        for name in ['MatrixMultiplication.lean', 'Statement.lean']:
            shutil.copyfile(CHALLENGE / name, work / name)
        shutil.copyfile(PACKAGE / 'code/Checks.lean', work / 'Checks.lean')
        run(['lake', 'exe', 'cache', 'get'], work, env)
        # The frozen challenge has three upstream theorem placeholders.
        # Only the new adapter and checks must build with no warnings/sorries.
        (work / '.lake/build/lib/lean').mkdir(parents=True, exist_ok=True)
        run(['lake', 'env', 'lean', '-o', '.lake/build/lib/lean/MatrixMultiplication.olean',
             'MatrixMultiplication.lean'], work, env)
        run(['lake', 'env', 'lean', '-DwarningAsError=true', '-o',
             '.lake/build/lib/lean/Statement.olean', 'Statement.lean'], work, env)
        output = run(['lake', 'env', 'lean', '-DwarningAsError=true', 'Checks.lean'],
                     work, env, capture=True)
        audit_axioms(output)
        print('PASS: Lean statement, rational substitution, wrong-bound type check, monotonicity, scalar circuit, allowed axioms', flush=True)
        print('SCOPE: statement validation only; no production Comparator receipt or new matrix bound', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', action='store_true', help='run pinned Lean checks on GitHub Actions')
    args = parser.parse_args()
    configuration = static_checks()
    if args.lean:
        lean_checks(configuration)
