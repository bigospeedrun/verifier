#!/usr/bin/python3
"""Trusted entrypoint, executed only inside the outer offline namespace."""
import json
import os
from pathlib import Path
import sys

work = Path(sys.argv[1])
phase = sys.argv[2]
request = json.loads((work / 'control/request.json').read_text())
stage = work / 'stage'
lean = work / 'tools/elan/toolchains' / request['request']['lean_toolchain'].replace('/', '--').replace(':', '---') / 'bin/lake'
comparator = work / 'tools/comparator/.lake/build/bin/comparator'
if phase == 'check':
    # A segment of a chain's kernel check (chain.py): Comparator on export files only. No Lake, no build, no
    # submission code; the trusted controller wrote the arguments.
    args = json.loads((work / 'control/check-args.json').read_text())
    if not isinstance(args, list) or not args or args[0] != '--bos-check' or not all(isinstance(a, str) for a in args):
        raise ValueError('invalid check arguments')
    os.execve(str(comparator), [str(comparator), *args], dict(os.environ, LEAN_NUM_THREADS='4'))
if phase.endswith('-exec'):
    # `lake env` prepends its toolchain bin to PATH. Restore the reviewed
    # adapter only after Lake has supplied LEAN_PATH and other package paths.
    kernel = phase.removesuffix('-exec')
    if kernel not in ['lean', 'nanoda', 'challenge', 'export']:
        raise ValueError('invalid kernel phase')
    env = dict(os.environ, LEAN_NUM_THREADS='4')
    env['PATH'] = str(work / 'control/bin') + ':' + env['PATH']
    if kernel == 'nanoda':
        # The nanoda thread count of this attempt (verifier.py NANODA_THREADS), from a file that only the controller writes.
        # Comparator with patches/comparator-nanoda-threads.patch reads it; an unpatched Comparator ignores it.
        threads_file = work / 'control/nanoda-threads.txt'
        if threads_file.exists():
            threads = threads_file.read_text()
            if threads not in ['1\n', '2\n', '3\n', '4\n']:
                raise ValueError('invalid nanoda thread count')
            env['COMPARATOR_NANODA_THREADS'] = threads.strip()
        # The nanoda worker stack of this attempt in MiB (verifier.py NANODA_STACK_MIB), from a file that only the controller writes.
        stack_file = work / 'control/nanoda-stack.txt'
        if stack_file.exists():
            stack = stack_file.read_text()
            if stack not in ['256\n', '1024\n', '4096\n']:
                raise ValueError('invalid nanoda stack size')
            env['COMPARATOR_NANODA_STACK_MIB'] = stack.strip()
    if kernel in ['challenge', 'export']:
        # A chain's export job (chain.py): the challenge build and export, in its own unit before any submission
        # build file is restored; then the solution build and export. Each writes one file in /tmp.
        mode, name = ('--bos-export-challenge', 'challenge') if kernel == 'challenge' else ('--bos-export-solution', 'solution')
        os.execve(str(comparator), [str(comparator), mode, str(work / 'control/lean.json'), f'/tmp/{name}.export'], env)
    os.execve(str(comparator), [str(comparator), str(work / f'control/{kernel}.json')], env)
# Every phase but the build runs Lean with 4 threads. Set it before the branches, so that the
# audit has it too (verifier#188: 195060b2 set it only in the else branch, and the audit's
# execve below raised NameError).
threads = '4'
if phase == 'audit':
    args = [str(lean), 'env', 'lean', str(stage / 'VerifierAudit.lean')]
else:
    # Submission code can write build products. Never trust its copy of the
    # challenge .olean/trace on a later run. Removal itself stays sandboxed,
    # so hostile output symlinks cannot reach the host checkout or receipts.
    for facet in ['lib/lean', 'ir']:
        parent = stage / '.lake/build' / facet
        if parent.exists():
            for path in parent.glob('VerifierChallenge.*'):
                if path.is_dir() and not path.is_symlink():
                    raise RuntimeError('unexpected challenge output directory')
                path.unlink()
    if phase == 'build':
        # Split job 1: one parallel build with the real Lake, not the chain shim. Lake's
        # LEAN_NUM_THREADS sets how many modules build at once (verifier.py LAKE_WORKERS).
        threads = sys.argv[3] if len(sys.argv) == 4 else ''
        if threads not in ['1', '2', '3', '4']:
            raise ValueError('invalid Lake worker count')
        args = [str(lean), 'build', request['profile']['solution_module']]
    else:
        args = [str(lean), 'env', '/usr/bin/python3', str(work / 'control/inside.py'),
                str(work), phase + '-exec']
os.execve(str(lean), args, dict(os.environ, LEAN_NUM_THREADS=threads))
