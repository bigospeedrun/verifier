#!/usr/bin/env python3
"""Trusted controller. Never execute this file from a submission."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import stat
import subprocess
import sys
import tarfile
import threading
import time
import urllib.parse
from datetime import datetime, timezone
from verdicts import kernel_outcome

ROOT = Path(__file__).resolve().parents[1]
ART = ROOT / 'artifacts'
WORK = Path(os.environ.get('RUNNER_TEMP', str(ROOT / '.work'))) / 'bos-verifier'
NAME = re.compile(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*\Z')
SHA = re.compile(r'[0-9a-f]{40}\Z')
AXIOMS = ['propext', 'Quot.sound', 'Classical.choice']
# Total check deadline from prepare, in each job.
DEADLINE_SECONDS = 320 * 60


def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + '.tmp')
    tmp.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')
    tmp.replace(path)


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda: f.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def receipt():
    return json.loads((ART / 'receipt.json').read_text())


def save(data):
    write_json(ART / 'receipt.json', data)


def command(args, label, cwd=None, env=None):
    print(f'{label}: started', flush=True)
    start = time.monotonic()
    with (ART / f'{label}.log').open('w') as log:
        p = subprocess.run([str(x) for x in args], cwd=cwd, env=env,
                           stdout=log, stderr=subprocess.STDOUT, check=False)
    data = receipt()
    data['steps'].append({'name': label, 'exit_code': p.returncode,
                          'wall_seconds': round(time.monotonic() - start, 3)})
    save(data)
    if p.returncode:
        raise RuntimeError(f'{label} failed with exit {p.returncode}; see artifact log')
    print(f'{label}: passed', flush=True)


def validate_request(request):
    url = request['repo_url']
    if not re.fullmatch(r'https://github\.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+(?:\.git)?', url):
        raise ValueError('repo_url must be a public https://github.com/OWNER/REPO URL')
    if not SHA.fullmatch(request['commit']):
        raise ValueError('commit must be a complete lowercase 40-digit Git SHA')
    if 'direct_submission' in request:
        from submissions import resolve_request
        profile, names = resolve_request(request)
        return profile, names
    profile = None
    for p in sorted((ROOT / 'profiles').glob('*.json')):
        candidate = json.loads(p.read_text())
        if isinstance(candidate, dict) and candidate.get('challenge_file') == request['challenge_file']:
            profile = candidate
    if profile is None:
        raise ValueError('challenge_file is not a registered verifier-owned challenge')
    if request['lean_toolchain'] != profile['lean_toolchain']:
        raise ValueError('toolchain does not match the reviewed challenge profile')
    names = [n for n in re.split(r'[\s,]+', request['theorem_names'].strip()) if n]
    if not names or len(names) != len(set(names)) or any(
            not NAME.fullmatch(n) or n not in profile['theorem_names'] for n in names):
        raise ValueError('theorem_names must be distinct names from the challenge profile')
    if digest(ROOT / profile['challenge_file']) != profile['challenge_sha256']:
        raise ValueError('trusted challenge digest does not match its reviewed profile')
    return profile, names


def clone(url, sha, dest, label, sparse_paths=None):
    dest.mkdir(parents=True)
    # No submodules, hooks, credential helper, or submission build commands.
    command(['git', 'init', dest], label + '-init')
    common = ['git', '-C', dest, '-c', 'core.hooksPath=/dev/null',
              '-c', 'credential.helper=', '-c', 'protocol.file.allow=never',
              '-c', 'filter.lfs.required=false', '-c', 'filter.lfs.smudge=', '-c', 'filter.lfs.process=']
    command(common + ['fetch', '--depth=1', url, sha], label + '-fetch')
    if sparse_paths:
        command(common + ['sparse-checkout', 'set', '--no-cone', *sparse_paths], label + '-sparse')
    command(common + ['checkout', '--detach', 'FETCH_HEAD'], label + '-checkout')
    actual = subprocess.check_output(['git', '-C', dest, 'rev-parse', 'HEAD'], text=True).strip()
    if actual != sha:
        raise ValueError('fetched commit does not match the requested pin')


def strip_comments(text):
    """Lean nested block comments and line comments, preserving newlines."""
    out, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1; out.append('  '); i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1; out.append('  '); i += 2
        elif not depth and text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        else:
            out.append(text[i] if not depth or text[i] == '\n' else ' '); i += 1
    if depth:
        raise ValueError('unclosed block comment in source')
    return ''.join(out)


def plan_sources(stage, root):
    """Only ordinary import headers are supported. Reject ambiguous planning."""
    done, visiting, order, closures = set(), set(), [], {}
    def visit(module):
        if module in done:
            return closures[module]
        if module in visiting:
            raise ValueError('cyclic submission imports')
        path = stage / (module.replace('.', '/') + '.lean')
        if not path.is_file():
            return set()  # fixed external package (checked by Lake)
        visiting.add(module)
        deps = set()
        for line in strip_comments(path.read_text()).splitlines():
            s = line.strip()
            if not s or s in ['prelude', 'module']:
                continue
            header = re.fullmatch(r'(?:(?:public|private|meta)\s+)*import\s+(.+)', s)
            if not header:
                break
            imports = header[1].split()
            if not imports or any(not NAME.fullmatch(n) for n in imports):
                raise ValueError('unsupported import header')
            for name in imports:
                if name.startswith('VerifierChallenge') or name.startswith('VerifierAudit'):
                    raise ValueError('submission imports a reserved verifier module')
                deps.add(name); deps.update(visit(name))
        visiting.remove(module); done.add(module); closures[module] = deps; order.append(module)
        return deps
    visit(root)
    if root not in done:
        raise ValueError('solution module is missing')
    chains = []
    for module in order:
        if chains and chains[-1][-1] in closures[module]:
            chains[-1].append(module)
        else:
            chains.append([module])
    seen = set()
    for chain in chains:
        for module in chain:
            if not (closures[module] & done) <= seen:
                raise ValueError('build order has an unmet local dependency')
            seen.add(module)
    return chains


def chain_targets(profile, chains):
    # Split profile: job 1 built the solution, so the shim makes one Lake call (docs/execution.md).
    if profile.get('runner') == 'github-split':
        return profile['solution_module'] + '\n'
    return ''.join(chain[-1] + '\n' for chain in chains)


# The Lean options that a solution dependency may set: those of a reviewed upstream build (eth, integer factoring).
# A new option needs review; Comparator and nanoda re-check every exported term in any case.
LEAN_OPTION_NAMES = {'autoImplicit', 'relaxedAutoImplicit', 'exponentiation.threshold', 'pp.unicode.fun'}


def lean_options(options):
    """Lake [leanOptions] lines: reviewed option names, and boolean or non-negative integer values only."""
    if not isinstance(options, dict) or not options:
        raise ValueError('lean_options must be a non-empty object')
    lines = ''
    for name, value in sorted(options.items()):
        if not isinstance(name, str) or name not in LEAN_OPTION_NAMES:
            raise ValueError('Lean option name is not in LEAN_OPTION_NAMES')
        if isinstance(value, bool):
            lines += f'{name} = {"true" if value else "false"}\n'
        elif type(value) is int and value >= 0:
            lines += f'{name} = {value}\n'
        else:
            raise ValueError('a Lean option value must be a boolean or a non-negative integer')
    return lines


def lakefile(roots, manifest_file='profiles/lake-manifest.json', auto_implicit=False, root_options=None):
    # A profile may keep Lean's default autoImplicit=true when its upstream build does
    # (integer factoring). It only changes how sources elaborate; Comparator checks the result.
    # root_options gives a root the Lean options of its own upstream build (a solution dependency's
    # lean_options); Lake applies a library's leanOptions after the package's.
    result = '''name = "Verifier"
version = "0.1.0"
[leanOptions]
autoImplicit = false
[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "d13f23b723b8a846827a245b89c10fc7d3f11612"
'''
    manifest = json.loads((ROOT / manifest_file).read_text())
    mathlib = next(p for p in manifest['packages'] if p['name'] == 'mathlib')
    result = result.replace('d13f23b723b8a846827a245b89c10fc7d3f11612', mathlib['rev'])
    if auto_implicit is not False:
        if auto_implicit is not True:
            raise ValueError('auto_implicit must be a boolean')
        result = result.replace('autoImplicit = false', 'autoImplicit = true')
    root_options = root_options or {}
    if set(root_options) - set(roots):
        raise ValueError('Lean options for a root that is not built')
    for name in roots:
        if not NAME.fullmatch(name):
            raise ValueError('invalid library name')
        result += f'\n[[lean_lib]]\nname = {json.dumps(name)}\n'
        if name in root_options:
            result += '[lean_lib.leanOptions]\n' + lean_options(root_options[name])
    return result


def dependency_root_options(dependencies, source_roots):
    """Each root of a solution dependency with lean_options gets those options.
    A dependency root must not be a submission root, a Verifier* root or a reserved root: this fails at
    prepare, before the build (build_roots refuses the last two again in pack and unpack)."""
    options = {}
    for dep in dependencies:
        for root in dep['source_roots']:
            if root in source_roots or root.startswith('Verifier') or root in RESERVED_ROOTS:
                raise ValueError('a solution dependency root must not be a submission, Verifier or reserved root')
        if 'lean_options' not in dep:
            continue
        lean_options(dep['lean_options'])
        for root in dep['source_roots']:
            if root in options and options[root] != dep['lean_options']:
                raise ValueError('two solution dependencies give one root different Lean options')
            options[root] = dep['lean_options']
    return options


def prepare():
    ART.mkdir(exist_ok=True)
    selected_path = os.environ.get('BOS_REQUEST_PATH')
    selected_flags = json.loads(Path(selected_path).read_text()) if selected_path else {}
    data = {'schema_version': 1, 'test_only': selected_flags.get('test_only', False), 'started_unix': time.time(), 'status': 'preparing',
            'verifier_commit': os.environ.get('BOS_VERIFIER_COMMIT', os.environ.get('GITHUB_SHA')),
            'run_url': f"https://github.com/{os.environ.get('GITHUB_REPOSITORY', '')}/actions/runs/{os.environ.get('GITHUB_RUN_ID', '')}",
            'steps': [], 'kernels': {'lean': {'status': 'not_started'}, 'nanoda': {'status': 'not_started'}},
            'axiom_audit': {'status': 'not_started'}}
    save(data)
    request_path = os.environ.get('BOS_REQUEST_PATH')
    event = json.loads(Path(request_path or os.environ['GITHUB_EVENT_PATH']).read_text())
    request = event['inputs']
    profile, names = validate_request(request)
    WORK.mkdir(parents=True, exist_ok=False)
    (WORK / 'control').mkdir(); (WORK / 'tools').mkdir()
    write_json(WORK / 'control/request.json', {'request': request, 'profile': profile, 'names': names})
    data.update(request=request, profile=profile, theorem_names=names)
    save(data)
    clone_options = {'sparse_paths': profile['sparse_paths']} if profile.get('sparse_paths') else {}
    clone(request['repo_url'], request['commit'], WORK / 'clone', 'submission', **clone_options)
    sources = [(WORK / 'clone', request.get('source_subdir', profile.get('source_subdir', '')),
                profile['source_roots'], profile.get('source_prefixes', []))]
    dependencies = profile.get('solution_dependencies', [])
    for index, dep in enumerate(dependencies):
        location = WORK / f'solution-dependency-{index}'
        clone(dep['repo_url'], dep['commit'], location, f'solution-dependency-{index}')
        if dep.get('patch_file'):
            patch_file = ROOT / dep['patch_file']
            if digest(patch_file) != dep['patch_sha256']:
                raise ValueError('solution compatibility patch digest mismatch')
            command(['git', '-C', location, 'apply', '--check', patch_file], f'solution-dependency-{index}-patch-check')
            command(['git', '-C', location, 'apply', patch_file], f'solution-dependency-{index}-patch')
        sources.append((location, dep.get('source_subdir', ''), dep['source_roots'], []))
    data = receipt(); data['solution_dependencies'] = dependencies; save(data)
    stage = WORK / 'stage'; stage.mkdir()
    hashes, total = {}, 0
    for location, subdir, roots, prefixes in sources:
        tracked = subprocess.check_output(['git', '-C', location, 'ls-tree', '-rz', 'HEAD'])
        for entry in tracked.split(b'\0'):
            if not entry:
                continue
            meta, rawpath = entry.split(b'\t', 1); mode = meta.split()[0]
            source_rel = Path(rawpath.decode('utf-8'))
            rel = source_rel
            if subdir:
                try:
                    rel = source_rel.relative_to(subdir)
                except ValueError:
                    continue
            if not rel.parts or rel.parts[0].removesuffix('.lean') not in roots or rel.suffix != '.lean':
                continue
            if prefixes and not any(rel.is_relative_to(prefix) for prefix in prefixes):
                continue
            module = '.'.join(rel.with_suffix('').parts)
            if mode != b'100644' or not NAME.fullmatch(module):
                raise ValueError('only regular Lean source files with ordinary module names are admitted')
            source = location / source_rel
            if source.stat().st_size > 20_000_000:
                raise ValueError('individual Lean source exceeds 20 MB')
            total += source.stat().st_size
            if total > 150_000_000:
                raise ValueError('Lean source input exceeds 150 MB')
            target = stage / rel
            if target.exists():
                raise ValueError('solution dependency collides with a staged source module')
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, target); hashes[str(rel)] = digest(target)
    write_json(ART / 'source-sha256.json', hashes)
    chains = plan_sources(stage, profile['solution_module'])
    write_json(WORK / 'control/chains.json', chains)
    (WORK / 'control/chain-targets.txt').write_text(chain_targets(profile, chains))
    if 'direct_submission' in request:
        from submissions import challenge_source
        (stage / 'VerifierChallenge.lean').write_text(challenge_source(request['direct_submission']))
    else:
        shutil.copyfile(ROOT / profile['challenge_file'], stage / 'VerifierChallenge.lean')
    data = receipt(); data['generated_challenge_sha256'] = digest(stage / 'VerifierChallenge.lean'); save(data)
    (stage / 'VerifierAudit.lean').write_text('import ' + profile['solution_module'] + '\n' +
                                           ''.join('#print axioms ' + n + '\n' for n in names))
    (stage / 'lakefile.toml').write_text(lakefile(profile['source_roots'] + [root for dep in dependencies for root in dep['source_roots']] + ['VerifierChallenge', 'VerifierAudit'], profile.get('manifest_file', 'profiles/lake-manifest.json'), profile.get('auto_implicit', False), dependency_root_options(dependencies, profile['source_roots'])))
    (stage / 'lean-toolchain').write_text(request['lean_toolchain'] + '\n')
    shutil.copyfile(ROOT / profile.get('manifest_file', 'profiles/lake-manifest.json'), stage / 'lake-manifest.json')
    (stage / '.lake/build').mkdir(parents=True); (stage / '.lake/packages').mkdir()
    (stage / '.lake/config').mkdir()
    (WORK / 'scratch').mkdir()
    for kernel in ['lean', 'nanoda']:
        write_json(WORK / f'control/{kernel}.json', {'challenge_module': 'VerifierChallenge',
                   'solution_module': profile['solution_module'], 'theorem_names': names,
                   'definition_names': [], 'permitted_axioms': AXIOMS, 'enable_nanoda': kernel == 'nanoda'})
    data = receipt(); data['status'] = 'prepared'; data['source_file_count'] = len(hashes); save(data)


def setup():
    profile = json.loads((WORK / 'control/request.json').read_text())['profile']
    pins = json.loads((ROOT / profile.get('tools_file', 'profiles/tools.json')).read_text())
    request = json.loads((WORK / 'control/request.json').read_text())['request']
    tools = WORK / 'tools'
    command(['sudo', 'apt-get', 'update'], 'apt-update')
    command(['sudo', 'apt-get', 'install', '-y', 'bubblewrap', 'build-essential', 'pkg-config', 'libssl-dev', 'apparmor', 'apparmor-profiles'], 'apt-tools')
    # Ubuntu ships the bwrap policy in the optional profiles package.
    # Load its exact packaged file; keep global userns restrictions enabled.
    command(['sudo', 'apparmor_parser', '-r',
             '/usr/share/apparmor/extra-profiles/bwrap-userns-restrict'], 'bwrap-apparmor-policy')
    # Only preinstalled SDKs on this disposable GitHub VM; never user/source paths.
    command(['sudo', 'rm', '-rf', '--', '/usr/share/dotnet', '/usr/local/lib/android', '/opt/ghc',
             '/usr/local/.ghcup'], 'runner-sdk-space')
    url = f"https://github.com/leanprover/elan/releases/download/{pins['elan_version']}/elan-x86_64-unknown-linux-gnu.tar.gz"
    command(['curl', '--fail', '--location', '--output', tools / 'elan.tar.gz', url], 'elan-download')
    if digest(tools / 'elan.tar.gz') != pins['elan_tar_sha256']:
        raise ValueError('elan archive checksum mismatch')
    command(['tar', '-xzf', tools / 'elan.tar.gz', '-C', tools], 'elan-unpack')
    env = dict(os.environ, ELAN_HOME=str(tools / 'elan'), LEAN_NUM_THREADS='4')
    command([tools / 'elan-init', '-y', '--no-modify-path', '--default-toolchain', 'none'], 'elan-install', env=env)
    command([tools / 'elan/bin/elan', 'toolchain', 'install', request['lean_toolchain']], 'lean-install', env=env)
    lean = toolchain_dir() / 'bin'
    if not (lean / 'lean').is_file():
        raise ValueError('reviewed toolchain layout is unavailable')
    env['PATH'] = str(lean) + ':' + env['PATH']
    clone('https://github.com/leanprover/comparator.git', pins['comparator'], tools / 'comparator', 'tool-comparator')
    exporter = tools / 'comparator/.lake/packages/lean4export'
    exporter.parent.mkdir(parents=True)
    clone('https://github.com/leanprover/lean4export.git', pins['lean4export'], exporter, 'tool-exporter')
    for folder in [tools / 'comparator', exporter]:
        (folder / 'lean-toolchain').write_text(request['lean_toolchain'] + '\n')
    command([lean / 'lake', 'build', 'lean4export', 'comparator'], 'build-comparator', tools / 'comparator', env)
    clone('https://github.com/ammkrn/nanoda_lib.git', pins['nanoda'], tools / 'nanoda', 'tool-nanoda')
    command(['cargo', 'build', '--release', '--locked', '-j', '2'], 'build-nanoda', tools / 'nanoda', env)
    clone('https://github.com/Zouuup/landrun.git', pins['landrun'], tools / 'landrun', 'tool-landrun')
    command(['go', 'build', '-o', str(tools / 'landrun/landrun'), 'cmd/landrun/main.go'], 'build-landrun', tools / 'landrun', env)
    cache = WORK / 'cache'; cache.mkdir()
    (cache / 'lakefile.toml').write_text(lakefile([], profile.get('manifest_file', 'profiles/lake-manifest.json')))
    (cache / 'lean-toolchain').write_text(request['lean_toolchain'] + '\n')
    shutil.copyfile(ROOT / profile.get('manifest_file', 'profiles/lake-manifest.json'), cache / 'lake-manifest.json')
    packages = cache / '.lake/packages'; packages.mkdir(parents=True)
    for item in json.loads((cache / 'lake-manifest.json').read_text())['packages']:
        clone(item['url'], item['rev'], packages / item['name'], 'dependency-' + item['name'])
    env['MATHLIB_CACHE_DIR'] = str(WORK / 'mathlib-downloads')
    command([lean / 'lake', 'exe', 'cache', 'get'], 'mathlib-cache', cache, env)
    inputs = {}
    for h in packages.glob('**/.lake/build/**/*.hash'):
        if not re.fullmatch('[0-9a-fA-F]{16}', h.read_text()):
            target = Path(str(h)[:-5])
            if target.is_file():
                inputs[target] = 'binary'
    lock = packages / 'proofwidgets/widget/package-lock.json'
    if lock.is_file(): inputs[lock] = 'text'
    hash_inputs = WORK / 'control/cache-hash-inputs.txt'
    hash_inputs.write_text(''.join(f'{kind}\t{path}\n' for path, kind in sorted(inputs.items())))
    command([lean / 'lean', '--run', ROOT / 'scripts/CacheHashes.lean', hash_inputs], 'cache-hash-metadata', ROOT, env)
    # The shim only serializes dependency chains; it uses the unchanged real Lake.
    bin_dir = WORK / 'control/bin'; bin_dir.mkdir()
    profile = json.loads((WORK / 'control/request.json').read_text())['profile']
    command(['cc', '-O2', '-Wall', '-Wextra',
             '-DREAL_LAKE=' + json.dumps(str(lean / 'lake')),
             '-DCONTROL=' + json.dumps(str(WORK / 'control')),
             '-DSOLUTION_MODULE=' + json.dumps(profile['solution_module']),
             ROOT / 'scripts/lake-shim.c', '-o', bin_dir / 'lake'], 'build-lake-adapter')
    shutil.copyfile(ROOT / 'scripts/inside.py', WORK / 'control/inside.py')
    binaries = {'lean': lean / 'lean', 'comparator': tools / 'comparator/.lake/build/bin/comparator',
                'lean4export': exporter / '.lake/build/bin/lean4export',
                'nanoda': tools / 'nanoda/target/release/nanoda_bin', 'landrun': tools / 'landrun/landrun'}
    write_json(ART / 'tool-sha256.json', {name: digest(path) for name, path in binaries.items()})
    # Compile only our Lake configuration before making its cache immutable.
    # `lean --version` elaborates no submission source. This stays offline.
    command(sandbox_args(config_write=True) + [str(lean / 'lake'), 'env', 'lean', '--version'],
            'trusted-lake-config')
    data = receipt(); data['tool_pins'] = pins; data['status'] = 'tools_ready'; save(data)


def toolchain_dir():
    request = json.loads((WORK / 'control/request.json').read_text())['request']
    return WORK / 'tools/elan/toolchains' / request['lean_toolchain'].replace('/', '--').replace(':', '---')


def sandbox_args(config_write=False):
    tools, stage, control = WORK / 'tools', WORK / 'stage', WORK / 'control'
    lean = toolchain_dir()
    args = ['/usr/bin/bwrap', '--unshare-all', '--die-with-parent', '--new-session',
            '--ro-bind', '/usr', '/usr', '--symlink', 'usr/bin', '/bin',
            '--symlink', 'usr/lib', '/lib', '--symlink', 'usr/lib64', '/lib64',
            '--ro-bind', '/etc/ld.so.cache', '/etc/ld.so.cache',
            '--proc', '/proc', '--dev', '/dev', '--ro-bind', str(stage), str(stage),
            '--bind', str(stage / '.lake/build'), str(stage / '.lake/build'),
            '--ro-bind', str(WORK / 'cache/.lake/packages'), str(stage / '.lake/packages'),
            '--ro-bind', str(tools), str(tools), '--ro-bind', str(control), str(control),
            '--bind', str(WORK / 'scratch'), '/tmp', '--chdir', str(stage), '--clearenv']
    if config_write:
        args += ['--bind', str(stage / '.lake/config'), str(stage / '.lake/config')]
    if Path('/etc/alternatives/which').exists():
        args += ['--ro-bind', '/etc/alternatives/which', '/etc/alternatives/which']
    env = {'PATH': f'{control}/bin:{lean}/bin:/usr/bin:/bin', 'HOME': '/tmp', 'TMPDIR': '/tmp',
           'LEAN_NUM_THREADS': '4', 'COMPARATOR_LANDRUN': str(tools / 'landrun/landrun'),
           'COMPARATOR_LEAN4EXPORT': str(tools / 'comparator/.lake/packages/lean4export/.lake/build/bin/lean4export'),
           'COMPARATOR_NANODA': str(tools / 'nanoda/target/release/nanoda_bin')}
    for k, v in env.items(): args += ['--setenv', k, v]
    return args


# Lean starts one more worker thread each time a pool task waits on another task (Task.get,
# IO.wait), with no upper bound (src/runtime/object.cpp, task_manager::wait_for). One large
# module can so need hundreds of threads: on 2026-10-21 PR #29 (one 1.8 MB module of 694
# decide theorems) failed with "failed to create thread" at TasksMax=512. MemoryMax still
# bounds the memory of these threads.
TASKS_MAX = 4096


def prepare_nanoda_swap():
    # Comparator retains its parsed proof while its external kernel runs.
    # Swap lets those idle pages leave RAM on the standard hosted runner.
    # This file is outside every submission mount and exists only on the VM.
    swap = WORK / 'nanoda.swap'
    if shutil.disk_usage(WORK).free < 20 * 1024**3:
        raise RuntimeError('nanoda swap needs at least 20 GiB free disk')
    command(['sudo', 'fallocate', '-l', '16G', swap], 'nanoda-swap-allocate')
    command(['sudo', 'chmod', '600', swap], 'nanoda-swap-permissions')
    command(['sudo', 'mkswap', swap], 'nanoda-swap-format')
    command(['sudo', 'swapon', swap], 'nanoda-swap-enable')


def sandbox_preflight():
    # Probe real namespace separation and read-only mounts before loading submission code.
    probe = '''import os, pathlib, sys
assert os.readlink('/proc/self/ns/net') != sys.argv[1]
assert os.readlink('/proc/self/ns/pid') != sys.argv[2]
assert not pathlib.Path(sys.argv[3]).exists()
assert not any(k.startswith(('GITHUB_', 'ACTIONS_')) for k in os.environ)
for path in sys.argv[4:]:
    try:
        open(path, 'ab').close()
    except PermissionError:
        continue
    except OSError as e:
        if e.errno == 30: continue
        raise
    raise AssertionError('read-only mount allowed a write')
print('Network/process namespaces, credential visibility, and read-only mounts passed')
'''
    command(sandbox_args() + ['/usr/bin/python3', '-c', probe,
            os.readlink('/proc/self/ns/net'), os.readlink('/proc/self/ns/pid'),
            str(ROOT / '.git/config'), str(WORK / 'stage/lakefile.toml'),
            str(WORK / 'stage/.lake/packages/mathlib/lean-toolchain')], 'sandbox-preflight')


def launch_github(kernel, command_args, deadline):
    """One systemd-run unit per stage with its own caps; returns exit code, unit result, guard stop, start, usage."""
    if kernel == 'nanoda':
        prepare_nanoda_swap()
    swap_limit = 16 * 1024**3 if kernel == 'nanoda' else 0
    unit = 'bos-verifier-' + kernel
    remaining = max(1, int(deadline - time.time()))
    args = ['sudo', 'systemd-run', '--wait', '--pipe', '--unit=' + unit,
            '--uid=' + str(os.getuid()), '--gid=' + str(os.getgid()),
            '--property=RestrictAddressFamilies=~AF_UNIX', '--property=Nice=10',
            '--property=CPUQuota=400%', '--property=MemoryMax=14G', '--property=MemorySwapMax=' + str(swap_limit),
            '--property=RuntimeMaxSec=' + str(remaining), '--property=TasksMax=' + str(TASKS_MAX), *command_args]
    print(f'{kernel}: isolated check started', flush=True)
    start, peak, swap_peak, tasks_peak, guard_stop = time.monotonic(), 0, 0, 0, None
    with (ART / f'{kernel}.log').open('w') as log:
        proc = subprocess.Popen(args, stdout=log, stderr=subprocess.STDOUT)
        while proc.poll() is None:
            memory = Path('/sys/fs/cgroup/system.slice') / (unit + '.service') / 'memory.peak'
            try: peak = max(peak, int(memory.read_text()))
            except (FileNotFoundError, ValueError): pass
            try: swap_peak = max(swap_peak, int(memory.with_name('memory.swap.current').read_text()))
            except (FileNotFoundError, ValueError): pass
            for name in ['pids.peak', 'pids.current']:
                try: tasks_peak = max(tasks_peak, int(memory.with_name(name).read_text()))
                except (FileNotFoundError, ValueError): pass
            if shutil.disk_usage(WORK).free < 1024**3:
                guard_stop = 'disk space below 1 GiB'
                subprocess.run(['sudo', 'systemctl', 'stop', unit], check=False, stdout=log, stderr=log)
            time.sleep(1)
        code = proc.wait()
    systemd_result = subprocess.run(['sudo', 'systemctl', 'show', unit, '--property=Result', '--value'],
                                     capture_output=True, text=True, check=False).stdout.strip()
    usage = {'sampled_peak_cgroup_bytes': peak, 'memory_limit_bytes': 14 * 1024**3,
             'sampled_peak_swap_bytes': swap_peak, 'swap_limit_bytes': swap_limit,
             'sampled_peak_tasks': tasks_peak, 'tasks_limit': TASKS_MAX}
    return code, systemd_result, guard_stop, start, usage


def verify(kernels=None):
    sandbox_preflight()
    # No submission elaboration has run before Comparator exports the trusted challenge.
    deadline = receipt()['started_unix'] + DEADLINE_SECONDS
    for kernel in kernels or ['lean', 'audit', 'nanoda']:
        data = receipt()
        if time.time() >= deadline:
            data['status'] = 'timeout'
            if kernel == 'nanoda':
                data['kernels']['nanoda'] = {'status': 'incomplete', 'reason': 'total_deadline'}
            save(data); return
        command_args = sandbox_args() + ['/usr/bin/python3', str(WORK / 'control/inside.py'), str(WORK), kernel]
        code, systemd_result, guard_stop, start, usage = launch_github(kernel, command_args, deadline)
        record = {'systemd_result': systemd_result, 'status': 'passed' if code == 0 else 'not_completed_or_rejected',
                  'exit_code': code, 'wall_seconds': round(time.monotonic() - start, 3),
                  **usage, 'guard_stop': guard_stop, 'log': kernel + '.log'}
        text = (ART / f'{kernel}.log').read_text(errors='replace')
        if kernel != 'audit':
            record.update(kernel_outcome(kernel, code, text, systemd_result, guard_stop))
            data = receipt(); data['kernels'][kernel] = record
        else:
            reported = {}
            for name in data['theorem_names']:
                hits = re.findall(re.escape("'" + name + "' depends on axioms: [") + r'([^\]]*)\]', text)
                if hits: reported[name] = [x.strip() for x in hits[-1].split(',') if x.strip()]
            record['reported_axioms'] = reported
            if code == 0 and (set(reported) != set(data['theorem_names']) or
                             any(set(v) - set(AXIOMS) for v in reported.values())):
                record['status'] = 'invalid_output'
            data = receipt(); data['axiom_audit'] = record
        save(data)
        print(f'{kernel}: {record["status"]}', flush=True)
        # A failed check never admits a theorem. Still try the independent audit.
        if guard_stop or systemd_result in ['oom-kill', 'timeout']:
            break
    data = receipt()
    data['status'] = ('passed' if all(v['status'] == 'passed' for v in data['kernels'].values())
                      and data['axiom_audit']['status'] == 'passed' else 'not_verified')
    save(data)


# Split build (docs/execution.md). Job 1 stops its build in time to pack and upload.
BUILD_PACK_SECONDS = 15 * 60
BUILD_ARTIFACT = ROOT / 'build-artifact'
BUILD_MAX_BYTES = 8 * 1024**3
BUILD_MAX_MEMBERS = 200_000
# Folders that hold the allowed paths. They are walked, but they are not members.
BUILD_PREFIXES = {'lib', 'lib/lean', 'ir'}
# Roots that would shadow the toolchain's own modules (docs/execution.md, LEAN_PATH order).
RESERVED_ROOTS = {'Init', 'Std', 'Lean', 'Lake'}


def build_roots(profile):
    roots = list(profile['source_roots']) + [r for dep in profile.get('solution_dependencies', []) for r in dep['source_roots']]
    for root in roots:
        if not NAME.fullmatch(root) or '.' in root or root in RESERVED_ROOTS or root.startswith('Verifier'):
            raise ValueError('source root cannot come from a build artifact')
    return roots


def build_allowed(rel, is_dir, roots):
    """Rule S1, shared by pack and unpack: only the solution's own build files in .lake/build.
    rel is a relative path with '/' separators."""
    try:
        rel.encode('utf-8')
    except UnicodeEncodeError:
        return False
    parts = rel.split('/')
    if '\0' in rel or any(x in ['', '.', '..'] for x in parts):
        return False
    if parts[:2] == ['lib', 'lean'] and len(parts) > 2:
        rest = parts[2:]
    elif parts[0] == 'ir' and len(parts) > 1:
        rest = parts[1:]
    else:
        return False
    if len(rest) == 1 and not is_dir:
        return any(rest[0].startswith(root + '.') and len(rest[0]) > len(root) + 1 for root in roots)
    return rest[0] in roots


def build():
    """Split job 1: one parallel Lake build of the solution in the sandbox. A failed or partial build is
    not fatal: pack keeps what exists, and job 2 continues or fails as one job would."""
    sandbox_preflight()
    deadline = receipt()['started_unix'] + DEADLINE_SECONDS - BUILD_PACK_SECONDS
    command_args = sandbox_args() + ['/usr/bin/python3', str(WORK / 'control/inside.py'), str(WORK), 'build']
    code, systemd_result, guard_stop, start, usage = launch_github('build', command_args, deadline)
    data = receipt()
    data['build'] = {'exit_code': code, 'systemd_result': systemd_result, 'wall_seconds': round(time.monotonic() - start, 3),
                     **usage, 'guard_stop': guard_stop, 'log': 'build.log'}
    save(data)
    print(f'build: exit {code}, {systemd_result}', flush=True)


def pack():
    """Split job 1, rule S2: trusted code writes a deterministic tar of the allowed build files after the build unit has ended.
    It never follows a symlink. The sha256 goes to the job output; job 2 checks it."""
    state = subprocess.run(['systemctl', 'is-active', 'bos-verifier-build'], capture_output=True, text=True, check=False).stdout.strip()
    if state not in ['inactive', 'failed']:
        raise RuntimeError('build unit is not stopped: ' + (state or 'unknown'))
    roots = build_roots(json.loads((WORK / 'control/request.json').read_text())['profile'])
    BUILD_ARTIFACT.mkdir(exist_ok=True)
    data = receipt()
    # Job 1's record and log go to job 2's receipt as data, also when the pack fails below.
    write_json(BUILD_ARTIFACT / 'build.json', {'build': data.get('build')})
    if (ART / 'build.log').is_file():
        shutil.copyfile(ART / 'build.log', BUILD_ARTIFACT / 'build.log')
    base = WORK / 'stage/.lake/build'
    if not stat.S_ISDIR(os.lstat(base).st_mode):
        raise RuntimeError('build folder is not a directory')
    members, skipped, total = [], [], 0
    for top, dirs, files in os.walk(base, followlinks=False):
        prefix = os.path.relpath(top, base)
        keep = []
        for name in dirs + files:
            rel = name if prefix == '.' else prefix + '/' + name
            st = os.lstat(os.path.join(top, name))
            is_dir = stat.S_ISDIR(st.st_mode)
            if is_dir and rel in BUILD_PREFIXES:
                keep.append(name)
            elif (is_dir or (stat.S_ISREG(st.st_mode) and st.st_nlink == 1)) and build_allowed(rel, is_dir, roots):
                members.append((rel, st))
                total += 0 if is_dir else st.st_size
                if is_dir:
                    keep.append(name)
            else:
                skipped.append(rel)
        dirs[:] = [d for d in dirs if d in keep]
        if len(members) > BUILD_MAX_MEMBERS or total > BUILD_MAX_BYTES:
            raise RuntimeError('build files exceed the pack caps')
    with tarfile.open(BUILD_ARTIFACT / 'build.tar', 'w', format=tarfile.PAX_FORMAT) as tar:
        for rel, st in sorted(members, key=lambda m: m[0]):
            info = tarfile.TarInfo(rel)
            info.uid = info.gid = 0
            info.uname = info.gname = ''
            # Keep the real mtime to the nanosecond: Lake can compare mtimes.
            ns = max(0, st.st_mtime_ns)
            info.mtime = ns // 10**9
            info.pax_headers = {'mtime': f'{ns // 10**9}.{ns % 10**9:09d}'}
            if stat.S_ISDIR(st.st_mode):
                info.type, info.mode = tarfile.DIRTYPE, 0o755
                tar.addfile(info)
                continue
            info.type, info.mode, info.size = tarfile.REGTYPE, 0o644, st.st_size
            with os.fdopen(os.open(base / rel, os.O_RDONLY | os.O_NOFOLLOW | os.O_CLOEXEC), 'rb') as f:
                now = os.fstat(f.fileno())
                if not stat.S_ISREG(now.st_mode) or (now.st_dev, now.st_ino, now.st_size) != (st.st_dev, st.st_ino, st.st_size):
                    raise RuntimeError('build file changed while packing')
                tar.addfile(info, f)
    sha = digest(BUILD_ARTIFACT / 'build.tar')
    data = receipt()
    data['pack'] = {'sha256': sha, 'members': len(members), 'files': sum(not stat.S_ISDIR(m[1].st_mode) for m in members),
                    'bytes': total, 'skipped_count': len(skipped), 'skipped_first': sorted(skipped)[:20]}
    save(data)
    write_json(BUILD_ARTIFACT / 'build.json', {'build': data.get('build'), 'pack': data['pack']})
    if os.environ.get('GITHUB_OUTPUT'):
        with open(os.environ['GITHUB_OUTPUT'], 'a') as out:
            out.write('build_sha256=' + sha + '\n')
    print(f"pack: {len(members)} members, {total} bytes, {len(skipped)} skipped, sha256 {sha}", flush=True)


def unpack():
    """Split job 2, rule S1: check job 1's tar against BOS_BUILD_SHA256, then restore only the allowed
    members into the empty build folder. Any other member refuses the whole archive."""
    data = receipt()
    record = BUILD_ARTIFACT / 'build.json'
    if record.is_file() and not record.is_symlink() and record.stat().st_size <= 64 * 1024:
        job1 = json.loads(record.read_text())
        data.update({k: job1[k] for k in ['build', 'pack'] if isinstance(job1, dict) and k in job1})
    # The site accepts at most 128 MB of receipt files; a larger log stays in job 1's artifact only.
    log = BUILD_ARTIFACT / 'build.log'
    if log.is_file() and not log.is_symlink() and log.stat().st_size <= 32 * 1024**2:
        shutil.copyfile(log, ART / 'build.log')
    save(data)
    if os.environ.get('BOS_BUILD_RESULT') != 'success':
        raise RuntimeError('build job did not succeed')
    expected = os.environ.get('BOS_BUILD_SHA256', '')
    if not re.fullmatch('[0-9a-f]{64}', expected):
        raise ValueError('BOS_BUILD_SHA256 must be 64 lowercase hex digits')
    path = BUILD_ARTIFACT / 'build.tar'
    if path.is_symlink() or not path.is_file() or digest(path) != expected:
        raise ValueError('build artifact is missing or its sha256 does not match')
    roots = build_roots(json.loads((WORK / 'control/request.json').read_text())['profile'])
    # Also refuse a root that names a module folder or file of the toolchain itself (fails if the folder is missing).
    toolchain = {name.split('.')[0] for name in os.listdir(toolchain_dir() / 'lib/lean')}
    if set(roots) & toolchain:
        raise ValueError('source root has the name of a toolchain module')
    base = WORK / 'stage/.lake/build'
    if not stat.S_ISDIR(os.lstat(base).st_mode) or os.listdir(base):
        raise RuntimeError('build folder is not the empty folder from prepare')
    # Record the LEAN_PATH that Lake gives Comparator, before any restored file exists.
    # Trusted: our Lake config only, no submission code.
    command(sandbox_args() + [str(toolchain_dir() / 'bin/lake'), 'env', 'printenv', 'LEAN_PATH'], 'lean-path')
    lines = (ART / 'lean-path.log').read_text(errors='replace').split()
    data = receipt(); data['lean_path'] = lines[-1].split(':') if lines else []; save(data)
    with tarfile.open(path, 'r:') as tar:
        checked, names, total = [], set(), 0
        for m in tar:
            mtime = re.fullmatch(r'([0-9]{1,12})\.([0-9]{9})', m.pax_headers.get('mtime', ''))
            if (m.type not in [tarfile.REGTYPE, tarfile.DIRTYPE] or set(m.pax_headers) - {'mtime', 'path'} or not mtime
                    or m.name in names or not build_allowed(m.name, m.isdir(), roots) or (m.isdir() and m.size)):
                raise ValueError('build artifact has a member outside the allow-list')
            names.add(m.name)
            total += m.size
            checked.append((m, int(mtime[1]) * 10**9 + int(mtime[2])))
            if len(checked) > BUILD_MAX_MEMBERS or total > BUILD_MAX_BYTES:
                raise ValueError('build artifact exceeds the pack caps')
        for prefix in sorted(BUILD_PREFIXES):
            os.mkdir(base / prefix, 0o755)
        dirs = []
        for m, ns in checked:
            if m.isdir():
                os.mkdir(base / m.name, 0o755); os.chmod(base / m.name, 0o755)
                dirs.append((base / m.name, ns))
                continue
            fd = os.open(base / m.name, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW | os.O_CLOEXEC, 0o644)
            with os.fdopen(fd, 'wb') as out, tar.extractfile(m) as src:
                shutil.copyfileobj(src, out, 1024 * 1024)
                out.flush(); os.fchmod(fd, 0o644); os.utime(fd, ns=(ns, ns))
        for folder, ns in reversed(dirs):
            os.utime(folder, ns=(ns, ns), follow_symlinks=False)
    path.unlink()  # Disk space for the checks and the nanoda swap.
    data = receipt()
    data['unpack'] = {'sha256': expected, 'members': len(checked), 'files': sum(not m.isdir() for m, _ in checked), 'bytes': total}
    save(data)


def verify_lean():
    verify(['lean', 'audit'])
    data = receipt()
    data['verification_stage'] = 'lean'
    data['kernels']['nanoda'] = {'status': 'pending', 'reason': 'advisory_queued'}
    save(data)


def verify_nanoda():
    verify(['nanoda'])
    data = receipt()
    data['verification_stage'] = 'final'
    save(data)


def finalize():
    ART.mkdir(exist_ok=True)
    if not (ART / 'receipt.json').exists():
        save({'schema_version': 1, 'status': 'setup_failed', 'steps': [], 'kernels': {}})
    data = receipt()
    stage = os.environ.get('BOS_RECEIPT_STAGE')
    if stage in ['lean', 'final']:
        data['verification_stage'] = stage
        if stage == 'lean' and data.get('kernels', {}).get('nanoda', {}).get('status') in [None, 'not_started']:
            data.setdefault('kernels', {})['nanoda'] = {'status': 'pending', 'reason': 'advisory_queued'}
    data['finished_unix'] = time.time()
    data['checked_at'] = datetime.fromtimestamp(data['finished_unix'], timezone.utc).isoformat().replace('+00:00', 'Z')
    if data.get('status') not in ['passed', 'not_verified', 'timeout']:
        data['status'] = 'setup_failed'
    data['total_wall_seconds'] = round(data['finished_unix'] - data.get('started_unix', data['finished_unix']), 3)
    data['theorems'] = {name: {
        'lean_kernel': data.get('kernels', {}).get('lean', {}).get('status', 'not_started'),
        'nanoda_kernel': data.get('kernels', {}).get('nanoda', {}).get('status', 'not_started'),
        'reported_axioms': data.get('axiom_audit', {}).get('reported_axioms', {}).get(name),
        'timing_group': 'shared theorem closure'} for name in data.get('theorem_names', [])}
    data['artifact_sha256'] = {p.name: digest(p) for p in ART.iterdir() if p.is_file() and p.name != 'receipt.json'}
    save(data)
    summary = [f'# Verifier result: {data["status"]}', '',
               f'Commit: `{data.get("request", {}).get("commit", "unknown")}`',
               f'Challenge: `{data.get("request", {}).get("challenge_file", "unknown")}`', '',
               '| Kernel | Result | Seconds | Sampled peak GiB |', '|---|---|---:|---:|']
    for name, result in data.get('kernels', {}).items():
        summary.append(f'| {name} | {result["status"]} | {result.get("wall_seconds", "—")} | {result.get("sampled_peak_cgroup_bytes", 0)/1024**3:.2f} |')
    summary += ['', 'Read the receipt and logs artifact for axiom output, provenance, and limits.',
                'A timeout, cancelled run, or incomplete kernel check is not a proof rejection.']
    if os.environ.get('GITHUB_STEP_SUMMARY'):
        with open(os.environ['GITHUB_STEP_SUMMARY'], 'a') as f: f.write('\n'.join(summary) + '\n')
    print(json.dumps({'status': data['status'], 'artifact': 'verifier-receipt-and-logs'}))


def main():
    parser = argparse.ArgumentParser(); parser.add_argument('phase', choices=['prepare', 'setup', 'build', 'pack', 'verify', 'unpack', 'verify_lean', 'verify_nanoda', 'finalize'])
    phase = parser.parse_args().phase
    try:
        globals()[phase]()
    except Exception as exc:
        if (ART / 'receipt.json').exists():
            data = receipt(); data['error'] = str(exc); save(data)
        print(f'{phase}: {exc}', file=sys.stderr); raise SystemExit(1)
    if phase == 'verify' and receipt()['status'] != 'passed': raise SystemExit(1)


if __name__ == '__main__': main()
