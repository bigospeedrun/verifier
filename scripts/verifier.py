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
import subprocess
import sys
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


def clone(url, sha, dest, label):
    dest.mkdir(parents=True)
    # No submodules, hooks, credential helper, or submission build commands.
    command(['git', 'init', dest], label + '-init')
    common = ['git', '-C', dest, '-c', 'core.hooksPath=/dev/null',
              '-c', 'credential.helper=', '-c', 'protocol.file.allow=never',
              '-c', 'filter.lfs.required=false', '-c', 'filter.lfs.smudge=', '-c', 'filter.lfs.process=']
    command(common + ['fetch', '--depth=1', url, sha], label + '-fetch')
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


def lakefile(roots, manifest_file='profiles/lake-manifest.json'):
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
    for name in roots:
        if not NAME.fullmatch(name):
            raise ValueError('invalid library name')
        result += f'\n[[lean_lib]]\nname = {json.dumps(name)}\n'
    return result


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
    clone(request['repo_url'], request['commit'], WORK / 'clone', 'submission')
    stage = WORK / 'stage'; stage.mkdir()
    tracked = subprocess.check_output(['git', '-C', WORK / 'clone', 'ls-tree', '-rz', 'HEAD'])
    hashes, total = {}, 0
    for entry in tracked.split(b'\0'):
        if not entry:
            continue
        meta, rawpath = entry.split(b'\t', 1); mode = meta.split()[0]
        source_rel = Path(rawpath.decode('utf-8'))
        rel = source_rel
        if request.get('source_subdir'):
            try:
                rel = source_rel.relative_to(request['source_subdir'])
            except ValueError:
                continue
        if not rel.parts or rel.parts[0].removesuffix('.lean') not in profile['source_roots'] or rel.suffix != '.lean':
            continue
        module = '.'.join(rel.with_suffix('').parts)
        if mode != b'100644' or not NAME.fullmatch(module):
            raise ValueError('only regular Lean source files with ordinary module names are admitted')
        source = WORK / 'clone' / source_rel
        if source.stat().st_size > 20_000_000:
            raise ValueError('individual Lean source exceeds 20 MB')
        total += source.stat().st_size
        if total > 150_000_000:
            raise ValueError('Lean source input exceeds 150 MB')
        target = stage / rel; target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target); hashes[str(rel)] = digest(target)
    write_json(ART / 'source-sha256.json', hashes)
    chains = plan_sources(stage, profile['solution_module'])
    write_json(WORK / 'control/chains.json', chains)
    (WORK / 'control/chain-targets.txt').write_text(''.join(chain[-1] + '\n' for chain in chains))
    if 'direct_submission' in request:
        from submissions import challenge_source
        (stage / 'VerifierChallenge.lean').write_text(challenge_source(request['direct_submission']))
    else:
        shutil.copyfile(ROOT / profile['challenge_file'], stage / 'VerifierChallenge.lean')
    data = receipt(); data['generated_challenge_sha256'] = digest(stage / 'VerifierChallenge.lean'); save(data)
    (stage / 'VerifierAudit.lean').write_text('import ' + profile['solution_module'] + '\n' +
                                           ''.join('#print axioms ' + n + '\n' for n in names))
    (stage / 'lakefile.toml').write_text(lakefile(profile['source_roots'] + ['VerifierChallenge', 'VerifierAudit'], profile.get('manifest_file', 'profiles/lake-manifest.json')))
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


def verify(kernels=None):
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
    # No submission elaboration has run before Comparator exports the trusted challenge.
    deadline = receipt()['started_unix'] + 320 * 60
    for kernel in kernels or ['lean', 'audit', 'nanoda']:
        data = receipt()
        if time.time() >= deadline:
            data['status'] = 'timeout'
            if kernel == 'nanoda':
                data['kernels']['nanoda'] = {'status': 'incomplete', 'reason': 'total_deadline'}
            save(data); return
        if kernel == 'nanoda':
            prepare_nanoda_swap()
        swap_limit = 16 * 1024**3 if kernel == 'nanoda' else 0
        unit = 'bos-verifier-' + kernel
        remaining = max(1, int(deadline - time.time()))
        command_args = sandbox_args() + ['/usr/bin/python3', str(WORK / 'control/inside.py'), str(WORK), kernel]
        args = ['sudo', 'systemd-run', '--wait', '--pipe', '--unit=' + unit,
                '--uid=' + str(os.getuid()), '--gid=' + str(os.getgid()),
                '--property=RestrictAddressFamilies=~AF_UNIX', '--property=Nice=10',
                '--property=CPUQuota=400%', '--property=MemoryMax=14G', '--property=MemorySwapMax=' + str(swap_limit),
                '--property=RuntimeMaxSec=' + str(remaining), '--property=TasksMax=512', *command_args]
        print(f'{kernel}: isolated check started', flush=True)
        start, peak, swap_peak, guard_stop = time.monotonic(), 0, 0, None
        with (ART / f'{kernel}.log').open('w') as log:
            proc = subprocess.Popen(args, stdout=log, stderr=subprocess.STDOUT)
            while proc.poll() is None:
                memory = Path('/sys/fs/cgroup/system.slice') / (unit + '.service') / 'memory.peak'
                try: peak = max(peak, int(memory.read_text()))
                except (FileNotFoundError, ValueError): pass
                try: swap_peak = max(swap_peak, int(memory.with_name('memory.swap.current').read_text()))
                except (FileNotFoundError, ValueError): pass
                if shutil.disk_usage(WORK).free < 1024**3:
                    guard_stop = 'disk space below 1 GiB'
                    subprocess.run(['sudo', 'systemctl', 'stop', unit], check=False, stdout=log, stderr=log)
                time.sleep(1)
            code = proc.wait()
        systemd_result = subprocess.run(['sudo', 'systemctl', 'show', unit, '--property=Result', '--value'],
                                         capture_output=True, text=True, check=False).stdout.strip()
        record = {'systemd_result': systemd_result, 'status': 'passed' if code == 0 else 'not_completed_or_rejected',
                  'exit_code': code, 'wall_seconds': round(time.monotonic() - start, 3),
                  'sampled_peak_cgroup_bytes': peak, 'memory_limit_bytes': 14 * 1024**3,
                  'sampled_peak_swap_bytes': swap_peak, 'swap_limit_bytes': swap_limit,
                  'guard_stop': guard_stop, 'log': kernel + '.log'}
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
    parser = argparse.ArgumentParser(); parser.add_argument('phase', choices=['prepare', 'setup', 'verify', 'verify_lean', 'verify_nanoda', 'finalize'])
    phase = parser.parse_args().phase
    try:
        globals()[phase]()
    except Exception as exc:
        if (ART / 'receipt.json').exists():
            data = receipt(); data['error'] = str(exc); save(data)
        print(f'{phase}: {exc}', file=sys.stderr); raise SystemExit(1)
    if phase == 'verify' and receipt()['status'] != 'passed': raise SystemExit(1)


if __name__ == '__main__': main()
