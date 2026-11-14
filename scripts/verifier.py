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
from verdicts import admission, kernel_outcome

ROOT = Path(__file__).resolve().parents[1]
ART = ROOT / 'artifacts'
WORK = Path(os.environ.get('RUNNER_TEMP', str(ROOT / '.work'))) / 'bos-verifier'
NAME = re.compile(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*\Z')
SHA = re.compile(r'[0-9a-f]{40}\Z')
AXIOMS = ['propext', 'Quot.sound', 'Classical.choice']
# Total check deadline from prepare, in each job. Every job has timeout-minutes 350; after the deadline, finalize and the
# uploads took about 10 s on #187 (run 43148643813: finalize 0-1 s, receipt uploads 2 s each) and the build pack and its
# upload about 2 min. Was 320 min; darkhipo proposed about 348 min on verifier#187 (task b1457f08, Lead: about 335).
DEADLINE_SECONDS = 335 * 60


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


def chain_targets(profile, chains, split):
    # Split run (BOS_SPLIT, the issue jobs of a split profile): job 1 built the solution, so the shim makes one Lake call
    # (docs/execution.md). A PR or maintainer run of a split profile has no build job and keeps the chains.
    if split:
        if profile.get('runner') != 'github-split':
            raise ValueError('a split run needs a split profile')
        return profile['solution_module'] + '\n'
    return ''.join(chain[-1] + '\n' for chain in chains)


# The Lean options that a solution dependency, or a profile for its submission roots (source_lean_options), may set:
# those of a reviewed upstream build (eth, integer factoring; maxSynthPendingDepth = 3 of Axiom Math's PrimeGapsLib,
# 2026-11-06). A new option needs review; Comparator and nanoda re-check every exported term in any case.
LEAN_OPTION_NAMES = {'autoImplicit', 'relaxedAutoImplicit', 'exponentiation.threshold', 'pp.unicode.fun', 'maxSynthPendingDepth'}
# A data file that a profile admits in the submission roots (source_data_suffixes): a regular file read by the
# submission's own build code (the prime gaps certificate JSON that Axiom Math's PrimeGapsCert reads with
# IO.FS.readFile), never built or run. Each path part is an ordinary name; the size cap is per file.
DATA_SUFFIXES = {'.json'}
DATA_PART = re.compile(r'[A-Za-z0-9_][A-Za-z0-9_.-]{0,127}')
DATA_MAX_BYTES = 1_000_000


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


def source_root_options(profile):
    """The Lean options of the profile's own submission roots (source_lean_options), merged with those of its
    solution dependencies. The profile is trusted; the submission cannot set an option."""
    dependencies = profile.get('solution_dependencies', [])
    options = dependency_root_options(dependencies, profile['source_roots'])
    if 'source_lean_options' in profile:
        lean_options(profile['source_lean_options'])
        for root in profile['source_roots']:
            options[root] = profile['source_lean_options']
    return options


def data_suffixes(profile):
    suffixes = profile.get('source_data_suffixes', [])
    if not isinstance(suffixes, list) or not set(suffixes) <= DATA_SUFFIXES:
        raise ValueError('source_data_suffixes must name reviewed data suffixes only')
    return set(suffixes)


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
    if 'lake_workers_start' in profile and (type(profile['lake_workers_start']) is not int
                                            or profile['lake_workers_start'] not in LAKE_WORKERS):
        raise ValueError('lake_workers_start must be one of the Lake worker counts')
    WORK.mkdir(parents=True, exist_ok=False)
    (WORK / 'control').mkdir(); (WORK / 'tools').mkdir()
    write_json(WORK / 'control/request.json', {'request': request, 'profile': profile, 'names': names})
    data.update(request=request, profile=profile, theorem_names=names)
    save(data)
    clone_options = {'sparse_paths': profile['sparse_paths']} if profile.get('sparse_paths') else {}
    clone(request['repo_url'], request['commit'], WORK / 'clone', 'submission', **clone_options)
    sources = [(WORK / 'clone', request.get('source_subdir', profile.get('source_subdir', '')),
                profile['source_roots'], profile.get('source_prefixes', []), data_suffixes(profile))]
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
        sources.append((location, dep.get('source_subdir', ''), dep['source_roots'], [], set()))
    data = receipt(); data['solution_dependencies'] = dependencies; save(data)
    stage = WORK / 'stage'; stage.mkdir()
    hashes, total = {}, 0
    for location, subdir, roots, prefixes, allowed in sources:
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
            if not rel.parts or rel.parts[0].removesuffix('.lean') not in roots or rel.suffix not in {'.lean'} | allowed:
                continue
            if prefixes and not any(rel.is_relative_to(prefix) for prefix in prefixes):
                continue
            source = location / source_rel
            if rel.suffix != '.lean':
                # A data file inside a submission root (source_data_suffixes), not a module: never built or run.
                if mode != b'100644' or len(rel.parts) < 2 or not all(DATA_PART.fullmatch(part) for part in rel.parts):
                    raise ValueError('only regular data files with ordinary names inside a source root are admitted')
                if source.stat().st_size > DATA_MAX_BYTES:
                    raise ValueError('individual data file exceeds 1 MB')
            else:
                module = '.'.join(rel.with_suffix('').parts)
                if mode != b'100644' or not NAME.fullmatch(module):
                    raise ValueError('only regular Lean source files with ordinary module names are admitted')
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
    (WORK / 'control/chain-targets.txt').write_text(chain_targets(profile, chains, os.environ.get('BOS_SPLIT') == 'true'))
    if 'direct_submission' in request:
        from submissions import challenge_source
        (stage / 'VerifierChallenge.lean').write_text(challenge_source(request['direct_submission']))
    else:
        shutil.copyfile(ROOT / profile['challenge_file'], stage / 'VerifierChallenge.lean')
    data = receipt(); data['generated_challenge_sha256'] = digest(stage / 'VerifierChallenge.lean'); save(data)
    (stage / 'VerifierAudit.lean').write_text('import ' + profile['solution_module'] + '\n' +
                                           ''.join('#print axioms ' + n + '\n' for n in names))
    (stage / 'lakefile.toml').write_text(lakefile(profile['source_roots'] + [root for dep in dependencies for root in dep['source_roots']] + ['VerifierChallenge', 'VerifierAudit'], profile.get('manifest_file', 'profiles/lake-manifest.json'), profile.get('auto_implicit', False), source_root_options(profile)))
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


def apply_exporter_patches(pins, exporter):
    """The reviewed lean4export patches of this tool file, in order (docs/execution.md, Patched lean4export). Each
    patch file must match its pinned sha256; `git apply --check` first, so a patch that does not fit stops setup."""
    for item in pins.get('lean4export_patches', []):
        patch = ROOT / item['file']
        if patch.parent != ROOT / 'patches' or digest(patch) != item['sha256']:
            raise ValueError(f'lean4export patch checksum mismatch: {item["file"]}')
        command(['git', '-C', exporter, 'apply', '--check', patch], 'tool-exporter-patch-check-' + patch.stem)
        command(['git', '-C', exporter, 'apply', patch], 'tool-exporter-patch-' + patch.stem)


def exporter_self_test(exporter, folder, lean, env):
    """tests/lean/NatTest.lean in a copy of the patched exporter source: the patched natVal print and parse must
    give the same results as Lean's own, and stay fast on a 1.9 M-digit value. Runs before any submission code."""
    shutil.copytree(exporter, folder, ignore=shutil.ignore_patterns('.lake', '.git'))
    shutil.copyfile(ROOT / 'tests/lean/NatTest.lean', folder / 'NatTest.lean')
    with (folder / 'lakefile.toml').open('a') as f:
        f.write('\n[[lean_exe]]\nname = "nattest"\nroot = "NatTest"\n')
    command([lean / 'lake', 'build', 'nattest'], 'build-nattest', folder, env)
    command([folder / '.lake/build/bin/nattest'], 'nattest', folder, env)


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
    apply_exporter_patches(pins, exporter)
    for folder in [tools / 'comparator', exporter]:
        (folder / 'lean-toolchain').write_text(request['lean_toolchain'] + '\n')
    command([lean / 'lake', 'build', 'lean4export', 'comparator'], 'build-comparator', tools / 'comparator', env)
    if pins.get('lean4export_patches'):
        exporter_self_test(exporter, tools / 'nattest', lean, env)
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

# Lake starts one Lean process per worker of its task pool, and LEAN_NUM_THREADS sets the size of that pool
# (Lean v4.34.1 src/runtime/object.cpp get_lean_num_threads; that Lake has no -j option). A Lean process
# ignores the variable (src/Lean/Shell.lean defaultNumThreads), so it only sets how many modules build at once.
# The 14G cap is for the whole unit: on verifier#182 four large modules at once hit it (oom-kill at Lake job
# 4214/6130, and again after 124 s when job 2 continued at 4). After an oom-kill during the build, the build
# continues in a new unit with the next count. Lake keeps each finished module.
LAKE_WORKERS = (4, 3, 2, 1)


def first_lake_workers(data):
    """The count that the last build attempt of this run used: the earlier stage of this job (lake_workers),
    else the build job before this one (build.attempts, restored by unpack). Else the profile's lake_workers_start
    (task b1457f08: darkhipo measured on verifier#187 that the 4, 3 and 2 worker attempts of Catalan 295 cost 85 min
    before 1 worker passed). Any other value starts at 4."""
    jobs = data.get('lake_workers')
    if jobs is None:
        build = data.get('build')
        attempts = build.get('attempts') if isinstance(build, dict) else None
        jobs = attempts[-1].get('lake_jobs') if isinstance(attempts, list) and attempts and isinstance(attempts[-1], dict) else None
    if jobs is None:
        profile = data.get('profile')
        jobs = profile.get('lake_workers_start') if isinstance(profile, dict) else None
    return jobs if type(jobs) is int and jobs in LAKE_WORKERS else LAKE_WORKERS[0]


def build_unfinished(text):
    """True when the log of one check shows fewer finished Lake chains (the shim's 'exit=0' lines) than chain targets."""
    targets = [line for line in (WORK / 'control/chain-targets.txt').read_text().splitlines() if line]
    return len(re.findall(r'^VERIFIER source chain \d+: exit=0 seconds=', text, re.M)) < len(targets)


SWAP_BYTES = 16 * 1024**3
SWAP_DIR = Path('/mnt')  # The runner's spare disk; tests point it elsewhere.


def kernel_swap_limit(kernel):
    """MemorySwapMax of a check unit. nanoda: Comparator retains its parsed proof while the external kernel runs.
    lean, in a split run only: the build is done in job 1, and the builtin replay of one large declaration can pass
    the 14G cap (task b1457f08, verifier#187: one declaration took RSS to 11.6 GB, unit peak 13.2 GB, 0.3 GB swap).
    Builds keep no swap, so an oom-kill during a build still restarts it with fewer Lake workers."""
    if kernel == 'nanoda' or (kernel == 'lean' and os.environ.get('BOS_SPLIT') == 'true'):
        return SWAP_BYTES
    return 0


class NoSwapDisk(RuntimeError):
    pass


def active_swaps():
    """The swap files and devices the kernel uses now (`swapon --show`)."""
    out = subprocess.run(['/usr/sbin/swapon', '--show=NAME', '--noheadings', '--raw'], capture_output=True, text=True, check=False)
    return {line.strip() for line in out.stdout.splitlines() if line.strip()}


def prepare_kernel_swap():
    # Swap lets idle pages leave RAM on the standard hosted runner. The file is outside every submission mount and
    # exists only on the VM: /mnt when it has room, else the work disk.
    active = active_swaps()
    for folder in [SWAP_DIR, WORK]:
        swap = folder / 'bos-kernel.swap'
        if str(swap) in active:
            return  # An earlier attempt or stage of this job made it.
        if swap.exists():
            # An earlier attempt stopped between fallocate and swapon: make the file again.
            command(['sudo', 'rm', '-f', '--', swap], 'kernel-swap-remove')
    folder = SWAP_DIR if SWAP_DIR.is_dir() and shutil.disk_usage(SWAP_DIR).free >= 20 * 1024**3 else WORK
    swap = folder / 'bos-kernel.swap'
    if shutil.disk_usage(folder).free < 20 * 1024**3:
        raise NoSwapDisk('kernel swap needs at least 20 GiB free disk')
    command(['sudo', 'fallocate', '-l', '16G', swap], 'kernel-swap-allocate')
    command(['sudo', 'chmod', '600', swap], 'kernel-swap-permissions')
    command(['sudo', 'mkswap', swap], 'kernel-swap-format')
    command(['sudo', 'swapon', swap], 'kernel-swap-enable')


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


def launch_github(kernel, command_args, deadline, log_mode='w'):
    """One systemd-run unit per stage with its own caps; returns exit code, unit result, guard stop, start, usage."""
    swap_limit = kernel_swap_limit(kernel)
    if swap_limit:
        try:
            prepare_kernel_swap()
        except NoSwapDisk:
            if kernel != 'lean':
                raise
            # The split Lean check ran without swap before 9ea7a5a; a small proof does not need it.
            print('kernel swap: not enough disk, lean runs without swap', flush=True)
            swap_limit = 0
    unit = 'bos-verifier-' + kernel
    remaining = max(1, int(deadline - time.time()))
    args = ['sudo', 'systemd-run', '--wait', '--pipe', '--unit=' + unit,
            '--uid=' + str(os.getuid()), '--gid=' + str(os.getgid()),
            '--property=RestrictAddressFamilies=~AF_UNIX', '--property=Nice=10',
            '--property=CPUQuota=400%', '--property=MemoryMax=14G', '--property=MemorySwapMax=' + str(swap_limit),
            '--property=RuntimeMaxSec=' + str(remaining), '--property=TasksMax=' + str(TASKS_MAX), *command_args]
    print(f'{kernel}: isolated check started', flush=True)
    start, peak, swap_peak, tasks_peak, guard_stop = time.monotonic(), 0, 0, 0, None
    with (ART / f'{kernel}.log').open(log_mode) as log:
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
        log = ART / f'{kernel}.log'
        if kernel == 'audit':
            code, systemd_result, guard_stop, start, usage = launch_github(kernel, command_args, deadline)
            text = log.read_text(errors='replace')
        else:
            # The shim reads the Lake worker count (lake-shim.c). Start at the count of the last build attempt.
            workers = LAKE_WORKERS[LAKE_WORKERS.index(first_lake_workers(data)):]
            attempts, offset = [], 0
            for jobs in workers:
                if attempts:
                    subprocess.run(['sudo', 'systemctl', 'reset-failed', 'bos-verifier-' + kernel], check=False,
                                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                    with log.open('a') as f:
                        f.write(f'VERIFIER {kernel}: oom-kill during the build, the check starts again with {jobs} Lake workers\n')
                    offset = log.stat().st_size
                (WORK / 'control/lake-workers.txt').write_text(f'{jobs}\n')
                code, systemd_result, guard_stop, start, usage = launch_github(kernel, command_args, deadline,
                                                                               'a' if attempts else 'w')
                with log.open('rb') as f:
                    f.seek(offset); text = f.read().decode(errors='replace')
                attempts.append({'lake_jobs': jobs, 'exit_code': code, 'systemd_result': systemd_result,
                                 'wall_seconds': round(time.monotonic() - start, 3), **usage, 'guard_stop': guard_stop})
                data = receipt(); data['lake_workers'] = jobs; save(data)
                if (systemd_result != 'oom-kill' or guard_stop or not build_unfinished(text)
                        or jobs == workers[-1] or time.time() >= deadline):
                    break
        record = {'systemd_result': systemd_result, 'status': 'passed' if code == 0 else 'not_completed_or_rejected',
                  'exit_code': code, 'wall_seconds': round(time.monotonic() - start, 3),
                  **usage, 'guard_stop': guard_stop, 'log': kernel + '.log'}
        if kernel != 'audit':
            # The outcome comes from the last attempt's part of the log only.
            record.update(kernel_outcome(kernel, code, text, systemd_result, guard_stop))
            record['attempts'] = attempts
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
# The pack is a tar stream compressed with zstd -3 (Lead, 2026-11-11, task b1457f08: ir/ travels in the pack, and the
# generated C compresses about 36x). BUILD_MAX_BYTES caps the compressed file (the artifact). BUILD_MAX_RAW_BYTES caps
# the sum of the member sizes, in pack and again in unpack, and the decompressed stream, so that a decompression bomb
# cannot fill the runner disk. The 3-SAT build is about 23 GB raw (20 GB of it ir/).
BUILD_PACK = 'build.tar.zst'
BUILD_MAX_BYTES = 8 * 1024**3
BUILD_MAX_RAW_BYTES = 40 * 1024**3
BUILD_MAX_MEMBERS = 200_000
# Tar headers and padding: at most three 512-byte blocks per member (pax header, header, last data block), and the end.
TAR_OVERHEAD_PER_MEMBER = 3 * 512
ZSTD_PACK = ['zstd', '-3', '-T4', '-q', '-c']
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
    attempts = []
    for jobs in LAKE_WORKERS[LAKE_WORKERS.index(first_lake_workers(receipt())):]:
        if attempts:
            if time.time() >= deadline:
                break
            # A failed transient unit stays loaded, and systemd-run refuses its name until it is reset.
            subprocess.run(['sudo', 'systemctl', 'reset-failed', 'bos-verifier-build'], check=False,
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            with (ART / 'build.log').open('a') as log:
                log.write(f'VERIFIER build: oom-kill, the build continues with {jobs} Lake workers\n')
        command_args = sandbox_args() + ['/usr/bin/python3', str(WORK / 'control/inside.py'), str(WORK), 'build', str(jobs)]
        code, systemd_result, guard_stop, start, usage = launch_github('build', command_args, deadline,
                                                                       'a' if attempts else 'w')
        attempts.append({'lake_jobs': jobs, 'exit_code': code, 'systemd_result': systemd_result,
                         'wall_seconds': round(time.monotonic() - start, 3), **usage, 'guard_stop': guard_stop})
        print(f'build: {jobs} Lake workers, exit {code}, {systemd_result}', flush=True)
        if systemd_result != 'oom-kill' or guard_stop:
            break
    # The top-level fields are those of the last attempt, with the total time and the highest samples.
    data = receipt()
    data['build'] = {**{k: v for k, v in attempts[-1].items() if k != 'lake_jobs'},
                     'wall_seconds': round(sum(a['wall_seconds'] for a in attempts), 3),
                     'sampled_peak_cgroup_bytes': max(a['sampled_peak_cgroup_bytes'] for a in attempts),
                     'sampled_peak_swap_bytes': max(a['sampled_peak_swap_bytes'] for a in attempts),
                     'sampled_peak_tasks': max(a['sampled_peak_tasks'] for a in attempts),
                     'log': 'build.log', 'attempts': attempts}
    save(data)


def pack():
    """Split job 1, rule S2: trusted code writes a deterministic tar of the allowed build files after the build unit has ended,
    compressed with zstd (BUILD_PACK). It never follows a symlink. The sha256 of the compressed file goes to the job output;
    job 2 checks it."""
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
        if len(members) > BUILD_MAX_MEMBERS or total > BUILD_MAX_RAW_BYTES:
            raise RuntimeError('build files exceed the pack caps')
    target = BUILD_ARTIFACT / BUILD_PACK
    try:
        with target.open('wb') as out:
            zstd = subprocess.Popen(ZSTD_PACK, stdin=subprocess.PIPE, stdout=out)
            try:
                write_pack(zstd.stdin, base, members)
            finally:
                zstd.stdin.close()
                code = zstd.wait()
        if code:
            raise RuntimeError(f'zstd failed with exit {code}')
        if target.stat().st_size > BUILD_MAX_BYTES:
            raise RuntimeError('the compressed pack exceeds BUILD_MAX_BYTES')
    except BaseException:
        target.unlink(missing_ok=True)
        raise
    sha = digest(target)
    data = receipt()
    data['pack'] = {'sha256': sha, 'members': len(members), 'files': sum(not stat.S_ISDIR(m[1].st_mode) for m in members),
                    'bytes': total, 'compressed_bytes': target.stat().st_size,
                    'skipped_count': len(skipped), 'skipped_first': sorted(skipped)[:20]}
    save(data)
    write_json(BUILD_ARTIFACT / 'build.json', {'build': data.get('build'), 'pack': data['pack']})
    if os.environ.get('GITHUB_OUTPUT'):
        with open(os.environ['GITHUB_OUTPUT'], 'a') as out:
            out.write('build_sha256=' + sha + '\n')
    print(f"pack: {len(members)} members, {total} bytes, {target.stat().st_size} compressed, {len(skipped)} skipped, sha256 {sha}", flush=True)


def write_pack(stream, base, members):
    """The tar stream of pack(): fixed owner, modes and order, the real mtime to the nanosecond."""
    with tarfile.open(fileobj=stream, mode='w|', format=tarfile.PAX_FORMAT) as tar:
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


def decompress(source, target, limit):
    """zstd -d of a pinned file into a new file, stopped when the output passes `limit` bytes (a decompression bomb)."""
    total = 0
    try:
        with target.open('xb') as out, subprocess.Popen(['zstd', '-d', '-q', '-c', '--', str(source)],
                                                        stdout=subprocess.PIPE) as zstd:
            try:
                for block in iter(lambda: zstd.stdout.read(1024 * 1024), b''):
                    total += len(block)
                    if total > limit:
                        raise ValueError('a pinned artifact decompresses to more than its size cap')
                    out.write(block)
            except BaseException:
                zstd.kill()
                raise
        if zstd.returncode:
            raise ValueError('a pinned artifact does not decompress')
    except BaseException:
        target.unlink(missing_ok=True)
        raise
    return total


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
    packed = BUILD_ARTIFACT / BUILD_PACK
    if packed.is_symlink() or not packed.is_file() or packed.stat().st_size > BUILD_MAX_BYTES or digest(packed) != expected:
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
    path = BUILD_ARTIFACT / 'build.tar'
    decompress(packed, path, BUILD_MAX_RAW_BYTES + BUILD_MAX_MEMBERS * TAR_OVERHEAD_PER_MEMBER + 20 * 512)
    packed.unlink()  # Disk space: the raw tar and the restored files exist at the same time below.
    try:
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
                if len(checked) > BUILD_MAX_MEMBERS or total > BUILD_MAX_RAW_BYTES:
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
    finally:
        path.unlink(missing_ok=True)  # Disk space for the checks and the kernel swap; also after a refusal.
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


def receipt_status(data):
    """The receipt's status comes from the verdict's own rule (verdicts.admission), so the receipt and the result say the
    same: before, a run whose advisory nanoda check did not finish said not_verified here and Lean Verified in the result
    (verifier#194, reported by darkhipo). blocked (a rejection or an unpermitted axiom) stays apart from not_verified.
    A setup failure keeps its status, and so does a timeout that the rule does not pass: the result comment and the
    site importer read both. check_summary gives each check's own outcome, with its reason."""
    checks = dict(data.get('kernels', {}))
    if 'axiom_audit' in data:
        checks = {'lean': checks.pop('lean', {}), 'axiom_audit': data['axiom_audit'], **checks}
    data['check_summary'] = {name: str(c.get('status', 'not_started')) + (f" ({c['reason']})" if c.get('reason') else '')
                             for name, c in checks.items() if isinstance(c, dict)}
    data.pop('status_reason', None)
    names = data.get('theorem_names') or []
    if data.get('status') == 'setup_failed' or not names:
        return
    status, reason = admission(data, names)
    if data.get('status') == 'timeout' and status != 'passed':
        return
    data['status'], data['status_reason'] = status, reason


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
    # blocked and pending_review come from an earlier finalize (the split run's Lean stage).
    if data.get('status') not in ['passed', 'not_verified', 'blocked', 'pending_review', 'timeout']:
        data['status'] = 'setup_failed'
    data['total_wall_seconds'] = round(data['finished_unix'] - data.get('started_unix', data['finished_unix']), 3)
    data['theorems'] = {name: {
        'lean_kernel': data.get('kernels', {}).get('lean', {}).get('status', 'not_started'),
        'nanoda_kernel': data.get('kernels', {}).get('nanoda', {}).get('status', 'not_started'),
        'reported_axioms': data.get('axiom_audit', {}).get('reported_axioms', {}).get(name),
        'timing_group': 'shared theorem closure'} for name in data.get('theorem_names', [])}
    receipt_status(data)
    data['artifact_sha256'] = {p.name: digest(p) for p in ART.iterdir() if p.is_file() and p.name != 'receipt.json'}
    save(data)
    summary = [f'# Verifier result: {data["status"]}', '',
               *([f'Reason: `{data["status_reason"]}`', ''] if data.get('status_reason') else []),
               *[f'- {name}: {outcome}' for name, outcome in data.get('check_summary', {}).items()], '',
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
