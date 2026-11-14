"""Pins of the GitHub job's exact host commands: the bwrap sandbox, the systemd-run unit per stage and the setup steps.
The split build (docs/execution.md) must not change them. Ported from the desktop-path branch (b76a86d)."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch, Mock

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import verifier as v

TC = 'leanprover--lean4---v4.34.1'
ACCEPT = 'Lean default kernel accepts the solution\nYour solution is okay!\nnanoda kernel accepts the solution\n'


class Base(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory(); self.addCleanup(tmp.cleanup)
        self.work, self.art = Path(tmp.name) / 'bos-verifier', Path(tmp.name) / 'artifacts'
        for target, value in [('WORK', self.work), ('ART', self.art), ('SWAP_DIR', Path(tmp.name) / 'mnt')]:
            p = patch.object(v, target, value); p.start(); self.addCleanup(p.stop)
        # These pins are for a one-job run; the split lean stage's swap has its own test.
        p = patch.dict(os.environ); p.start(); self.addCleanup(p.stop); os.environ.pop('BOS_SPLIT', None)
        self.active = set()  # Swap files that `swapon --show` lists, for run_verify.
        profile = json.loads((ROOT / 'profiles/direct.json').read_text())['dft']
        (self.work / 'control').mkdir(parents=True); (self.work / 'tools').mkdir()
        v.write_json(self.work / 'control/request.json', {'request': {'lean_toolchain': 'leanprover/lean4:v4.34.1'},
                                                          'profile': profile, 'names': ['Race.bound']})
        self.art.mkdir()
        v.save({'started_unix': 1000.0, 'steps': [], 'theorem_names': ['Race.bound'],
                'kernels': {'lean': {'status': 'not_started'}, 'nanoda': {'status': 'not_started'}},
                'axiom_audit': {'status': 'not_started'}})

    def sandbox(self, config_write=False):
        W = str(self.work)
        args = ['/usr/bin/bwrap', '--unshare-all', '--die-with-parent', '--new-session',
                '--ro-bind', '/usr', '/usr', '--symlink', 'usr/bin', '/bin',
                '--symlink', 'usr/lib', '/lib', '--symlink', 'usr/lib64', '/lib64',
                '--ro-bind', '/etc/ld.so.cache', '/etc/ld.so.cache',
                '--proc', '/proc', '--dev', '/dev', '--ro-bind', f'{W}/stage', f'{W}/stage',
                '--bind', f'{W}/stage/.lake/build', f'{W}/stage/.lake/build',
                '--ro-bind', f'{W}/cache/.lake/packages', f'{W}/stage/.lake/packages',
                '--ro-bind', f'{W}/tools', f'{W}/tools', '--ro-bind', f'{W}/control', f'{W}/control',
                '--bind', f'{W}/scratch', '/tmp', '--chdir', f'{W}/stage', '--clearenv']
        if config_write:
            args += ['--bind', f'{W}/stage/.lake/config', f'{W}/stage/.lake/config']
        if Path('/etc/alternatives/which').exists():
            args += ['--ro-bind', '/etc/alternatives/which', '/etc/alternatives/which']
        for k, value in [('PATH', f'{W}/control/bin:{W}/tools/elan/toolchains/{TC}/bin:/usr/bin:/bin'), ('HOME', '/tmp'),
                         ('TMPDIR', '/tmp'), ('LEAN_NUM_THREADS', '4'), ('COMPARATOR_LANDRUN', f'{W}/tools/landrun/landrun'),
                         ('COMPARATOR_LEAN4EXPORT', f'{W}/tools/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export'),
                         ('COMPARATOR_NANODA', f'{W}/tools/nanoda/target/release/nanoda_bin')]:
            args += ['--setenv', k, value]
        return args


class SandboxPinTests(Base):
    def test_sandbox_args_are_unchanged(self):
        self.assertEqual(v.sandbox_args(), self.sandbox())
        self.assertEqual(v.sandbox_args(config_write=True), self.sandbox(config_write=True))


class VerifyPinTests(Base):
    def test_each_stage_runs_in_the_same_systemd_unit(self):
        launched, runs, commands = [], [], []

        def popen(args, stdout=None, stderr=None, **kwargs):
            launched.append(args); stdout.write(ACCEPT); stdout.flush()
            return Mock(poll=Mock(return_value=0), wait=Mock(return_value=0))

        def run(args, **kwargs):
            runs.append(args)
            return Mock(stdout='success\n', returncode=0)

        with patch.object(v.subprocess, 'Popen', side_effect=popen), patch.object(v.subprocess, 'run', side_effect=run), \
             patch.object(v, 'command', side_effect=lambda args, label, *a, **k: commands.append((label, [str(x) for x in args]))), \
             patch.object(v, 'active_swaps', return_value=set()), \
             patch.object(v.time, 'time', return_value=1000.0), patch.object(v.shutil, 'disk_usage', return_value=Mock(free=100 * 1024**3)):
            v.verify(['lean', 'audit', 'nanoda'])
        W, uid, gid = str(self.work), str(os.getuid()), str(os.getgid())
        swap = str(self.work / 'bos-kernel.swap')
        self.assertEqual([c[0] for c in commands], ['sandbox-preflight', 'kernel-swap-allocate', 'kernel-swap-permissions',
                                                    'kernel-swap-format', 'kernel-swap-enable'])
        self.assertEqual(commands[0][1][:len(self.sandbox()) + 2], self.sandbox() + ['/usr/bin/python3', '-c'])
        self.assertEqual(commands[1:], [('kernel-swap-allocate', ['sudo', 'fallocate', '-l', '16G', swap]),
                                        ('kernel-swap-permissions', ['sudo', 'chmod', '600', swap]),
                                        ('kernel-swap-format', ['sudo', 'mkswap', swap]),
                                        ('kernel-swap-enable', ['sudo', 'swapon', swap])])
        for args, kernel, swap_limit in zip(launched, ['lean', 'audit', 'nanoda'], ['0', '0', str(16 * 1024**3)]):
            self.assertEqual(args, ['sudo', 'systemd-run', '--wait', '--pipe', '--unit=bos-verifier-' + kernel,
                                    '--uid=' + uid, '--gid=' + gid,
                                    '--property=RestrictAddressFamilies=~AF_UNIX', '--property=Nice=10',
                                    '--property=CPUQuota=400%', '--property=MemoryMax=14G', '--property=MemorySwapMax=' + swap_limit,
                                    '--property=RuntimeMaxSec=20100', '--property=TasksMax=4096',
                                    *self.sandbox(), '/usr/bin/python3', f'{W}/control/inside.py', W, kernel])
        self.assertEqual(runs, [['sudo', 'systemctl', 'show', 'bos-verifier-' + k, '--property=Result', '--value']
                                for k in ['lean', 'audit', 'nanoda']])
        data = v.receipt()
        self.assertEqual(data['kernels']['lean'], {
            'systemd_result': 'success', 'status': 'passed', 'reason': 'comparator_acceptance', 'exit_code': 0,
            'wall_seconds': data['kernels']['lean']['wall_seconds'], 'sampled_peak_cgroup_bytes': 0,
            'memory_limit_bytes': 14 * 1024**3, 'sampled_peak_swap_bytes': 0, 'swap_limit_bytes': 0,
            'sampled_peak_tasks': 0, 'tasks_limit': 4096, 'guard_stop': None, 'log': 'lean.log',
            'attempts': [{'lake_jobs': 4, 'exit_code': 0, 'systemd_result': 'success',
                          'wall_seconds': data['kernels']['lean']['attempts'][0]['wall_seconds'], 'sampled_peak_cgroup_bytes': 0,
                          'memory_limit_bytes': 14 * 1024**3, 'sampled_peak_swap_bytes': 0, 'swap_limit_bytes': 0,
                          'sampled_peak_tasks': 0, 'tasks_limit': 4096, 'guard_stop': None}]})
        self.assertEqual(data['kernels']['nanoda']['swap_limit_bytes'], 16 * 1024**3)
        self.assertEqual((self.work / 'control/lake-workers.txt').read_text(), '4\n')
        self.assertEqual(data['axiom_audit']['status'], 'invalid_output')  # The fixture log prints no axioms.

    def test_the_lean_stage_of_a_split_run_gets_the_kernel_swap(self):
        os.environ['BOS_SPLIT'] = 'true'
        self.assertEqual([v.kernel_swap_limit(k) for k in ['lean', 'audit', 'nanoda']], [16 * 1024**3, 0, 16 * 1024**3])
        os.environ['BOS_SPLIT'] = 'false'
        self.assertEqual([v.kernel_swap_limit(k) for k in ['lean', 'audit', 'nanoda']], [0, 0, 16 * 1024**3])
        os.environ['BOS_SPLIT'] = 'true'
        launched, calls = self.run_verify(['lean', 'audit', 'nanoda'], [(ACCEPT, 'success'), ('', 'success'), (ACCEPT, 'success')])
        # One swap file for the job, made before the lean stage; /mnt is used when it has room.
        self.assertEqual([c for c in calls if isinstance(c, str) and c.startswith('kernel-swap')],
                         ['kernel-swap-allocate', 'kernel-swap-permissions', 'kernel-swap-format', 'kernel-swap-enable'])
        self.assertEqual(v.receipt()['kernels']['lean']['swap_limit_bytes'], 16 * 1024**3)
        self.assertTrue((self.work / 'bos-kernel.swap').exists())
        # A later stage of the same job reuses the active file, also when /mnt has room now.
        (v.SWAP_DIR).mkdir()
        _, calls = self.run_verify(['nanoda'], [(ACCEPT, 'success')])
        self.assertFalse([c for c in calls if isinstance(c, str) and c.startswith('kernel-swap')])
        # A file that swapon does not list (an attempt stopped before swapon) is made again, on /mnt now.
        self.active.clear()
        _, calls = self.run_verify(['nanoda'], [(ACCEPT, 'success')])
        self.assertEqual([c for c in calls if isinstance(c, str) and c.startswith('kernel-swap')],
                         ['kernel-swap-remove', 'kernel-swap-allocate', 'kernel-swap-permissions', 'kernel-swap-format',
                          'kernel-swap-enable'])
        self.assertFalse((self.work / 'bos-kernel.swap').exists())
        self.assertTrue((v.SWAP_DIR / 'bos-kernel.swap').exists())

    def test_without_swap_disk_the_split_lean_check_runs_without_swap_and_nanoda_stops(self):
        os.environ['BOS_SPLIT'] = 'true'
        with patch.object(v.shutil, 'disk_usage', return_value=Mock(free=5 * 1024**3)), \
             patch.object(v.subprocess, 'Popen', side_effect=lambda args, stdout=None, **k: (stdout.write(ACCEPT), stdout.flush(),
                          Mock(poll=Mock(return_value=0), wait=Mock(return_value=0)))[2]), \
             patch.object(v.subprocess, 'run', return_value=Mock(stdout='success\n', returncode=0)), \
             patch.object(v, 'command'), patch.object(v, 'active_swaps', return_value=set()), \
             patch.object(v.time, 'time', return_value=1000.0), patch('builtins.print') as printed:
            v.verify(['lean'])
            printed.assert_any_call('kernel swap: not enough disk, lean runs without swap', flush=True)
            self.assertEqual(v.receipt()['kernels']['lean']['swap_limit_bytes'], 0)
            self.assertEqual(v.receipt()['kernels']['lean']['status'], 'passed')
            with self.assertRaises(v.NoSwapDisk):
                v.verify(['nanoda'])

    def run_verify(self, kernels, outputs):
        """v.verify() with one (log text, systemd result) per launch; returns (unit, Lake workers) per launch and the systemctl calls."""
        launched, runs, outputs = [], [], list(outputs)
        (self.work / 'control/chain-targets.txt').write_text('Submission\n')

        def popen(args, stdout=None, stderr=None, **kwargs):
            text, result = outputs.pop(0)
            launched.append((args[4].removeprefix('--unit='), (self.work / 'control/lake-workers.txt').read_text().strip()))
            runs.append(result); stdout.write(text); stdout.flush()
            return Mock(poll=Mock(return_value=0), wait=Mock(return_value=0 if result == 'success' else 1))

        def run(args, **kwargs):
            if args[2] == 'show':
                return Mock(stdout=runs.pop(0) + '\n', returncode=0)
            calls.append(args); return Mock(stdout='', returncode=0)

        def command(args, label, *a, **k):
            calls.append(label)
            if label == 'kernel-swap-allocate':
                Path(args[-1]).touch()
            if label == 'kernel-swap-enable':
                self.active.add(str(args[-1]))
            if label == 'kernel-swap-remove':
                Path(args[-1]).unlink()

        calls = []
        with patch.object(v.subprocess, 'Popen', side_effect=popen), patch.object(v.subprocess, 'run', side_effect=run), \
             patch.object(v, 'command', side_effect=command), patch.object(v, 'active_swaps', side_effect=lambda: set(self.active)), \
             patch.object(v.time, 'time', return_value=1000.0), patch.object(v.shutil, 'disk_usage', return_value=Mock(free=100 * 1024**3)):
            v.verify(kernels)
        return launched, calls

    def test_an_oom_kill_during_the_build_starts_the_check_again_with_fewer_lake_workers(self):
        building = '✔ [10/20] Built Submission.A\n'
        done = 'VERIFIER source chain 0: exit=0 seconds=9.000\n'
        launched, calls = self.run_verify(['lean'], [(building, 'oom-kill'), (building, 'oom-kill'), (done + ACCEPT, 'success')])
        self.assertEqual(launched, [('bos-verifier-lean', '4'), ('bos-verifier-lean', '3'), ('bos-verifier-lean', '2')])
        reset = ['sudo', 'systemctl', 'reset-failed', 'bos-verifier-lean']
        self.assertEqual(calls, ['sandbox-preflight', reset, reset])
        lean = v.receipt()['kernels']['lean']
        self.assertEqual((lean['status'], lean['reason']), ('passed', 'comparator_acceptance'))
        self.assertEqual([(a['lake_jobs'], a['systemd_result']) for a in lean['attempts']], [(4, 'oom-kill'), (3, 'oom-kill'), (2, 'success')])
        self.assertEqual(v.receipt()['lake_workers'], 2)
        self.assertIn('VERIFIER lean: oom-kill during the build, the check starts again with 3 Lake workers\n',
                      (self.art / 'lean.log').read_text())
        # The outcome reads only the last attempt: an oom-kill and then a source error is a rejection.
        error = 'error: Submission/A.lean:1:2: unsolved goals\nerror: build failed\n'
        self.run_verify(['lean'], [(building, 'oom-kill'), (error, 'exit-code')])
        self.assertEqual(v.receipt()['kernels']['lean']['reason'], 'lean_compile_error')

    def test_no_new_attempt_after_the_build_finished_or_at_one_worker(self):
        done = 'VERIFIER source chain 0: exit=0 seconds=9.000\n'
        launched, _ = self.run_verify(['lean'], [(done, 'oom-kill')])
        self.assertEqual(launched, [('bos-verifier-lean', '4')])
        self.assertEqual(v.receipt()['kernels']['lean']['reason'], 'out_of_memory')
        data = v.receipt(); data['lake_workers'] = 1; v.save(data)
        launched, _ = self.run_verify(['lean'], [('', 'oom-kill')])
        self.assertEqual(launched, [('bos-verifier-lean', '1')])

    def test_job_2_starts_at_the_last_count_of_job_1_and_nanoda_at_that_of_lean(self):
        data = v.receipt()
        data['build'] = {'systemd_result': 'success', 'attempts': [{'lake_jobs': 4, 'systemd_result': 'oom-kill'},
                                                                 {'lake_jobs': 2, 'systemd_result': 'success'}]}
        v.save(data)
        building = '✔ [10/20] Built Submission.A\n'
        launched, calls = self.run_verify(['lean', 'audit'], [(building, 'oom-kill'), (ACCEPT, 'success'), ('', 'success')])
        self.assertEqual(launched, [('bos-verifier-lean', '2'), ('bos-verifier-lean', '1'), ('bos-verifier-audit', '1')])
        launched, calls = self.run_verify(['nanoda'], [(building, 'oom-kill')])
        self.assertEqual(launched, [('bos-verifier-nanoda', '1')])
        # Swap is made once per job, also when the check starts again.
        data = v.receipt(); data['lake_workers'] = 2; v.save(data)
        (self.work / 'bos-kernel.swap').unlink(); self.active.clear()  # A new job: no swap yet.
        launched, calls = self.run_verify(['nanoda'], [(building, 'oom-kill'), (ACCEPT, 'success')])
        self.assertEqual(launched, [('bos-verifier-nanoda', '2'), ('bos-verifier-nanoda', '1')])
        self.assertEqual([c for c in calls if isinstance(c, str) and c.startswith('kernel-swap')],
                         ['kernel-swap-allocate', 'kernel-swap-permissions', 'kernel-swap-format', 'kernel-swap-enable'])

    def test_a_bad_count_from_the_build_record_starts_at_4(self):
        for value in [None, 0, 5, '2', True, 2.0]:
            data = v.receipt(); data.pop('lake_workers', None)
            data['build'] = {'attempts': [{'lake_jobs': value}]}; v.save(data)
            self.assertEqual(v.first_lake_workers(v.receipt()), 4)
        for build in [None, [], {'attempts': []}, {'attempts': 'x'}, {'attempts': ['x']}]:
            self.assertEqual(v.first_lake_workers({'build': build}), 4)
        self.assertEqual(v.first_lake_workers({'lake_workers': 3, 'build': {'attempts': [{'lake_jobs': 1}]}}), 3)

    def test_the_profile_gives_the_first_count_when_no_attempt_did(self):
        catalan = json.loads((ROOT / 'profiles/direct.json').read_text())['catalan']
        self.assertEqual(catalan['lake_workers_start'], 1)
        self.assertEqual(v.first_lake_workers({'profile': catalan}), 1)
        self.assertEqual(v.first_lake_workers({'profile': {'lake_workers_start': 2}}), 2)
        # An attempt of this run comes first; a bad profile value starts at 4.
        self.assertEqual(v.first_lake_workers({'profile': catalan, 'build': {'attempts': [{'lake_jobs': 3}]}}), 3)
        self.assertEqual(v.first_lake_workers({'profile': catalan, 'lake_workers': 2}), 2)
        for value in [0, 5, '2', True, None]:
            self.assertEqual(v.first_lake_workers({'profile': {'lake_workers_start': value}}), 4)

    def test_the_deadline_is_335_minutes_on_github(self):
        self.assertEqual(v.DEADLINE_SECONDS, 335 * 60)
        with patch.object(v, 'command'), patch.object(v.time, 'time', return_value=1000.0 + 335 * 60):
            v.verify(['lean', 'audit', 'nanoda'])
        self.assertEqual(v.receipt()['status'], 'timeout')
        self.assertEqual(v.receipt()['kernels']['lean'], {'status': 'not_started'})


class SetupPinTests(Base):
    def test_setup_runs_the_same_steps(self):
        steps = []
        pins = json.loads((ROOT / 'profiles/tools.json').read_text())

        def command(args, label, cwd=None, env=None):
            keep = {k: env[k] for k in ['ELAN_HOME', 'LEAN_NUM_THREADS', 'MATHLIB_CACHE_DIR'] if env and k in env}
            if env: keep['PATH0'] = env['PATH'].split(':')[0]
            steps.append((label, [str(x) for x in args], str(cwd) if cwd else None, keep))

        def clone(url, sha, dest, label, sparse_paths=None):
            dest.mkdir(parents=True); steps.append(('clone', url, sha, str(dest), label))

        lean = self.work / 'tools/elan/toolchains' / TC / 'bin'
        lean.mkdir(parents=True); (lean / 'lean').write_text('')
        with patch.object(v, 'command', side_effect=command), patch.object(v, 'clone', side_effect=clone), \
             patch.object(v, 'digest', side_effect=lambda p: pins['elan_tar_sha256'] if p.name == 'elan.tar.gz' else
                          {ROOT / x['file']: x['sha256'] for x in pins['lean4export_patches']}.get(p, 'h')):
            v.setup()
        W, T, L = str(self.work), str(self.work / 'tools'), str(lean)
        env = {'ELAN_HOME': f'{T}/elan', 'LEAN_NUM_THREADS': '4'}
        built = dict(env, PATH0=L)
        manifest = json.loads((ROOT / 'profiles/lake-manifest.json').read_text())['packages']
        url = f"https://github.com/leanprover/elan/releases/download/{pins['elan_version']}/elan-x86_64-unknown-linux-gnu.tar.gz"
        expected = [
            ('apt-update', ['sudo', 'apt-get', 'update'], None, {}),
            ('apt-tools', ['sudo', 'apt-get', 'install', '-y', 'bubblewrap', 'build-essential', 'pkg-config', 'libssl-dev', 'apparmor', 'apparmor-profiles'], None, {}),
            ('bwrap-apparmor-policy', ['sudo', 'apparmor_parser', '-r', '/usr/share/apparmor/extra-profiles/bwrap-userns-restrict'], None, {}),
            ('runner-sdk-space', ['sudo', 'rm', '-rf', '--', '/usr/share/dotnet', '/usr/local/lib/android', '/opt/ghc', '/usr/local/.ghcup'], None, {}),
            ('elan-download', ['curl', '--fail', '--location', '--output', f'{T}/elan.tar.gz', url], None, {}),
            ('elan-unpack', ['tar', '-xzf', f'{T}/elan.tar.gz', '-C', T], None, {}),
            ('elan-install', [f'{T}/elan-init', '-y', '--no-modify-path', '--default-toolchain', 'none'], None, dict(env, PATH0=os.environ['PATH'].split(':')[0])),
            ('lean-install', [f'{T}/elan/bin/elan', 'toolchain', 'install', 'leanprover/lean4:v4.34.1'], None, dict(env, PATH0=os.environ['PATH'].split(':')[0])),
            ('clone', 'https://github.com/leanprover/comparator.git', pins['comparator'], f'{T}/comparator', 'tool-comparator'),
            ('clone', 'https://github.com/leanprover/lean4export.git', pins['lean4export'], f'{T}/comparator/.lake/packages/lean4export', 'tool-exporter'),
            *[step for name in ['lean4export-pr52-natlit-print', 'lean4export-natlit-parse'] for step in [
                ('tool-exporter-patch-check-' + name, ['git', '-C', f'{T}/comparator/.lake/packages/lean4export', 'apply', '--check', str(ROOT / f'patches/{name}.patch')], None, {}),
                ('tool-exporter-patch-' + name, ['git', '-C', f'{T}/comparator/.lake/packages/lean4export', 'apply', str(ROOT / f'patches/{name}.patch')], None, {})]],
            ('build-comparator', [f'{L}/lake', 'build', 'lean4export', 'comparator'], f'{T}/comparator', built),
            ('build-nattest', [f'{L}/lake', 'build', 'nattest'], f'{T}/nattest', built),
            ('nattest', [f'{T}/nattest/.lake/build/bin/nattest'], f'{T}/nattest', built),
            ('clone', 'https://github.com/ammkrn/nanoda_lib.git', pins['nanoda'], f'{T}/nanoda', 'tool-nanoda'),
            ('build-nanoda', ['cargo', 'build', '--release', '--locked', '-j', '2'], f'{T}/nanoda', built),
            ('clone', 'https://github.com/Zouuup/landrun.git', pins['landrun'], f'{T}/landrun', 'tool-landrun'),
            ('build-landrun', ['go', 'build', '-o', f'{T}/landrun/landrun', 'cmd/landrun/main.go'], f'{T}/landrun', built),
            *[('clone', p['url'], p['rev'], f"{W}/cache/.lake/packages/{p['name']}", 'dependency-' + p['name']) for p in manifest],
            ('mathlib-cache', [f'{L}/lake', 'exe', 'cache', 'get'], f'{W}/cache', dict(built, MATHLIB_CACHE_DIR=f'{W}/mathlib-downloads')),
            ('cache-hash-metadata', [f'{L}/lean', '--run', str(ROOT / 'scripts/CacheHashes.lean'), f'{W}/control/cache-hash-inputs.txt'], str(ROOT), dict(built, MATHLIB_CACHE_DIR=f'{W}/mathlib-downloads')),
            ('build-lake-adapter', ['cc', '-O2', '-Wall', '-Wextra', '-DREAL_LAKE=' + json.dumps(f'{L}/lake'), '-DCONTROL=' + json.dumps(f'{W}/control'),
                                    '-DSOLUTION_MODULE="Submission"', str(ROOT / 'scripts/lake-shim.c'), '-o', f'{W}/control/bin/lake'], None, {}),
            ('trusted-lake-config', self.sandbox(config_write=True) + [f'{L}/lake', 'env', 'lean', '--version'], None, {}),
        ]
        self.assertEqual(steps, expected)
        self.assertEqual((self.work / 'cache/lakefile.toml').read_text(), v.lakefile([], 'profiles/lake-manifest.json'))
        self.assertTrue((self.work / 'control/inside.py').is_file())
        data = v.receipt()
        self.assertEqual((data['status'], data['tool_pins']), ('tools_ready', pins))
        self.assertNotIn('setup_skipped', data)
        self.assertEqual(sorted(json.loads((self.art / 'tool-sha256.json').read_text())), ['comparator', 'landrun', 'lean', 'lean4export', 'nanoda'])


class BuildPinTests(Base):
    def test_split_build_runs_one_unit_with_the_same_caps(self):
        launched, runs, labels = [], [], []

        def popen(args, stdout=None, stderr=None, **kwargs):
            launched.append(args); stdout.write('build output\n'); stdout.flush()
            return Mock(poll=Mock(return_value=0), wait=Mock(return_value=1))

        def run(args, **kwargs):
            runs.append(args)
            return Mock(stdout='exit-code\n', returncode=0)

        with patch.object(v.subprocess, 'Popen', side_effect=popen), patch.object(v.subprocess, 'run', side_effect=run), \
             patch.object(v, 'command', side_effect=lambda args, label, *a, **k: labels.append(label)), \
             patch.object(v.time, 'time', return_value=1000.0), patch.object(v.shutil, 'disk_usage', return_value=Mock(free=100 * 1024**3)):
            v.build()  # A failed Lake build is not fatal.
        W = str(self.work)
        self.assertEqual(labels, ['sandbox-preflight'])
        # No swap; the deadline leaves 15 minutes to pack and upload.
        self.assertEqual(launched, [['sudo', 'systemd-run', '--wait', '--pipe', '--unit=bos-verifier-build',
                                     '--uid=' + str(os.getuid()), '--gid=' + str(os.getgid()),
                                     '--property=RestrictAddressFamilies=~AF_UNIX', '--property=Nice=10',
                                     '--property=CPUQuota=400%', '--property=MemoryMax=14G', '--property=MemorySwapMax=0',
                                     '--property=RuntimeMaxSec=19200', '--property=TasksMax=4096',
                                     *self.sandbox(), '/usr/bin/python3', f'{W}/control/inside.py', W, 'build', '4']])
        # Only an oom-kill starts a second attempt.
        self.assertEqual(runs, [['sudo', 'systemctl', 'show', 'bos-verifier-build', '--property=Result', '--value']])
        record = v.receipt()['build']
        attempt = {'exit_code': 1, 'systemd_result': 'exit-code', 'wall_seconds': record['wall_seconds'],
                   'sampled_peak_cgroup_bytes': 0, 'memory_limit_bytes': 14 * 1024**3, 'sampled_peak_swap_bytes': 0,
                   'swap_limit_bytes': 0, 'sampled_peak_tasks': 0, 'tasks_limit': 4096, 'guard_stop': None}
        self.assertEqual(record, {**attempt, 'log': 'build.log', 'attempts': [{'lake_jobs': 4, **attempt}]})
        self.assertEqual((self.art / 'build.log').read_text(), 'build output\n')

    def run_build(self, results, clock=None, guard=None):
        """v.build() with one systemd result per attempt; returns the launches and the other systemctl calls."""
        launched, runs, results = [], [], list(results)

        def popen(args, stdout=None, stderr=None, **kwargs):
            launched.append(args); stdout.write(f'attempt {len(launched)}\n'); stdout.flush()
            return Mock(poll=Mock(side_effect=[None, 0]), wait=Mock(return_value=1))

        def run(args, **kwargs):
            runs.append(args)
            return Mock(stdout=results.pop(0) + '\n' if args[2] == 'show' else '', returncode=0)

        free = guard or (lambda: 100 * 1024**3)
        with patch.object(v.subprocess, 'Popen', side_effect=popen), patch.object(v.subprocess, 'run', side_effect=run), \
             patch.object(v, 'command'), patch.object(v.time, 'sleep'), \
             patch.object(v.time, 'time', side_effect=lambda: clock(launched) if clock else 1000.0), \
             patch.object(v.shutil, 'disk_usage', side_effect=lambda path: Mock(free=free())):
            v.build()
        return launched, runs

    def test_an_oom_kill_continues_the_build_with_fewer_lake_workers(self):
        W = str(self.work)
        launched, runs = self.run_build(['oom-kill', 'oom-kill', 'success'])
        self.assertEqual([a[a.index('--unit=bos-verifier-build') + 1:][-1] for a in launched], ['4', '3', '2'])
        self.assertTrue(all(a[:3] == ['sudo', 'systemd-run', '--wait'] and '--property=MemoryMax=14G' in a and
                            a[-5:-1] == ['/usr/bin/python3', f'{W}/control/inside.py', W, 'build'] for a in launched))
        show = ['sudo', 'systemctl', 'show', 'bos-verifier-build', '--property=Result', '--value']
        reset = ['sudo', 'systemctl', 'reset-failed', 'bos-verifier-build']
        self.assertEqual(runs, [show, reset, show, reset, show])
        self.assertEqual((self.art / 'build.log').read_text(),
                         'attempt 1\nVERIFIER build: oom-kill, the build continues with 3 Lake workers\n'
                         'attempt 2\nVERIFIER build: oom-kill, the build continues with 2 Lake workers\nattempt 3\n')
        record = v.receipt()['build']
        self.assertEqual([(a['lake_jobs'], a['systemd_result']) for a in record['attempts']], [(4, 'oom-kill'), (3, 'oom-kill'), (2, 'success')])
        self.assertEqual((record['systemd_result'], record['log']), ('success', 'build.log'))
        self.assertEqual(record['wall_seconds'], round(sum(a['wall_seconds'] for a in record['attempts']), 3))
        self.assertNotIn('lake_jobs', record)

    def test_the_build_starts_at_the_profile_count_or_the_last_count_of_the_job_before(self):
        data = v.receipt(); data['profile'] = {'lake_workers_start': 2}; v.save(data)
        launched, _ = self.run_build(['oom-kill', 'success'])
        self.assertEqual([a[-1] for a in launched], ['2', '1'])
        # A later build job of a chain: unpack restored the record of the job before (its last count was 1).
        data = v.receipt(); data['build'] = {'attempts': [{'lake_jobs': 3}, {'lake_jobs': 1}]}; v.save(data)
        launched, _ = self.run_build(['timeout'])
        self.assertEqual([a[-1] for a in launched], ['1'])

    def test_the_retries_stop_at_one_worker(self):
        launched, runs = self.run_build(['oom-kill'] * 4)
        self.assertEqual([a[-1] for a in launched], ['4', '3', '2', '1'])
        self.assertEqual(v.receipt()['build']['systemd_result'], 'oom-kill')

    def test_no_retry_after_another_failure_a_guard_stop_or_the_deadline(self):
        for result in ['exit-code', 'timeout']:
            launched, _ = self.run_build([result])
            self.assertEqual(len(launched), 1)
        # Disk space below 1 GiB stops the unit; that is not a memory problem.
        launched, _ = self.run_build(['oom-kill'], guard=lambda: 512 * 1024**2)
        self.assertEqual(len(launched), 1)
        self.assertEqual(v.receipt()['build']['guard_stop'], 'disk space below 1 GiB')
        # started_unix is 1000 in Base; the build deadline is 335 - 15 minutes later.
        launched, runs = self.run_build(['oom-kill'], clock=lambda launched: 1000.0 + 320 * 60 if launched else 1000.0)
        self.assertEqual(len(launched), 1)
        self.assertNotIn('reset-failed', [a[2] for a in runs])



@unittest.skipIf(shutil.which('cc') is None, 'no C compiler')
class LakeShimTests(unittest.TestCase):
    def test_the_shim_gives_lake_the_worker_count_of_the_verifier(self):
        tmp = tempfile.TemporaryDirectory(); self.addCleanup(tmp.cleanup)
        control, shim = Path(tmp.name), Path(tmp.name) / 'lake'
        subprocess.run(['cc', '-O2', '-Wall', '-Wextra', '-Werror', '-DREAL_LAKE="/usr/bin/env"', f'-DCONTROL="{control}"',
                        '-DSOLUTION_MODULE="Submission"', str(ROOT / 'scripts/lake-shim.c'), '-o', str(shim)], check=True)

        def threads():
            out = subprocess.run([str(shim)], capture_output=True, text=True, env={})
            return out.returncode, [l for l in out.stdout.splitlines() if l.startswith('LEAN_NUM_THREADS=')]
        self.assertEqual(threads(), (0, ['LEAN_NUM_THREADS=4']))  # No file: 4, as before.
        for value, expected in [('1\n', 1), ('2', 2), ('3\n', 3), ('4\n', 4)]:
            (control / 'lake-workers.txt').write_text(value)
            self.assertEqual(threads(), (0, [f'LEAN_NUM_THREADS={expected}']))
        for value in ['', '0\n', '5\n', '2 \n', '12\n', '2\n\n', 'x']:
            (control / 'lake-workers.txt').write_text(value)
            self.assertEqual(threads(), (1, []))


if __name__ == '__main__':
    unittest.main()
