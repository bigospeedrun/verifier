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

    def test_a_chain_unit_sizes_its_swap_from_the_free_disk(self):
        GiB = 1024**3
        v.SWAP_DIR.mkdir()
        for free, size in [(100 * GiB, 64 * GiB), (40 * GiB + 5, 30 * GiB), (20 * GiB, 16 * GiB), (5 * GiB, 16 * GiB)]:
            with self.subTest(free=free), patch.object(v.shutil, 'disk_usage', return_value=Mock(free=free)):
                self.assertEqual(v.chain_swap_bytes(), size)
                self.assertEqual([v.kernel_swap_limit(k) for k in ['export', 'check']], [size, size])
        # This job's own file counts as free disk, so a later unit asks for the same size.
        (v.SWAP_DIR / 'bos-kernel.swap').write_bytes(b'x' * 1024)
        with patch.object(v.shutil, 'disk_usage', return_value=Mock(free=30 * GiB - 1024)):
            self.assertEqual(v.chain_swap_bytes(), 20 * GiB)
        # Other units keep SWAP_BYTES.
        with patch.object(v.shutil, 'disk_usage', return_value=Mock(free=100 * GiB)):
            self.assertEqual(v.kernel_swap_limit('nanoda'), 16 * GiB)

    def test_a_large_swap_falls_back_to_swap_bytes_and_reuses_the_active_file(self):
        GiB = 1024**3
        allocated = []
        def command(args, label, *a, **k):
            if label == 'kernel-swap-allocate':
                allocated.append(args[3]); Path(args[4]).write_bytes(b'')
        v.SWAP_DIR.mkdir()
        with patch.object(v, 'command', side_effect=command), patch.object(v, 'active_swaps', return_value=set()):
            with patch.object(v.shutil, 'disk_usage', return_value=Mock(free=60 * GiB)):
                self.assertEqual(v.prepare_kernel_swap(40 * GiB), 40 * GiB)
            (v.SWAP_DIR / 'bos-kernel.swap').unlink()
            with patch.object(v.shutil, 'disk_usage', return_value=Mock(free=25 * GiB)):
                self.assertEqual(v.prepare_kernel_swap(40 * GiB), 16 * GiB)
            for bad in [16 * GiB + 1, 8 * GiB]:
                with self.assertRaises(ValueError):
                    v.prepare_kernel_swap(bad)
        self.assertEqual(allocated, ['40G', '16G'])
        with patch.object(v, 'active_swaps', return_value={str(v.SWAP_DIR / 'bos-kernel.swap')}), patch.object(v, 'command') as c:
            (v.SWAP_DIR / 'bos-kernel.swap').write_bytes(b'x' * 4096)
            self.assertEqual(v.prepare_kernel_swap(64 * GiB), 4096)
            c.assert_not_called()

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
        self.threads = []  # control/nanoda-threads.txt at each launch (None: no file)
        self.stacks = []  # control/nanoda-stack.txt at each launch (None: no file)
        (self.work / 'control/nanoda-stack.txt').unlink(missing_ok=True)
        (self.work / 'control/chain-targets.txt').write_text('Submission\n')

        def popen(args, stdout=None, stderr=None, **kwargs):
            text, result = outputs.pop(0)
            launched.append((args[4].removeprefix('--unit='), (self.work / 'control/lake-workers.txt').read_text().strip()))
            threads_file = self.work / 'control/nanoda-threads.txt'
            self.threads.append(threads_file.read_text().strip() if threads_file.exists() else None)
            stack_file = self.work / 'control/nanoda-stack.txt'
            self.stacks.append(stack_file.read_text().strip() if stack_file.exists() else None)
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

    def test_an_oom_kill_of_nanoda_after_the_build_starts_it_again_with_2_then_1_threads(self):
        # Task be5e47b3 (Lead, 2026-11-23): 4, then 2, then 1 nanoda threads; the Lake workers stay as they were.
        done = 'VERIFIER source chain 0: exit=0 seconds=9.000\n'
        launched, calls = self.run_verify(['nanoda'], [(done, 'oom-kill'), (done, 'oom-kill'), (done + ACCEPT, 'success')])
        self.assertEqual(launched, [('bos-verifier-nanoda', '4')] * 3)
        self.assertEqual(self.threads, ['4', '2', '1'])
        reset = ['sudo', 'systemctl', 'reset-failed', 'bos-verifier-nanoda']
        self.assertEqual([c for c in calls if c == reset], [reset, reset])
        nanoda = v.receipt()['kernels']['nanoda']
        self.assertEqual((nanoda['status'], nanoda['reason']), ('passed', 'comparator_acceptance'))
        self.assertEqual([(a['nanoda_threads'], a['lake_jobs'], a['systemd_result']) for a in nanoda['attempts']],
                         [(4, 4, 'oom-kill'), (2, 4, 'oom-kill'), (1, 4, 'success')])
        self.assertEqual(v.receipt()['nanoda_threads'], 1)
        log = (self.art / 'nanoda.log').read_text()
        self.assertIn('VERIFIER nanoda: oom-kill, the check starts again with 2 nanoda threads\n', log)
        self.assertIn('VERIFIER nanoda: oom-kill, the check starts again with 1 nanoda threads\n', log)
        self.assertEqual([name for name, _ in v.resource_units(v.receipt()) if name.startswith('nanoda')],
                         ['nanoda attempt 1 (4 nanoda threads)', 'nanoda attempt 2 (2 nanoda threads)', 'nanoda attempt 3 (1 nanoda threads)'])
        warnings = v.resource_report(v.receipt())['warnings']
        self.assertIn('nanoda attempt 2 (2 nanoda threads): out-of-memory kill', warnings)
        # Still killed at 1 thread: no fourth attempt, and the outcome is the last attempt's own.
        self.run_verify(['nanoda'], [(done, 'oom-kill')] * 3)
        self.assertEqual(self.threads, ['4', '2', '1'])
        self.assertEqual(v.receipt()['kernels']['nanoda']['reason'], 'out_of_memory')
        # A pass at 4 threads makes no retry, and the file says 4.
        launched, _ = self.run_verify(['nanoda'], [(done + ACCEPT, 'success')])
        self.assertEqual((len(launched), self.threads), (1, ['4']))

    def test_a_nanoda_stack_overflow_starts_the_check_again_with_a_larger_stack(self):
        # verifier#226 (Lead, 2026-11-26): the Lean kernel and the axiom audit passed; nanoda aborted with a stack overflow
        # in a worker (its own 32 MiB default). Every check starts at 256 MiB, then 1024 and 4096 MiB, with the same threads.
        done = 'VERIFIER source chain 0: exit=0 seconds=9.000\n'
        overflow = ("Running nanoda kernel on solution\nnanoda kernel num_threads: 4\n\nthread 'thread_1' (3054) has overflowed its stack\n"
                    'fatal runtime error: stack overflow, aborting\nnanoda kernel rejected the solution\nRunning Lean default kernel on solution.\n'
                    'Lean default kernel accepts the solution\nuncaught exception: nanoda exited with 134\n')
        self.assertTrue(v.nanoda_stack_overflow('exit-code', done + overflow))
        launched, calls = self.run_verify(['nanoda'], [(done + overflow, 'exit-code'), (done + ACCEPT, 'success')])
        self.assertEqual((self.threads, self.stacks), (['4', '4'], ['256', '1024']))
        nanoda = v.receipt()['kernels']['nanoda']
        self.assertEqual((nanoda['status'], nanoda['reason']), ('passed', 'comparator_acceptance'))
        self.assertEqual([(a['nanoda_threads'], a['nanoda_stack_mib'], a['systemd_result']) for a in nanoda['attempts']],
                         [(4, 256, 'exit-code'), (4, 1024, 'success')])
        self.assertEqual((v.receipt()['nanoda_threads'], v.receipt()['nanoda_stack_mib']), (4, 1024))
        self.assertIn('VERIFIER nanoda: stack overflow, the check starts again with a 1024 MiB nanoda stack\n', (self.art / 'nanoda.log').read_text())
        self.assertEqual([c for c in calls if c == ['sudo', 'systemctl', 'reset-failed', 'bos-verifier-nanoda']], [['sudo', 'systemctl', 'reset-failed', 'bos-verifier-nanoda']])
        self.assertEqual([name for name, _ in v.resource_units(v.receipt()) if name.startswith('nanoda')],
                         ['nanoda attempt 1 (4 nanoda threads)', 'nanoda attempt 2 (4 nanoda threads) (1024 MiB nanoda stack)'])
        # Still overflowing at 4096 MiB: no fourth attempt, and the outcome stays for a maintainer (no new reason).
        self.run_verify(['nanoda'], [(done + overflow, 'exit-code')] * 3)
        self.assertEqual(self.stacks, ['256', '1024', '4096'])
        self.assertEqual((v.receipt()['kernels']['nanoda']['status'], v.receipt()['kernels']['nanoda']['reason']), ('pending_review', 'ambiguous_failure'))
        # An overflow, then an oom-kill at the larger stack: fewer threads, the larger stack is kept.
        self.run_verify(['nanoda'], [(done + overflow, 'exit-code'), (done, 'oom-kill'), (done + ACCEPT, 'success')])
        self.assertEqual((self.threads, self.stacks), (['4', '4', '2'], ['256', '1024', '1024']))
        # Not a stack overflow: another nanoda failure, the overflow line without the abort exit, or too little time.
        for text in [done + 'uncaught exception: nanoda exited with 134\n', done + overflow.replace('exited with 134', 'exited with 1')]:
            self.run_verify(['nanoda'], [(text, 'exit-code')])
            self.assertEqual(self.stacks, ['256'])
        self.assertFalse(v.nanoda_stack_overflow('oom-kill', done + overflow))
        clock = iter(range(0, 10**7, 30000))
        with patch.object(v.time, 'monotonic', lambda: next(clock)):
            self.run_verify(['nanoda'], [(done + overflow, 'exit-code'), (done + ACCEPT, 'success')])
        self.assertEqual(self.stacks, ['256'], 'the first attempt took 30000 s, more than the deadline leaves')

    def test_the_profile_can_start_nanoda_at_fewer_threads_and_a_bad_value_starts_at_4(self):
        done = 'VERIFIER source chain 0: exit=0 seconds=9.000\n'
        for value in [None, 0, 3, 5, '1', True, 1.0]:
            self.assertEqual(v.first_nanoda_threads({'profile': {'nanoda_threads_start': value}}), 4, repr(value))
        self.assertEqual(v.first_nanoda_threads({}), 4)
        for value in [4, 2, 1]:
            self.assertEqual(v.first_nanoda_threads({'profile': {'nanoda_threads_start': value}}), value)
        # A smoke run: start at 1; the file says 1 and an oom-kill there is final.
        data = v.receipt(); data['profile'] = {'nanoda_threads_start': 1}; v.save(data)
        launched, _ = self.run_verify(['nanoda'], [(done + ACCEPT, 'success')])
        self.assertEqual((len(launched), self.threads), (1, ['1']))
        self.assertEqual(v.receipt()['kernels']['nanoda']['attempts'][0]['nanoda_threads'], 1)
        self.run_verify(['nanoda'], [(done, 'oom-kill')])
        self.assertEqual(self.threads, ['1'])
        data = v.receipt(); data['profile'] = {'nanoda_threads_start': 2}; v.save(data)
        self.run_verify(['nanoda'], [(done, 'oom-kill'), (done, 'oom-kill')])
        self.assertEqual(self.threads, ['2', '1'])

    def test_no_nanoda_thread_retry_after_another_failure_a_guard_stop_an_unfinished_build_or_too_little_time(self):
        done = 'VERIFIER source chain 0: exit=0 seconds=9.000\n'
        # A rejection or a timeout is not an out-of-memory kill.
        for result in ['exit-code', 'timeout']:
            self.run_verify(['nanoda'], [(done, result)])
            self.assertEqual(self.threads, ['4'], result)
        # An oom-kill while the build is unfinished is the Lake worker loop's: the thread file keeps 4.
        building = '✔ [10/20] Built Submission.A\n'
        launched, _ = self.run_verify(['nanoda'], [(building, 'oom-kill'), (building, 'oom-kill'), (building, 'oom-kill'), (building, 'oom-kill')])
        self.assertEqual((launched, self.threads), ([('bos-verifier-nanoda', n) for n in '4321'], ['4'] * 4))
        # Time left: a retry needs at least the wall time of the killed attempt (it repeats the export and the Lean replay).
        data = v.receipt(); data['lake_workers'] = 4; v.save(data)
        clock = iter(range(0, 10**7, 30000))
        with patch.object(v.time, 'monotonic', lambda: next(clock)):
            self.run_verify(['nanoda'], [(done, 'oom-kill'), (done + ACCEPT, 'success')])
        self.assertEqual(self.threads, ['4'], 'the first attempt took 30000 s, more than the 20100 s that the deadline leaves')
        self.assertGreater(v.receipt()['kernels']['nanoda']['attempts'][0]['wall_seconds'], 20100)
        self.assertEqual(v.receipt()['kernels']['nanoda']['reason'], 'out_of_memory')

    def test_inside_passes_the_nanoda_thread_count_only_from_the_controllers_file(self):
        """scripts/inside.py, phase nanoda-exec, with a fake Comparator that prints its environment."""
        with tempfile.TemporaryDirectory() as temp:
            work = Path(temp)
            (work / 'control').mkdir()
            (work / 'control/request.json').write_text(json.dumps({'request': {'lean_toolchain': 'leanprover/lean4:v4.34.1'}}))
            fake = work / 'tools/comparator/.lake/build/bin/comparator'
            fake.parent.mkdir(parents=True)
            fake.write_text('#!/bin/sh\necho "threads=${COMPARATOR_NANODA_THREADS-unset}"\n'); fake.chmod(0o755)

            def run(phase, text=None, env=None):
                threads = work / 'control/nanoda-threads.txt'
                threads.unlink(missing_ok=True)
                if text is not None:
                    threads.write_text(text)
                result = subprocess.run([sys.executable, str(ROOT / 'scripts/inside.py'), str(work), phase], capture_output=True, text=True,
                                        env=dict(os.environ, **(env or {})))
                return result.returncode, result.stdout.strip()
            for count in '1234':
                self.assertEqual(run('nanoda-exec', count + '\n'), (0, 'threads=' + count))
            # No file (the Lean check, an older flow): unset, so Comparator keeps its own 4.
            self.assertEqual(run('nanoda-exec'), (0, 'threads=unset'))
            self.assertEqual(run('lean-exec', '2\n'), (0, 'threads=unset'))
            # The file wins over the environment; without a file the environment is not touched (the sandbox starts with an
            # empty one, sandbox_args, so a submission has no way to set it).
            self.assertEqual(run('nanoda-exec', '2\n', {'COMPARATOR_NANODA_THREADS': '1'}), (0, 'threads=2'))
            self.assertEqual(run('nanoda-exec', None, {'COMPARATOR_NANODA_THREADS': '1'}), (0, 'threads=1'))
            # A bad file stops the check before Comparator starts.
            for bad in ['0\n', '5\n', '2', '2\n\n', ' 2\n', 'two\n', '']:
                code, out = run('nanoda-exec', bad)
                self.assertEqual((code != 0, out), (True, ''), repr(bad))

    def test_inside_passes_the_nanoda_stack_size_only_from_the_controllers_file(self):
        """verifier#226: scripts/inside.py, phase nanoda-exec, sets COMPARATOR_NANODA_STACK_MIB from control/nanoda-stack.txt only."""
        with tempfile.TemporaryDirectory() as temp:
            work = Path(temp)
            (work / 'control').mkdir()
            (work / 'control/request.json').write_text(json.dumps({'request': {'lean_toolchain': 'leanprover/lean4:v4.34.1'}}))
            fake = work / 'tools/comparator/.lake/build/bin/comparator'
            fake.parent.mkdir(parents=True)
            fake.write_text('#!/bin/sh\necho "stack=${COMPARATOR_NANODA_STACK_MIB-unset}"\n'); fake.chmod(0o755)

            def run(phase, text=None, env=None):
                stack = work / 'control/nanoda-stack.txt'
                stack.unlink(missing_ok=True)
                if text is not None:
                    stack.write_text(text)
                result = subprocess.run([sys.executable, str(ROOT / 'scripts/inside.py'), str(work), phase], capture_output=True, text=True,
                                        env=dict(os.environ, **(env or {})))
                return result.returncode, result.stdout.strip()
            for size in ['256', '1024', '4096']:
                self.assertEqual(run('nanoda-exec', size + '\n'), (0, 'stack=' + size))
            self.assertEqual(run('nanoda-exec'), (0, 'stack=unset'))
            self.assertEqual(run('lean-exec', '1024\n'), (0, 'stack=unset'))
            self.assertEqual(run('nanoda-exec', '1024\n', {'COMPARATOR_NANODA_STACK_MIB': '4096'}), (0, 'stack=1024'))
            for bad in ['32\n', '512\n', '1024', '1024\n\n', ' 256\n', '']:
                code, out = run('nanoda-exec', bad)
                self.assertEqual((code != 0, out), (True, ''), repr(bad))

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
        def image_check(name):
            return lambda: steps.append((name,))

        with patch.object(v, 'command', side_effect=command), patch.object(v, 'clone', side_effect=clone), \
             patch.object(v, 'require_runner_image', side_effect=image_check('require-runner-image')), \
             patch.object(v, 'require_bwrap_profile', side_effect=image_check('require-bwrap-profile')), \
             patch.object(v, 'digest', side_effect=lambda p: pins['elan_tar_sha256'] if p.name == 'elan.tar.gz' else
                          {ROOT / x['file']: x['sha256'] for x in pins['lean4export_patches'] + pins['comparator_nanoda_patches']}.get(p, 'h')):
            v.setup()
        W, T, L = str(self.work), str(self.work / 'tools'), str(lean)
        env = {'ELAN_HOME': f'{T}/elan', 'LEAN_NUM_THREADS': '4'}
        built = dict(env, PATH0=L)
        manifest = json.loads((ROOT / 'profiles/lake-manifest.json').read_text())['packages']
        url = f"https://github.com/leanprover/elan/releases/download/{pins['elan_version']}/elan-x86_64-unknown-linux-gnu.tar.gz"
        expected = [
            ('require-runner-image',),
            ('apt-update', ['sudo', 'apt-get', 'update'], None, {}),
            ('apt-tools', ['sudo', 'apt-get', 'install', '-y', 'bubblewrap', 'build-essential', 'pkg-config', 'libssl-dev', 'apparmor', 'apparmor-profiles'], None, {}),
            ('require-bwrap-profile',),
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
            # Task be5e47b3: the nanoda thread patch on Comparator. Its own key: the segmented-check self-test stays off.
            ('tool-comparator-nanoda-patch-check-comparator-nanoda-threads', ['git', '-C', f'{T}/comparator', 'apply', '--check', str(ROOT / 'patches/comparator-nanoda-threads.patch')], None, {}),
            ('tool-comparator-nanoda-patch-comparator-nanoda-threads', ['git', '-C', f'{T}/comparator', 'apply', str(ROOT / 'patches/comparator-nanoda-threads.patch')], None, {}),
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



class RunnerImageTests(unittest.TestCase):
    """Every job runs on the reviewed image ubuntu-24.04 (verifier #195, 2026-11-14: ubuntu-latest became 26.04, where
    the bwrap AppArmor profile is not at its 24.04 path). Setup refuses another image with a clear reason."""
    def test_every_job_pins_ubuntu_24_04(self):
        import re
        lines = [(p.name, line.strip()) for p in sorted((ROOT / '.github/workflows').glob('*.yml'))
                 for line in p.read_text().splitlines() if re.match(r'\s*runs-on:', line)]
        self.assertGreater(len(lines), 15)
        self.assertEqual({line for _, line in lines}, {'runs-on: ubuntu-24.04'})
        for p in (ROOT / '.github/workflows').glob('*.yml'):
            self.assertNotIn('ubuntu-latest', p.read_text(), p.name)

    def test_setup_refuses_another_image(self):
        with tempfile.TemporaryDirectory() as d:
            release = Path(d) / 'os-release'
            with patch.object(v, 'OS_RELEASE', release):
                release.write_text('NAME="Ubuntu"\nID=ubuntu\nVERSION_ID="24.04"\n')
                v.require_runner_image()
                for text in ['ID=ubuntu\nVERSION_ID="26.04"\n', 'ID=debian\nVERSION_ID="24.04"\n', 'ID=ubuntu\n', '']:
                    release.write_text(text)
                    with self.subTest(text=text), self.assertRaisesRegex(RuntimeError, '^unsupported runner image: .*Ubuntu 24.04 only'):
                        v.require_runner_image()
            profile = Path(d) / 'bwrap-userns-restrict'
            with patch.object(v, 'BWRAP_PROFILE', profile):
                with self.assertRaisesRegex(RuntimeError, '^unsupported runner image: .*bwrap-userns-restrict is missing'):
                    v.require_bwrap_profile()
                profile.write_text('profile bwrap {}\n')
                v.require_bwrap_profile()
        self.assertEqual(str(v.BWRAP_PROFILE), '/usr/share/apparmor/extra-profiles/bwrap-userns-restrict')


if __name__ == '__main__':
    unittest.main()
