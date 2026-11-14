"""The split build (docs/execution.md): the profile runner, the selection flag, the PR refusal, the build job,
the pack/unpack hand-over (rules S1 and S2) and the workflow structure."""
import hashlib
import io
import json
import os
from pathlib import Path
import runpy
import shutil
import subprocess
import sys
import tarfile
import tempfile
import unittest
from unittest.mock import patch, Mock

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import pr_submissions as p
import submissions as s
import verifier as v


def sub(problem, bound='1'):
    return {'schema_version': 1, 'problem': problem, 'bound': bound, 'repo_url': 'https://github.com/a/b',
            'commit': 'a' * 40, 'authors': []}


class RunnerTests(unittest.TestCase):
    def test_runner_values(self):
        self.assertEqual(s.runner(sub('catalan')), 'github-split')
        # 3SUM issues run split since 2026-11-02: issue #99 built for over 5 h 16 min in one job and timed out.
        self.assertEqual(s.runner(sub('3sum')), 'github-split')
        for problem in ['dft', 'apsp', 'average-sensitivity', 'subset-sum']:
            self.assertEqual(s.runner(sub(problem)), 'github')
        self.assertEqual(s.runner(dict(sub('dft', '7547360/10000000000'), entrypoint='dft233')), 'github')
        # Catalan opened on 2026-10-27; its issues run as split runs.
        self.assertNotIn('catalan', s.CLOSED)

    def test_an_unknown_runner_is_refused(self):
        profiles = json.loads((ROOT / 'profiles/direct.json').read_text())
        for bad in ['maintainer-desktop', 'github-Split', '', None, True]:
            with self.subTest(runner=bad):
                changed = dict(profiles, dft=dict(profiles['dft'], runner=bad))
                real = Path.read_text
                fake = lambda path, *a, **k: json.dumps(changed) if path.name == 'direct.json' else real(path, *a, **k)
                with patch.object(Path, 'read_text', fake), self.assertRaises(ValueError):
                    s.selected_profile(sub('dft'))

    def test_matrix_entry(self):
        self.assertEqual(s.matrix_entry(5, 'x', 'issue', sub('catalan')),
                         {'issue_number': 5, 'login': 'x', 'route': 'issue', 'split': True})
        self.assertEqual(s.matrix_entry(5, 'x', 'issue', sub('3sum')),
                         {'issue_number': 5, 'login': 'x', 'route': 'issue', 'split': True})
        self.assertEqual(s.matrix_entry(5, 'x', 'issue', sub('dft')), {'issue_number': 5, 'login': 'x', 'route': 'issue'})
        # A PR request can have no submission (invalid layout); the PR route never splits.
        self.assertEqual(s.matrix_entry(6, 'y', 'pull_request', None), {'issue_number': 6, 'login': 'y', 'route': 'pull_request'})

    def test_a_split_pr_starts_no_job(self):
        class Lease:
            def admitted(self, key): return False
        pr = {'number': 7, 'head': {'sha': 'h'}, 'base': {'sha': 'b'}, 'user': {'login': 'u'}}
        with patch.object(p, 'api', return_value=pr), patch.object(p, 'proof_candidate', return_value=True), \
             patch.object(p, 'inspect_pr', return_value={'head_sha': 'h', 'submission': {'problem': 'catalan'}, 'pr_url': 'u'}), \
             patch.object(p, 'validate_controller'), patch.object(s, 'current_record') as record, \
             patch.dict(os.environ, GITHUB_SHA='b' * 40):
            self.assertIsNone(p.select_candidate({'number': 7}, Lease()))
            record.assert_not_called()

    def test_a_3sum_pr_runs_as_one_job(self):
        # 3SUM issues run split; a 3SUM PR is still selected and runs in pr_verify (no build job).
        class Lease:
            def admitted(self, key): return False
        pr = {'number': 8, 'head': {'sha': 'h'}, 'base': {'sha': 'b'}, 'user': {'login': 'u'}}
        submission = sub('3sum', '19/10')
        with patch.object(p, 'api', return_value=pr), patch.object(p, 'proof_candidate', return_value=True), \
             patch.object(p, 'inspect_pr', return_value={'head_sha': 'h', 'submission': submission, 'pr_url': 'u'}), \
             patch.object(p, 'validate_controller'), patch.object(s, 'current_record', return_value='record') as record, \
             patch.object(s, 'qualifies_for_run', return_value=True), patch.dict(os.environ, GITHUB_SHA='b' * 40):
            selected = p.select_candidate({'number': 8}, Lease())
        record.assert_called_once_with('3sum', 'u')
        self.assertEqual((selected['gate'], selected['record_gate']), ('ready', 'record'))
        self.assertEqual(s.matrix_entry(8, 'u', 'pull_request', submission), {'issue_number': 8, 'login': 'u', 'route': 'pull_request'})


ROOTS = ['Submission']


class AllowListTests(unittest.TestCase):
    def test_allowed_paths(self):
        for rel, is_dir in [('lib/lean/Submission.olean', False), ('lib/lean/Submission.ilean', False),
                            ('lib/lean/Submission.trace', False), ('lib/lean/Submission', True),
                            ('lib/lean/Submission/OAI/A.olean', False), ('lib/lean/Submission/OAI', True),
                            ('ir/Submission.c', False), ('ir/Submission.c.hash', False), ('ir/Submission/OAI/A.c', False),
                            ('ir/Submission', True)]:
            with self.subTest(rel=rel):
                self.assertTrue(v.build_allowed(rel, is_dir, ROOTS))

    def test_refused_paths(self):
        for rel, is_dir in [('lib/lean/Mathlib/Order/Basic.olean', False), ('lib/lean/Mathlib', True), ('lib/lean/Mathlib.olean', False),
                            ('lib/lean/VerifierChallenge.olean', False), ('lib/lean/VerifierChallenge.trace', False),
                            ('ir/VerifierChallenge.c', False), ('lib/lean/VerifierAudit.olean', False), ('ir/VerifierAudit.c', False),
                            ('lib/lean/Init/Prelude.olean', False), ('lib/lean/Init', True), ('lib/lean/Lean.olean', False),
                            ('lib/lean/Submission', False), ('lib/lean/Submission.', False), ('lib/lean/SubmissionX.olean', False),
                            ('lib/lean/Submission.olean', True), ('lib/lean/Submission.x/A.olean', False),
                            ('lib/Submission.olean', False), ('lib/libSubmission.a', False), ('lib', True), ('lib/lean', True),
                            ('ir', True), ('bin/x', False), ('other/Submission.olean', False), ('Submission.olean', False),
                            ('../lib/lean/Submission.olean', False), ('lib/lean/../lean/Submission.olean', False),
                            ('lib/lean/Submission/../../Mathlib.olean', False), ('/lib/lean/Submission.olean', False),
                            ('lib/lean/Submission/./A.olean', False), ('lib//lean/Submission.olean', False),
                            ('lib/lean/Submission/A.olean/', False), ('lib/lean/Submission/\udcff.olean', False),
                            ('lib/lean/Submission/A\0.olean', False), ('', False),
                            # Shared libraries: Lake puts .lake/build/lib on LD_LIBRARY_PATH (docs/execution.md).
                            ('lib/libleanshared.so', False), ('lib/lean/libleanshared.so', False), ('lib/lean/libc.so.6', False),
                            ('lib/libc.so.6', False), ('lib/lean/Submission/../x', False), ('lib/lean/Submission/../libc.so.6', False)]:
            with self.subTest(rel=rel, is_dir=is_dir):
                self.assertFalse(v.build_allowed(rel, is_dir, ROOTS))

    def test_roots_come_from_the_profile_and_its_dependencies(self):
        profile = {'source_roots': ['Submission'], 'solution_dependencies': [{'source_roots': ['Dep']}]}
        self.assertEqual(v.build_roots(profile), ['Submission', 'Dep'])
        for bad in ['Init', 'Lean', 'Std', 'Lake', 'VerifierChallenge', 'VerifierAudit', 'A.B', '../x', '']:
            with self.subTest(root=bad), self.assertRaises(ValueError):
                v.build_roots({'source_roots': [bad]})


class ChainTargetTests(unittest.TestCase):
    def test_split_writes_one_line(self):
        chains = [['Submission.A', 'Submission.B'], ['Submission.C', 'Submission']]
        profiles = json.loads((ROOT / 'profiles/direct.json').read_text())
        for name in ['catalan', '3sum']:
            with self.subTest(profile=name):
                self.assertEqual(v.chain_targets(profiles[name], chains, True), 'Submission\n')
                # A PR or maintainer run of a split profile has no build job: it keeps the chains.
                self.assertEqual(v.chain_targets(profiles[name], chains, False), 'Submission.B\nSubmission\n')
        self.assertEqual(v.chain_targets(profiles['dft'], chains, False), 'Submission.B\nSubmission\n')
        with self.assertRaises(ValueError):
            v.chain_targets(profiles['dft'], chains, True)


class SplitGateTests(unittest.TestCase):
    """Job 2 follows job 1's gate: an explicit 'false' there ends job 2 as claimed only."""
    def test_preflight(self):
        import queue_lease
        from test_submissions import issue
        item = issue(42)
        selected = s.issue_request(item, s.issue_input(item))
        with tempfile.TemporaryDirectory() as tmp:
            old = Path.cwd(); os.chdir(tmp); self.addCleanup(os.chdir, old)
            for split, proceed, expected in [('true', 'true', 'true'), ('true', 'false', 'false'), ('true', '', 'true'),
                                             ('false', 'false', 'true'), ('', 'false', 'true'), ('false', '', 'true')]:
                with self.subTest(split=split, proceed=proceed):
                    Path('request').mkdir(exist_ok=True); Path('request/request.json').write_text(s.canonical(selected))
                    Path('output').write_text('')
                    with patch.dict(os.environ, GITHUB_OUTPUT=str(Path(tmp) / 'output'), BOS_SPLIT=split, BOS_BUILD_PROCEED=proceed), \
                         patch.object(queue_lease, 'assert_owner'), patch.object(s, 'api', return_value=item), \
                         patch.object(s, 'current_record', return_value={'score': '1'}), patch.object(s, 'qualifies_for_run', return_value=True):
                        s.preflight()
                    self.assertEqual(Path('output').read_text(), 'proceed=' + expected + '\n')
                    gate = json.loads(Path('artifacts/gate.json').read_text())
                    self.assertEqual((gate['status'], gate['reason']), ('proceed', 'matches_or_beats_current_record') if expected == 'true'
                                     else ('claimed_only', 'record_or_issue_changed'))


class Base(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory(); self.addCleanup(tmp.cleanup)
        self.tmp = Path(tmp.name)
        self.work, self.art, self.out = self.tmp / 'bos-verifier', self.tmp / 'artifacts', self.tmp / 'build-artifact'
        for target, value in [('WORK', self.work), ('ART', self.art), ('BUILD_ARTIFACT', self.out)]:
            patcher = patch.object(v, target, value); patcher.start(); self.addCleanup(patcher.stop)
        profile = json.loads((ROOT / 'profiles/direct.json').read_text())['catalan']
        (self.work / 'control').mkdir(parents=True); (self.work / 'tools').mkdir()
        v.write_json(self.work / 'control/request.json', {'request': {'lean_toolchain': 'leanprover/lean4:v4.34.1'},
                                                          'profile': profile, 'names': ['Race.bound']})
        self.build = self.work / 'stage/.lake/build'; self.build.mkdir(parents=True)
        # A fake toolchain lib/lean: unpack refuses a root with the name of one of its entries.
        self.toolchain_lib = self.work / 'tools/elan/toolchains/leanprover--lean4---v4.34.1/lib/lean'
        self.toolchain_lib.mkdir(parents=True)
        for name in ['Init', 'Init.olean', 'Std', 'Lean.olean', 'Lake', 'libleanshared.so']:
            (self.toolchain_lib / name).mkdir() if '.' not in name else (self.toolchain_lib / name).write_text('')
        self.art.mkdir()
        v.save({'started_unix': 1000.0, 'steps': [], 'kernels': {}, 'build': {'exit_code': 0}})
        self.output = self.tmp / 'github-output'
        env = patch.dict(os.environ, GITHUB_OUTPUT=str(self.output)); env.start(); self.addCleanup(env.stop)

    def put(self, rel, data=b'x', mtime_ns=1_700_000_000_123_456_789):
        path = self.build / rel; path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data); os.utime(path, ns=(mtime_ns, mtime_ns))
        return path

    def pack(self, state='inactive\n'):
        with patch.object(v.subprocess, 'run', return_value=Mock(stdout=state)) as run:
            v.pack()
        run.assert_called_once_with(['systemctl', 'is-active', 'bos-verifier-build'], capture_output=True, text=True, check=False)
        return v.receipt()['pack']

    def packed_file(self):
        return self.out / v.BUILD_PACK

    def tar_bytes(self):
        return subprocess.run(['zstd', '-d', '-q', '-c', '--', str(self.packed_file())], capture_output=True, check=True).stdout

    def unpack(self, sha=None, result='success'):
        sha = sha if sha is not None else hashlib.sha256(self.packed_file().read_bytes()).hexdigest()
        def command(args, label, *a, **k):
            self.assertEqual(os.listdir(self.build), [])  # Before any restored file exists.
            (self.art / (label + '.log')).write_text('/w/.lake/packages/mathlib/.lake/build/lib/lean:/w/stage/.lake/build/lib/lean\n')
        with patch.dict(os.environ, BOS_BUILD_RESULT=result, BOS_BUILD_SHA256=sha), patch.object(v, 'command', side_effect=command) as c:
            v.unpack()
        return c

    def tree(self):
        found = {}
        for top, dirs, files in os.walk(self.build):
            for name in dirs + files:
                path = Path(top) / name; st = os.lstat(path)
                found[str(path.relative_to(self.build))] = (path.is_dir(), oct(st.st_mode & 0o777), st.st_mtime_ns,
                                                             None if path.is_dir() else path.read_bytes())
        return found


class PackTests(Base):
    def test_pack_keeps_only_the_allow_list_and_never_follows_a_symlink(self):
        self.put('lib/lean/Submission.olean', b'root')
        self.put('lib/lean/Submission/OAI/A.olean', b'a' * 3000)
        self.put('ir/Submission/OAI/A.c', b'c')
        self.put('lib/lean/Mathlib/Order/Basic.olean', b'evil')
        self.put('lib/lean/VerifierChallenge.olean', b'evil')
        self.put('lib/lean/Init/Prelude.olean', b'evil')
        self.put('lib/libSubmission.a', b'lib')
        self.put('lib/libleanshared.so', b'evil'); self.put('lib/lean/libc.so.6', b'evil')
        secret = self.tmp / 'secret'; secret.write_text('runner secret')
        os.symlink(secret, self.build / 'lib/lean/Submission/OAI/Link.olean')
        os.symlink(self.tmp, self.build / 'lib/lean/Submission/Dir')
        os.link(self.build / 'lib/lean/Submission.olean', self.build / 'lib/lean/Submission/Hard.olean')
        os.mkfifo(self.build / 'ir/Submission/fifo')
        record = self.pack()
        with tarfile.open(fileobj=io.BytesIO(self.tar_bytes())) as tar:
            members = tar.getmembers()
        names = [m.name for m in members]
        self.assertEqual(names, ['ir/Submission', 'ir/Submission/OAI', 'ir/Submission/OAI/A.c', 'lib/lean/Submission',
                                 'lib/lean/Submission/OAI', 'lib/lean/Submission/OAI/A.olean'])
        for m in members:
            self.assertEqual((m.uid, m.gid, m.uname, m.gname), (0, 0, '', ''))
            self.assertEqual((m.type, m.mode), (tarfile.DIRTYPE, 0o755) if m.isdir() else (tarfile.REGTYPE, 0o644))
        self.assertEqual(members[2].pax_headers['mtime'], '1700000000.123456789')
        # The hard link's other name is refused too (one inode, two names).
        self.assertEqual(record['skipped_first'], ['ir/Submission/fifo', 'lib/lean/Init', 'lib/lean/Mathlib', 'lib/lean/Submission.olean',
                                                   'lib/lean/Submission/Dir', 'lib/lean/Submission/Hard.olean',
                                                   'lib/lean/Submission/OAI/Link.olean', 'lib/lean/VerifierChallenge.olean',
                                                   'lib/lean/libc.so.6', 'lib/libSubmission.a', 'lib/libleanshared.so'])
        self.assertEqual((record['members'], record['files'], record['bytes'], record['skipped_count']), (6, 2, 3001, 11))
        self.assertEqual(record['compressed_bytes'], self.packed_file().stat().st_size)
        self.assertFalse((self.out / 'build.tar').exists())
        sha = hashlib.sha256(self.packed_file().read_bytes()).hexdigest()
        self.assertEqual(record['sha256'], sha)
        self.assertEqual(self.output.read_text(), 'build_sha256=' + sha + '\n')
        self.assertEqual(json.loads((self.out / 'build.json').read_text()), {'build': {'exit_code': 0}, 'pack': record})

    def test_pack_is_deterministic(self):
        self.put('lib/lean/Submission/B.olean', b'b'); self.put('lib/lean/Submission/A.olean', b'a'); self.put('ir/Submission.c')
        first = self.pack()['sha256']
        os.chmod(self.build / 'lib/lean/Submission/A.olean', 0o600)
        self.assertEqual(self.pack()['sha256'], first)
        self.put('lib/lean/Submission/A.olean', b'a', mtime_ns=1_700_000_000_123_456_790)
        self.assertNotEqual(self.pack()['sha256'], first)

    def test_pack_refuses_a_running_build_unit_and_the_caps(self):
        self.put('lib/lean/Submission/A.olean', b'a' * 10); self.put('lib/lean/Submission/B.olean', b'b' * 10)
        for state in ['active', 'activating', 'deactivating', '']:
            with self.subTest(state=state), self.assertRaises(RuntimeError):
                self.pack(state)
        self.assertFalse(self.packed_file().exists())
        # The raw cap counts the member sizes; the compressed cap the file. A refused pack leaves no file.
        size = len(subprocess.run(v.ZSTD_PACK, input=b'', capture_output=True, check=True).stdout)
        for name, value in [('BUILD_MAX_MEMBERS', 2), ('BUILD_MAX_RAW_BYTES', 19), ('BUILD_MAX_BYTES', size)]:
            with self.subTest(cap=name), patch.object(v, name, value), self.assertRaises(RuntimeError):
                self.pack()
            self.assertFalse(self.packed_file().exists())
        self.assertEqual(self.pack()['bytes'], 20)

    def test_pack_refuses_a_symlinked_build_folder(self):
        os.rmdir(self.build); os.symlink(self.tmp, self.build)
        with self.assertRaises(RuntimeError):
            self.pack()


class UnpackTests(Base):
    def packed(self):
        (self.art / 'build.log').write_text('log')
        self.put('lib/lean/Submission.olean', b'root')
        self.put('lib/lean/Submission/OAI/A.olean', b'a' * 3000, mtime_ns=1_700_000_001_000_000_001)
        self.put('ir/Submission/OAI/A.c', b'c')
        os.utime(self.build / 'lib/lean/Submission/OAI', ns=(1_600_000_000_000_000_007,) * 2)
        self.pack()
        before = self.tree()
        shutil.rmtree(self.build); self.build.mkdir()
        return before

    def test_round_trip_restores_files_modes_and_mtimes(self):
        before = self.packed()
        command = self.unpack()
        after = self.tree()
        for prefix in ['lib', 'lib/lean', 'ir']:
            self.assertTrue(after.pop(prefix)[0])
            before.pop(prefix)
        # The content and the mtimes come back; the modes are the fixed ones.
        self.assertEqual({k: (d, m, c) for k, (d, _, m, c) in after.items()}, {k: (d, m, c) for k, (d, _, m, c) in before.items()})
        self.assertEqual({mode for d, mode, _, _ in after.values()}, {'0o755', '0o644'})
        self.assertTrue(all(mode == ('0o755' if d else '0o644') for d, mode, _, _ in after.values()))
        self.assertEqual(after['lib/lean/Submission/OAI'][2], 1_600_000_000_000_000_007)
        data = v.receipt()
        self.assertEqual(data['unpack'], {'sha256': data['pack']['sha256'], 'members': 7, 'files': 3, 'bytes': 3005})
        self.assertEqual(data['build'], {'exit_code': 0})
        self.assertFalse((self.out / 'build.tar').exists())
        self.assertFalse(self.packed_file().exists())
        # LEAN_PATH record: our Lake config only, in the sandbox, before Comparator.
        lake = str(self.work / 'tools/elan/toolchains/leanprover--lean4---v4.34.1/bin/lake')
        command.assert_called_once_with(v.sandbox_args() + [lake, 'env', 'printenv', 'LEAN_PATH'], 'lean-path')
        self.assertEqual(data['lean_path'], ['/w/.lake/packages/mathlib/.lake/build/lib/lean', '/w/stage/.lake/build/lib/lean'])

    def test_fail_closed_before_any_write(self):
        self.packed()
        sha = hashlib.sha256(self.packed_file().read_bytes()).hexdigest()
        for kwargs in [dict(result='failure'), dict(result='cancelled'), dict(result=''), dict(sha=''), dict(sha=sha.upper()),
                       dict(sha=sha[:63]), dict(sha=sha + '0'), dict(sha='0' * 64)]:
            with self.subTest(**kwargs), self.assertRaises((RuntimeError, ValueError)):
                self.unpack(**{'sha': sha, **kwargs})
            self.assertEqual(os.listdir(self.build), [])
        # The record and the log of job 1 still reach the receipt; a log over 32 MB does not.
        self.assertEqual(v.receipt()['build'], {'exit_code': 0})
        self.assertEqual((self.art / 'build.log').read_text(), 'log')
        (self.art / 'build.log').unlink(); (self.out / 'build.log').write_bytes(b'x' * (32 * 1024**2 + 1))
        with self.assertRaises(RuntimeError):
            self.unpack(sha=sha, result='failure')
        self.assertFalse((self.art / 'build.log').exists())
        self.packed_file().unlink()
        with self.assertRaises(ValueError):
            self.unpack(sha=sha)
        self.assertEqual(os.listdir(self.build), [])

    def test_a_root_with_a_toolchain_module_name_is_refused(self):
        self.packed()
        for entry in ['Submission', 'Submission.olean', 'Submission.ilean']:
            with self.subTest(entry=entry):
                path = self.toolchain_lib / entry; path.write_text('')
                with patch.object(v, 'command') as command, self.assertRaises(ValueError):
                    self.unpack()
                path.unlink()
                command.assert_not_called()
                self.assertEqual(os.listdir(self.build), [])
        # Fail closed if the folder is missing.
        shutil.rmtree(self.toolchain_lib)
        with self.assertRaises(FileNotFoundError):
            self.unpack()
        self.assertEqual(os.listdir(self.build), [])

    def test_the_build_folder_must_be_empty(self):
        self.packed()
        (self.build / 'lib').mkdir()
        with self.assertRaises(RuntimeError):
            self.unpack()

    def write_tar(self, members):
        """members: (TarInfo, data) pairs. Our pack's headers unless a test changes them. Compressed as pack does."""
        self.out.mkdir(exist_ok=True)
        raw = io.BytesIO()
        with tarfile.open(fileobj=raw, mode='w', format=tarfile.PAX_FORMAT) as tar:
            for info, data in members:
                tar.addfile(info, io.BytesIO(data) if data is not None else None)
        self.packed_file().write_bytes(subprocess.run(v.ZSTD_PACK, input=raw.getvalue(), capture_output=True, check=True).stdout)

    def info(self, name, kind=tarfile.REGTYPE, data=b'x', **pax):
        info = tarfile.TarInfo(name); info.type = kind; info.mtime = 1
        info.size = len(data) if kind == tarfile.REGTYPE else 0
        info.pax_headers = {'mtime': '1.000000000', **pax}
        return info, (data if kind == tarfile.REGTYPE else None)

    def test_one_bad_member_rejects_the_whole_archive(self):
        good = [self.info('lib/lean/Submission', tarfile.DIRTYPE), self.info('lib/lean/Submission/A.olean')]
        self.write_tar(good); self.unpack()
        self.assertEqual(sorted(self.tree()), ['ir', 'lib', 'lib/lean', 'lib/lean/Submission', 'lib/lean/Submission/A.olean'])
        data = v.receipt(); data.pop('unpack'); v.save(data)
        def link(name, kind, target):
            info, _ = self.info(name, kind); info.linkname = target; info.size = 0
            return info, None
        bad = {'mathlib': self.info('lib/lean/Mathlib/Order/Basic.olean'), 'mathlib-dir': self.info('lib/lean/Mathlib', tarfile.DIRTYPE),
               'challenge': self.info('lib/lean/VerifierChallenge.olean'), 'challenge-ir': self.info('ir/VerifierChallenge.c'),
               'audit': self.info('lib/lean/VerifierAudit.olean'), 'init': self.info('lib/lean/Init/Prelude.olean'),
               'top': self.info('bin/x'), 'dotdot': self.info('lib/lean/Submission/../../../x.olean'),
               'dotdot-root': self.info('../lib/lean/Submission.olean'), 'absolute': self.info('/lib/lean/Submission.olean'),
               'symlink': link('lib/lean/Submission/L.olean', tarfile.SYMTYPE, '/etc/passwd'),
               'hardlink': link('lib/lean/Submission/H.olean', tarfile.LNKTYPE, 'lib/lean/Submission/A.olean'),
               'fifo': self.info('lib/lean/Submission/F', tarfile.FIFOTYPE), 'char': self.info('lib/lean/Submission/C', tarfile.CHRTYPE),
               'contiguous': self.info('lib/lean/Submission/K.olean', tarfile.CONTTYPE),
               'duplicate': self.info('lib/lean/Submission/A.olean'), 'no-mtime': None, 'float-mtime': self.info('lib/lean/Submission/M.olean', mtime='1.5'),
               'linkpath': self.info('lib/lean/Submission/P.olean', linkpath='/etc/passwd'),
               'sparse': self.info('lib/lean/Submission/S.olean', **{'GNU.sparse.map': '0,1'}),
               'non-utf8': self.info('lib/lean/Submission/\udcff.olean'),
               'shared-lib': self.info('lib/libleanshared.so'), 'shared-lib-lean': self.info('lib/lean/libleanshared.so'),
               'libc': self.info('lib/lean/libc.so.6'), 'dotdot-x': self.info('lib/lean/Submission/../x')}
        bad['no-mtime'] = self.info('lib/lean/Submission/N.olean'); bad['no-mtime'][0].pax_headers = {}
        for name, member in bad.items():
            with self.subTest(member=name):
                shutil.rmtree(self.build); self.build.mkdir()
                self.write_tar(good + [member])
                with self.assertRaises((ValueError, tarfile.TarError)):
                    self.unpack()
                self.assertEqual(os.listdir(self.build), [])
                self.assertNotIn('unpack', v.receipt())

    def test_caps(self):
        members = [self.info('lib/lean/Submission', tarfile.DIRTYPE), self.info('lib/lean/Submission/A.olean', data=b'a' * 10)]
        self.write_tar(members)
        size = self.packed_file().stat().st_size
        for name, value in [('BUILD_MAX_MEMBERS', 1), ('BUILD_MAX_RAW_BYTES', 9), ('BUILD_MAX_BYTES', size - 1)]:
            self.write_tar(members)  # A refused archive is used up: unpack removes the pack after its decompression.
            with self.subTest(cap=name), patch.object(v, name, value), self.assertRaises(ValueError):
                self.unpack()
            self.assertEqual(os.listdir(self.build), [])
            self.assertFalse((self.out / 'build.tar').exists())

    def test_a_decompression_bomb_stops_at_the_raw_cap(self):
        # 64 MiB of zeros compress to a few KiB; the stream stops long before the disk fills.
        bomb = subprocess.run(v.ZSTD_PACK, input=bytes(64 * 1024**2), capture_output=True, check=True).stdout
        self.out.mkdir(exist_ok=True); self.packed_file().write_bytes(bomb)
        with patch.object(v, 'BUILD_MAX_RAW_BYTES', 1024**2), patch.object(v, 'BUILD_MAX_MEMBERS', 10), \
                self.assertRaises(ValueError):
            self.unpack()
        self.assertFalse((self.out / 'build.tar').exists())
        self.assertEqual(os.listdir(self.build), [])
        # Not zstd at all.
        self.packed_file().write_bytes(b'not a zstd frame')
        with self.assertRaises(ValueError):
            self.unpack()
        self.assertFalse((self.out / 'build.tar').exists())

    def test_unpack_never_uses_extractall(self):
        source = (ROOT / 'scripts/verifier.py').read_text()
        self.assertNotIn('extractall', source)
        self.assertNotIn('.extract(', source)


class BuildTests(Base):
    def test_inside_build_runs_the_real_lake_once(self):
        v.write_json(self.work / 'control/request.json', {'request': {'lean_toolchain': 'leanprover/lean4:v4.34.1'},
                                                          'profile': {'solution_module': 'Submission'}})
        challenge = self.work / 'stage/.lake/build/lib/lean/VerifierChallenge.olean'
        challenge.parent.mkdir(parents=True); challenge.write_text('stale')
        calls = []
        class Exec(Exception): pass
        def execve(path, args, env):
            calls.append((path, args, env['LEAN_NUM_THREADS'])); raise Exec()
        for jobs in ['4', '2']:
            with patch.object(sys, 'argv', ['inside.py', str(self.work), 'build', jobs]), \
                 patch.object(os, 'execve', side_effect=execve), self.assertRaises(Exec):
                runpy.run_path(str(ROOT / 'scripts/inside.py'), run_name='__main__')
        lake = str(self.work / 'tools/elan/toolchains/leanprover--lean4---v4.34.1/bin/lake')
        self.assertEqual(calls, [(lake, [lake, 'build', 'Submission'], '4'), (lake, [lake, 'build', 'Submission'], '2')])
        self.assertFalse(challenge.exists())
        # The Lake worker count comes only from the controller, and only 1 to 4.
        for argv in [['build'], ['build', '0'], ['build', '5'], ['build', '2 '], ['build', '2', 'x']]:
            with patch.object(sys, 'argv', ['inside.py', str(self.work), *argv]), \
                 patch.object(os, 'execve', side_effect=execve), self.assertRaises(ValueError):
                runpy.run_path(str(ROOT / 'scripts/inside.py'), run_name='__main__')
        self.assertEqual(len(calls), 2)

    def test_inside_every_phase_reaches_execve(self):
        # verifier#188 (AnanasClassic; test idea from darkhipo's PR #189): 195060b2 set LEAN_NUM_THREADS only in
        # the build branch, so the audit raised NameError before its execve. The build test above was the only
        # unit test of inside.py; the other phases ran only in real sandbox runs. Run every phase here.
        v.write_json(self.work / 'control/request.json', {'request': {'lean_toolchain': 'leanprover/lean4:v4.34.1'},
                                                          'profile': {'solution_module': 'Submission'}})
        lake = str(self.work / 'tools/elan/toolchains/leanprover--lean4---v4.34.1/bin/lake')
        comparator = str(self.work / 'tools/comparator/.lake/build/bin/comparator')
        expected = {
            'audit': (lake, [lake, 'env', 'lean', str(self.work / 'stage/VerifierAudit.lean')]),
            'lean': (lake, [lake, 'env', '/usr/bin/python3', str(self.work / 'control/inside.py'), str(self.work), 'lean-exec']),
            'nanoda': (lake, [lake, 'env', '/usr/bin/python3', str(self.work / 'control/inside.py'), str(self.work), 'nanoda-exec']),
            'lean-exec': (comparator, [comparator, str(self.work / 'control/lean.json')]),
            'nanoda-exec': (comparator, [comparator, str(self.work / 'control/nanoda.json')]),
        }
        class Exec(Exception): pass
        for phase, (path, args) in expected.items():
            calls = []
            def execve(p, a, env):
                calls.append((p, a, env['LEAN_NUM_THREADS'], env.get('PATH', ''))); raise Exec()
            with self.subTest(phase=phase), patch.object(sys, 'argv', ['inside.py', str(self.work), phase]), \
                 patch.object(os, 'execve', side_effect=execve), self.assertRaises(Exec):
                runpy.run_path(str(ROOT / 'scripts/inside.py'), run_name='__main__')
            self.assertEqual(calls[0][:3], (path, args, '4'), phase)
            if phase.endswith('-exec'):
                self.assertTrue(calls[0][3].startswith(str(self.work / 'control/bin') + ':'), phase)
        with patch.object(sys, 'argv', ['inside.py', str(self.work), 'audit-exec']), \
             patch.object(os, 'execve', side_effect=AssertionError('no execve')), self.assertRaises(ValueError):
            runpy.run_path(str(ROOT / 'scripts/inside.py'), run_name='__main__')


try:
    import yaml
except ImportError:
    yaml = None


@unittest.skipIf(yaml is None, 'PyYAML is not installed')
class WorkflowTests(unittest.TestCase):
    def load(self, name):
        return yaml.safe_load((ROOT / '.github/workflows' / name).read_text())

    def test_the_split_input_reaches_the_check(self):
        check = self.load('submission-check.yml')
        self.assertEqual(check[True]['workflow_call']['inputs']['split'], {'required': False, 'type': 'boolean', 'default': False})
        self.assertEqual(self.load('submissions.yml')['jobs']['check']['with']['split'], '${{ matrix.split == true }}')

    def test_build_job(self):
        jobs = self.load('submission-check.yml')['jobs']
        self.assertEqual(list(jobs), ['build', 'verify', 'pr_verify'])
        build, verify = jobs['build'], jobs['verify']
        self.assertEqual(build['if'], "inputs.split && inputs.route == 'issue'")
        self.assertEqual(build['permissions'], {'contents': 'read', 'issues': 'read'})
        self.assertEqual(build['timeout-minutes'], 350)
        self.assertEqual(build['outputs'], {'proceed': '${{ steps.gate.outputs.proceed }}',
                                            'build_sha256': '${{ steps.pack.outputs.build_sha256 }}'})
        runs = [step.get('run') or step['uses'].split('@')[0] for step in build['steps']]
        self.assertEqual(runs, ['actions/checkout', 'actions/download-artifact', 'python3 scripts/submissions.py materialize',
                                'python3 scripts/submissions.py preflight', 'python3 -m unittest discover -s tests -v',
                                'python3 scripts/verifier.py prepare', 'python3 scripts/verifier.py setup',
                                'python3 scripts/verifier.py build', 'python3 scripts/verifier.py pack', 'actions/upload-artifact'])
        self.assertEqual(build['steps'][0]['with'], {'ref': '${{ github.sha }}', 'persist-credentials': False})
        pack, upload = build['steps'][8], build['steps'][9]
        self.assertEqual((pack['id'], pack['if']), ('pack', "${{ !cancelled() && steps.prepare.outcome == 'success' }}"))
        self.assertEqual(upload['if'], pack['if'])
        self.assertEqual(upload['with'], {'name': 'verifier-build-${{ github.run_id }}-${{ github.run_attempt }}-${{ inputs.issue_number }}',
                                          'path': 'build-artifact/', 'if-no-files-found': 'error', 'retention-days': 1})
        # The same action pins as the other jobs.
        pins = {step['uses'] for step in verify['steps'] if 'uses' in step}
        self.assertTrue({step['uses'] for step in build['steps'] if 'uses' in step} <= pins)

    def test_verify_job(self):
        jobs = self.load('submission-check.yml')['jobs']
        verify = jobs['verify']
        self.assertEqual(verify['needs'], 'build')
        # A skipped build skips its dependents unless a status function is used. Not always(): a cancel stops the run.
        self.assertEqual(verify['if'], "${{ !cancelled() && inputs.route == 'issue' }}")
        steps = verify['steps']
        runs = [step.get('run') or step['uses'].split('@')[0] for step in steps]
        at = runs.index('python3 scripts/verifier.py setup')
        self.assertEqual(runs[at + 1:at + 4], ['actions/download-artifact', 'python3 scripts/verifier.py unpack',
                                               'python3 scripts/verifier.py verify_lean'])
        download, unpack = steps[at + 1], steps[at + 2]
        self.assertEqual(download['with'], {'name': 'verifier-build-${{ github.run_id }}-${{ github.run_attempt }}-${{ inputs.issue_number }}',
                                            'path': 'build-artifact'})
        self.assertEqual(unpack['env'], {'BOS_BUILD_RESULT': '${{ needs.build.result }}',
                                         'BOS_BUILD_SHA256': '${{ needs.build.outputs.build_sha256 }}'})
        for step in [download, unpack]:
            self.assertEqual(step['if'], "inputs.split && steps.gate.outputs.proceed == 'true'")
        gate = next(step for step in steps if step.get('id') == 'gate')
        self.assertEqual(gate['env'], {'GH_TOKEN': '${{ github.token }}', 'BOS_BUILD_PROCEED': '${{ needs.build.outputs.proceed }}'})
        build_gate = next(step for step in jobs['build']['steps'] if step.get('id') == 'gate')
        self.assertEqual(build_gate['env'], {'GH_TOKEN': '${{ github.token }}'})
        # Both issue jobs set BOS_SPLIT for the gate and prepare (verifier.chain_targets); pr_verify never does.
        for name in ['build', 'verify']:
            self.assertEqual(jobs[name]['env']['BOS_SPLIT'], '${{ inputs.split }}')
        self.assertNotIn('BOS_SPLIT', jobs['pr_verify']['env'])
        # The unit tests of both issue jobs run without it: #99's rerun 41494392206 failed there, 3 errors (2026-11-02).
        for name in ['build', 'verify']:
            tests = next(step for step in jobs[name]['steps'] if step.get('run') == 'python3 -m unittest discover -s tests -v')
            self.assertEqual(tests['env'], {'BOS_SPLIT': ''})
        # Without split, the steps are the steps of 255e338, and the report job is unchanged.
        plain = [r for r, step in zip(runs, steps) if 'inputs.split' not in str(step.get('if'))]
        self.assertEqual(plain, ['actions/checkout', 'actions/download-artifact', 'python3 scripts/submissions.py materialize',
                                 'python3 scripts/submissions.py preflight', 'python3 -m unittest discover -s tests -v',
                                 'python3 scripts/verifier.py prepare', 'python3 scripts/verifier.py setup',
                                 'python3 scripts/verifier.py verify_lean', 'python3 scripts/verifier.py finalize',
                                 'actions/upload-artifact', 'python3 scripts/verifier.py verify_nanoda',
                                 'python3 scripts/verifier.py finalize', 'actions/upload-artifact'])
        self.assertNotIn('needs', jobs['pr_verify'])

    def test_each_issue_of_a_matrix_gets_its_report(self):
        # Run 42648121034 (2026-11-09) checked #187 and #190 in one matrix. The report job inside the reusable workflow
        # was never created for #190 (no error; the run ended failure), so #190 got no verdict. The report is now a plain
        # matrix job of the caller, over the same matrix, after every check leg: one report per selected issue.
        caller = self.load('submissions.yml')['jobs']
        check, report = caller['check'], caller['report']
        self.assertEqual(report['needs'], ['select', 'check'])
        self.assertEqual(report['if'], "${{ always() && needs.select.outputs.selected == 'true' }}")
        self.assertEqual(report['strategy'], check['strategy'])
        self.assertNotIn('uses', report)
        self.assertEqual(report['permissions'], {'contents': 'read', 'actions': 'read', 'issues': 'write'})
        self.assertEqual(report['env'], {'ISSUE_NUMBER': '${{ matrix.issue_number }}'})
        # Issue write moves from the check legs (which run the submitted Lean code) to the report job only.
        self.assertEqual(check['permissions']['issues'], 'read')
        for name, job in self.load('submission-check.yml')['jobs'].items():
            self.assertNotEqual(job.get('permissions', {}).get('issues'), 'write', name)
        steps = report['steps']
        self.assertTrue(all(step['if'] == "matrix.route == 'issue'" for step in steps))
        runs = [step.get('run') or step['uses'].split('@')[0] for step in steps]
        self.assertEqual(runs, ['actions/checkout', 'actions/download-artifact', 'python3 scripts/submissions.py materialize',
                                'actions/download-artifact', 'python3 scripts/submissions.py report', 'actions/upload-artifact',
                                'python3 scripts/submissions.py publish'])
        self.assertEqual(steps[0]['with'], {'ref': '${{ github.sha }}', 'persist-credentials': False})
        # The artifact names of the check legs and of the site import are unchanged.
        self.assertEqual(steps[1]['with']['name'], 'direct-requests-${{ github.run_id }}-${{ github.run_attempt }}')
        self.assertEqual(steps[3]['with']['name'], 'verifier-receipt-and-logs-${{ github.run_id }}-${{ github.run_attempt }}-${{ matrix.issue_number }}')
        self.assertEqual(steps[5]['with']['name'], 'direct-submission-${{ github.run_id }}-${{ github.run_attempt }}-${{ matrix.issue_number }}')
        verify = self.load('submission-check.yml')['jobs']['verify']
        uploads = [step['with']['name'] for step in verify['steps'] if step.get('uses', '').startswith('actions/upload-artifact')]
        self.assertIn('verifier-receipt-and-logs-${{ github.run_id }}-${{ github.run_attempt }}-${{ inputs.issue_number }}', uploads)
        # The same action pins as the check jobs.
        pins = {step['uses'] for step in verify['steps'] if 'uses' in step}
        self.assertTrue({step['uses'] for step in steps if 'uses' in step} <= pins)


class SuiteUnderSplitTests(unittest.TestCase):
    # The suite must pass with the split job's environment too, not only with the step's clear (run 41494392206).
    @unittest.skipIf(os.environ.get('BOS_SUITE_UNDER_SPLIT') == '1', 'the inner run')
    def test_the_suite_passes_with_bos_split_true(self):
        env = dict(os.environ, BOS_SPLIT='true', BOS_SUITE_UNDER_SPLIT='1')
        run = subprocess.run([sys.executable, '-m', 'unittest', 'discover', '-s', 'tests'], cwd=ROOT, env=env,
                             capture_output=True, text=True, timeout=300)
        self.assertEqual(run.returncode, 0, run.stderr[-4000:])


if __name__ == '__main__':
    unittest.main()
