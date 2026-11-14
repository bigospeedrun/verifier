"""The check chain (runner github-chain, scripts/chain.py, docs/execution.md, Check chain): caps, the job outputs of each
chain job, the pack pick, the coverage rule of the final job, the final receipt, and the workflow graph."""
import hashlib
import json
import os
from pathlib import Path
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

import yaml

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import chain
import submissions as s
import verdicts
import verifier as v

H0 = chain.HASH_START
SHA = 'a' * 64


def seg(start, to, status='stopped', hash_from=None, hash_to=None, **extra):
    """A chain_segment record of one job, with Comparator's segment receipt inside."""
    receipt = {'schema': 'bos-segment-v1', 'status': status, 'from': start, 'to': to,
               'hash_from': hash_from or (H0 if start == 0 else f'{start:016x}'), 'hash_to': hash_to or f'{to:016x}',
               'compare': 'passed' if start == 0 else 'not_run', 'complete': status == 'passed',
               'quot_post_check': 'passed' if status == 'passed' else 'not_run'}
    receipt.update(extra)
    return {'export_sha256': SHA, 'from': start, 'status': 'linked', 'segment': receipt}


class CapTests(unittest.TestCase):
    def test_defaults_and_limits(self):
        self.assertEqual(chain.caps({}), {'max_build_jobs': 1, 'max_check_jobs': 1, 'max_hours': 30, 'segment_parts': 0})
        self.assertEqual(chain.caps({'chain': {'max_build_jobs': 4, 'max_check_jobs': 4, 'max_hours': 30, 'segment_parts': 5}}),
                         {'max_build_jobs': 4, 'max_check_jobs': 4, 'max_hours': 30, 'segment_parts': 5})
        for bad in [{'max_build_jobs': 5}, {'max_check_jobs': 0}, {'max_hours': 31}, {'max_hours': 2.5},
                    {'max_build_jobs': '2'}, {'max_build_jobs': True}, {'other': 1}, [],
                    {'segment_parts': 6}, {'segment_parts': -1}, {'segment_parts': True}, {'segment_parts': '3'}]:
            with self.subTest(chain=bad), self.assertRaises(ValueError):
                chain.caps({'chain': bad})


class CoverageTests(unittest.TestCase):
    def test_contiguous_segments_pass(self):
        segments = [seg(0, 100), seg(100, 250), seg(250, 300, 'passed')]
        self.assertEqual(chain.coverage(segments, SHA), {'status': 'passed', 'reason': 'segmented_comparator_acceptance',
                                                         'declarations': 300, 'segments': 3})
        self.assertEqual(chain.coverage([seg(0, 300, 'passed')], SHA)['status'], 'passed')

    def test_a_job_without_time_for_a_segment_is_skipped(self):
        not_run = {'export_sha256': SHA, 'from': 100, 'status': 'not_run', 'expected_hash_from': f'{100:016x}'}
        self.assertEqual(chain.coverage([seg(0, 100), not_run, seg(100, 300, 'passed')], SHA)['status'], 'passed')
        export_not_run = {'export_sha256': SHA, 'from': 0, 'status': 'not_run', 'expected_hash_from': H0}
        self.assertEqual(chain.coverage([export_not_run, seg(0, 300, 'passed')], SHA)['status'], 'passed')

    def test_any_gap_overlap_or_other_export_is_not_a_pass(self):
        cases = {
            'gap': [seg(0, 100), seg(101, 300, 'passed', hash_from=f'{100:016x}')],
            'overlap': [seg(0, 100), seg(99, 300, 'passed', hash_from=f'{100:016x}')],
            'other hash': [seg(0, 100), seg(100, 300, 'passed', hash_from='f' * 16)],
            'other export': [seg(0, 100), dict(seg(100, 300, 'passed'), export_sha256='b' * 64)],
            'no compare at 0': [seg(0, 300, 'passed', compare='not_run')],
            'no progress': [seg(0, 0)],
            'no quotient check': [seg(0, 300, 'passed', quot_post_check='not_run')],
            'not complete': [seg(0, 300, 'passed', complete=False)],
            'passed before the end': [seg(0, 300, 'passed'), seg(300, 300, 'passed')],
            'record from differs': [dict(seg(0, 100), **{'from': 5}), seg(100, 300, 'passed')],
            'not linked': [seg(0, 100), {'export_sha256': SHA, 'from': 100, 'status': 'unlinked'}],
            'unknown status': [seg(0, 300, 'odd')],
        }
        for name, segments in cases.items():
            with self.subTest(name):
                result = chain.coverage(segments, SHA)
                self.assertNotEqual(result['status'], 'passed')
                self.assertEqual(result, {'status': 'incomplete', 'reason': 'chain_coverage'})

    def test_rejection_mismatch_and_caps(self):
        self.assertEqual(chain.coverage([seg(0, 100), seg(100, 140, 'rejected', error='kernel')], SHA),
                         {'status': 'rejected', 'reason': 'lean_kernel_rejection', 'segment': 1, 'at': 140})
        mismatch = {'export_sha256': SHA, 'from': 0, 'status': 'linked', 'segment': {
            'schema': 'bos-segment-v1', 'status': 'mismatch', 'from': 0, 'to': 0,
            'error': "Challenge and solution theorem statement do not match: 'Race.bound'"}}
        self.assertEqual(chain.coverage([mismatch], SHA), {'status': 'pending_review', 'reason': 'statement_mismatch',
                                                           'theorem': 'Race.bound'})
        mismatch['segment']['error'] = "Const does not match between challenge and target 'Race.f'"
        self.assertEqual(chain.coverage([mismatch], SHA)['mismatch'], 'definition')
        mismatch['segment']['error'] = 'something else'
        self.assertEqual(chain.coverage([mismatch], SHA), {'status': 'pending_review', 'reason': 'ambiguous_failure'})
        # A mismatch is only possible at 0.
        late = dict(mismatch, **{'from': 100}); late['segment'] = dict(mismatch['segment'], **{'from': 100})
        self.assertEqual(chain.coverage([seg(0, 100), late], SHA)['reason'], 'chain_coverage')
        # The last job stopped: the cap ended the chain. A killed unit keeps its reason.
        self.assertEqual(chain.coverage([seg(0, 100), seg(100, 200)], SHA), {'status': 'incomplete', 'reason': 'check_chain_cap'})
        killed = {'export_sha256': SHA, 'from': 100, 'status': 'incomplete', 'reason': 'out_of_memory'}
        self.assertEqual(chain.coverage([seg(0, 100), killed], SHA), {'status': 'incomplete', 'reason': 'out_of_memory'})
        self.assertEqual(chain.coverage([], SHA), {'status': 'incomplete', 'reason': 'check_chain_cap'})


class LegBase(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory(); self.addCleanup(tmp.cleanup)
        self.tmp = Path(tmp.name)
        self.art = self.tmp / 'artifacts'
        for target, value in [('ART', self.art), ('WORK', self.tmp / 'work')]:
            p = patch.object(v, target, value); p.start(); self.addCleanup(p.stop)
        self.output = self.tmp / 'out'
        self.profile = {'runner': 'github-chain', 'chain': {'max_build_jobs': 3, 'max_check_jobs': 2, 'max_hours': 30}}

    def leg(self, name, data, started=None):
        self.art.mkdir(exist_ok=True)
        v.save(data)
        self.output.write_text('')
        env = {'BOS_CHAIN_LEG': name, 'GITHUB_OUTPUT': str(self.output),
               'BOS_CHAIN_STARTED': repr(started if started is not None else time.time() - 3600)}
        with patch.dict(os.environ, env):
            chain.leg()
        out = dict(line.split('=', 1) for line in self.output.read_text().splitlines())
        self.assertEqual(out['leg_sha256'], v.digest(self.art / 'receipt.json'))
        return out, v.receipt()['chain_leg']


class BuildLegTests(LegBase):
    def data(self, result, code, lake_jobs=1, pack='p' * 64, unpack=None):
        data = {'status': 'prepared', 'started_unix': time.time() - 600, 'profile': self.profile,
                'build': {'attempts': [{'lake_jobs': lake_jobs, 'exit_code': code, 'systemd_result': result, 'guard_stop': None}]},
                'pack': {'sha256': pack}}
        if unpack:
            data['unpack'] = {'sha256': unpack}
        return data

    def test_done_continue_and_stop(self):
        out, state = self.leg('build1', self.data('success', 0))
        self.assertEqual((out['done'], out['next'], state['build']), ('true', 'false', 'done'))
        out, state = self.leg('build1', self.data('timeout', 1))
        self.assertEqual((out['done'], out['next'], state['build']), ('false', 'true', 'continue'))
        # build1 passes on its own start; a later job passes on the start it got.
        self.assertAlmostEqual(float(out['chain_started']), v.receipt()['started_unix'], places=3)
        started = round(time.time()) - 7200 + 0.5
        out, _ = self.leg('build2', self.data('timeout', 1), started=started)
        self.assertEqual(out['chain_started'], repr(started))
        # The deadline cut the oom back-off: continue. An oom-kill at 1 worker: stop.
        out, state = self.leg('build1', self.data('oom-kill', 137, lake_jobs=2))
        self.assertEqual((out['next'], state['build']), ('true', 'continue'))
        out, state = self.leg('build1', self.data('oom-kill', 137, lake_jobs=1))
        self.assertEqual((out['next'], state['outcome']), ('false', {'status': 'incomplete', 'reason': 'out_of_memory'}))
        # A Lean error: the build log decides, as in kernel_outcome.
        self.art.mkdir(exist_ok=True)
        (self.art / 'build.log').write_text('error: Submission/A.lean:3:4: unknown identifier \'x\'\nerror: build failed\n')
        out, state = self.leg('build1', self.data('exit-code', 1))
        self.assertEqual(out['next'], 'false')
        self.assertEqual(state['outcome']['reason'], 'lean_compile_error')

    def test_caps_and_no_new_pack(self):
        out, state = self.leg('build3', self.data('timeout', 1, unpack='u' * 64))
        self.assertEqual((out['next'], state['outcome']), ('false', {'status': 'incomplete', 'reason': 'build_chain_cap'}))
        out, state = self.leg('build2', self.data('timeout', 1, unpack='u' * 64), started=time.time() - 31 * 3600)
        self.assertEqual((out['next'], state['outcome']['reason']), ('false', 'build_chain_cap'))
        out, state = self.leg('build2', self.data('timeout', 1, pack='u' * 64, unpack='u' * 64))
        self.assertEqual((out['next'], out['done'], state['outcome']['reason']), ('false', 'false', 'build_not_run'))
        out, _ = self.leg('build2', self.data('timeout', 1, pack='', unpack='u' * 64))
        self.assertEqual(out['next'], 'false')
        # A build that ends after max_hours starts no export job (Integrations N1).
        out, state = self.leg('build2', self.data('success', 0, unpack='u' * 64), started=time.time() - 30 * 3600 - 1)
        self.assertEqual((out['done'], out['next'], state['outcome']), ('false', 'false', {'status': 'incomplete', 'reason': 'build_chain_cap'}))
        out, _ = self.leg('build2', self.data('success', 0, unpack='u' * 64), started=time.time() - 29 * 3600)
        self.assertEqual(out['done'], 'true')

    def test_bad_inputs_stop_the_chain(self):
        for started in ['', 'x', '1e9', '-1']:
            with self.subTest(started=started), patch.dict(os.environ, {'BOS_CHAIN_STARTED': started}):
                self.art.mkdir(exist_ok=True); v.save(self.data('timeout', 1)); self.output.write_text('')
                with patch.dict(os.environ, {'BOS_CHAIN_LEG': 'build2', 'GITHUB_OUTPUT': str(self.output)}):
                    chain.leg()
                out = dict(line.split('=', 1) for line in self.output.read_text().splitlines())
                self.assertEqual(out['next'], 'false')
                self.assertIn('error', v.receipt()['chain_leg'])
        with patch.dict(os.environ, {'BOS_CHAIN_LEG': 'build9'}), self.assertRaises(ValueError):
            chain.leg()
        # No receipt (the gate stopped build1): a setup_failed receipt, no next.
        self.art.mkdir(exist_ok=True); (self.art / 'receipt.json').unlink(missing_ok=True); self.output.write_text('')
        with patch.dict(os.environ, {'BOS_CHAIN_LEG': 'build1', 'GITHUB_OUTPUT': str(self.output)}):
            chain.leg()
        self.assertIn('next=false', self.output.read_text())
        self.assertEqual(v.receipt()['status'], 'setup_failed')


class CheckLegTests(LegBase):
    def data(self, record, files=True):
        data = {'status': 'chain_export', 'started_unix': time.time() - 600, 'profile': self.profile, 'chain_segment': record}
        if files:
            data['chain_export'] = {'files': {'solution': {'sha256': SHA}, 'challenge': {'sha256': 'c' * 64}}}
        return data

    def test_export_and_check_outputs(self):
        out, _ = self.leg('export', self.data(seg(0, 100)))
        self.assertEqual({k: out[k] for k in ['next', 'check_from', 'hash_from', 'export_sha256', 'challenge_sha256']},
                         {'next': 'true', 'check_from': '100', 'hash_from': f'{100:016x}', 'export_sha256': SHA,
                          'challenge_sha256': 'c' * 64})
        out, _ = self.leg('check1', self.data(seg(100, 200)))
        self.assertEqual((out['next'], out['check_from']), ('true', '200'))
        self.assertNotIn('export_sha256', out)
        # max_check_jobs 2: check2 is the last one.
        out, state = self.leg('check2', self.data(seg(200, 300)))
        self.assertEqual((out['next'], state['outcome']), ('false', {'status': 'incomplete', 'reason': 'check_chain_cap'}))
        self.assertIn('/', state['disk_free_bytes'])  # The runner disk at the end of each job.
        # No time for a segment: the next job starts at the same place.
        not_run = {'export_sha256': SHA, 'from': 0, 'status': 'not_run', 'expected_hash_from': H0}
        out, _ = self.leg('export', self.data(not_run))
        self.assertEqual((out['next'], out['check_from'], out['hash_from']), ('true', '0', H0))

    def test_no_next_after_the_end_or_a_failure(self):
        for record in [seg(0, 300, 'passed'), seg(0, 10, 'rejected'), dict(seg(0, 100), status='unlinked'),
                       {'export_sha256': SHA, 'from': 0, 'status': 'incomplete', 'reason': 'timeout'}, None]:
            with self.subTest(record=record):
                out, _ = self.leg('check1', self.data(record))
                self.assertEqual(out['next'], 'false')
        out, _ = self.leg('export', self.data(seg(0, 100)), started=time.time() - 30 * 3600 - 1)
        self.assertEqual(out['next'], 'false')

    def test_a_bad_stop_point_is_not_written_as_an_output(self):
        for bad in [{'to': '100'}, {'to': -1}, {'to': True}, {'hash_to': 'x\nnext=true'}, {'hash_to': 'F' * 16}]:
            with self.subTest(bad=bad):
                record = seg(0, 100)
                record['segment'].update(bad)
                out, state = self.leg('export', self.data(record))
                self.assertEqual(out['next'], 'false')
                self.assertNotIn('check_from', out)
                self.assertIn('error', state)


class PickTests(unittest.TestCase):
    def pick(self, needs):
        tmp = tempfile.NamedTemporaryFile('w+', delete=False); tmp.close(); self.addCleanup(os.unlink, tmp.name)
        with patch.dict(os.environ, {'BOS_CHAIN_NEEDS': json.dumps(needs), 'GITHUB_OUTPUT': tmp.name}):
            chain.pick()
        return dict(line.split('=', 1) for line in Path(tmp.name).read_text().splitlines())

    def job(self, done, result='success', sha=SHA, record='d' * 64):
        return {'result': result, 'outputs': {'done': 'true' if done else 'false', 'build_sha256': sha,
                                              'build_record_sha256': record}}

    def test_the_last_build_job_is_picked(self):
        skipped = {'result': 'skipped', 'outputs': {}}
        needs = {'chain_build1': self.job(False), 'chain_build2': self.job(True, sha='b' * 64),
                 'chain_build3': skipped, 'chain_build4': skipped}
        self.assertEqual(self.pick(needs), {'leg': 'build2', 'build_sha256': 'b' * 64, 'build_record_sha256': 'd' * 64,
                                            'result': 'success'})
        self.assertEqual(self.pick({'chain_build1': self.job(True)})['leg'], 'build1')

    def test_refusals(self):
        skipped = {'result': 'skipped', 'outputs': {}}
        for needs in [{}, {'chain_build1': skipped, 'chain_build2': self.job(True)},
                      {'chain_build1': self.job(True), 'chain_build2': self.job(True)},
                      {'chain_build1': self.job(False)}, {'chain_build1': self.job(True, sha='x')},
                      {'chain_build1': self.job(True, record='')},
                      {'chain_build1': self.job(False), 'chain_build2': skipped, 'chain_build3': self.job(True)}]:
            with self.subTest(needs=needs), self.assertRaises(ValueError):
                self.pick(needs)


class FinalTests(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory(); self.addCleanup(tmp.cleanup)
        self.tmp = Path(tmp.name)
        self.art = self.tmp / 'artifacts'
        for target, value in [('ART', self.art), ('ROOT', self.tmp)]:
            p = patch.object(v, target, value); p.start(); self.addCleanup(p.stop)
        env = patch.dict(os.environ, {'GITHUB_RUN_ID': '7', 'GITHUB_RUN_ATTEMPT': '1', 'ISSUE_NUMBER': '42',
                                      'GITHUB_REPOSITORY': 'bigospeedrun/verifier', 'GITHUB_SHA': 'e' * 40}); env.start()
        self.addCleanup(env.stop)
        self.needs = {}

    def put(self, name, receipt, result='success', pin=True, gate=None, run='7', commit='e' * 40):
        folder = self.tmp / 'chain-legs' / f'chain-leg-7-1-42-{name}'
        folder.mkdir(parents=True)
        receipt = {'run_url': f'https://github.com/bigospeedrun/verifier/actions/runs/{run}', 'verifier_commit': commit, **receipt}
        if gate:
            (folder / 'gate.json').write_text(json.dumps(gate))
            receipt['chain_leg'] = {**receipt.get('chain_leg', {}), 'gate_sha256': v.digest(folder / 'gate.json')}
        (folder / 'receipt.json').write_text(json.dumps(receipt))
        sha = hashlib.sha256((folder / 'receipt.json').read_bytes()).hexdigest() if pin else '0' * 64
        self.needs['chain_' + name] = {'result': result, 'outputs': {'leg_sha256': sha}}

    def final(self):
        for name in chain.LEGS:
            self.needs.setdefault('chain_' + name, {'result': 'skipped', 'outputs': {}})
        with patch.dict(os.environ, {'BOS_CHAIN_NEEDS': json.dumps(self.needs)}):
            chain.final()
        return v.receipt() if (self.art / 'receipt.json').exists() else None

    def base(self, **extra):
        data = {'schema_version': 1, 'status': 'chain_export', 'request': {'commit': 'c' * 40}, 'theorem_names': ['Race.bound'],
                'kernels': {'lean': {'status': 'not_started'}, 'nanoda': {'status': 'not_started'}},
                'axiom_audit': {'status': 'passed', 'reported_axioms': {'Race.bound': ['propext']}},
                'chain_export': {'status': 'passed', 'reason': 'comparator_acceptance', 'files': {'solution': {'sha256': SHA}}}}
        data.update(extra)
        return data

    def test_a_full_chain_passes_and_admits(self):
        self.put('build1', {'status': 'prepared', 'build': {'attempts': [{'lake_jobs': 1}]}, 'chain_leg': {'build': 'continue'}})
        self.put('build2', {'status': 'prepared', 'build': {'attempts': [{'lake_jobs': 1, 'exit_code': 0}]}, 'chain_leg': {'build': 'done'}})
        self.put('export', self.base(chain_segment=seg(0, 100)), gate={'status': 'proceed'})
        self.put('check1', {'chain_segment': seg(100, 200)})
        self.put('check2', {'chain_segment': seg(200, 260, 'passed')})
        data = self.final()
        lean = data['kernels']['lean']
        self.assertEqual((lean['status'], lean['reason'], lean['declarations'], lean['segments']),
                         ('passed', 'segmented_comparator_acceptance', 260, 3))
        self.assertEqual(data['kernels']['nanoda'], {'status': 'incomplete', 'reason': 'not_run_chain'})
        self.assertEqual(data['status'], 'passed')
        self.assertEqual([x['leg'] for x in data['chain']['legs']], ['build1', 'build2', 'export', 'check1', 'check2'])
        self.assertEqual(data['build'], {'attempts': [{'lake_jobs': 1, 'exit_code': 0}]})
        self.assertEqual(json.loads((self.art / 'gate.json').read_text()), {'status': 'proceed'})
        for key in ['chain_segment', 'chain_leg', 'error']:
            self.assertNotIn(key, data)
        # The verdict rule admits it (finalize then writes theorems and runs receipt_status).
        data['theorems'] = {'Race.bound': {'lean_kernel': 'passed', 'nanoda_kernel': 'incomplete',
                                           'reported_axioms': ['propext']}}
        self.assertEqual(verdicts.admission(data, ['Race.bound']), ('passed', 'lean_and_axiom_passed_nanoda_incomplete'))

    def test_a_receipt_that_does_not_match_its_pin_is_not_a_pass(self):
        self.put('build1', {'status': 'prepared', 'chain_leg': {'build': 'done'}})
        self.put('export', self.base(chain_segment=seg(0, 100)))
        self.put('check1', {'chain_segment': seg(100, 200, 'passed')}, pin=False)
        data = self.final()
        self.assertEqual(data['kernels']['lean'], {'status': 'incomplete', 'reason': 'chain_coverage',
                                                   'segments_detail': data['kernels']['lean']['segments_detail']})
        self.assertEqual(data['status'], 'not_verified')
        # A missing build receipt, too.
        self.setUp()
        self.put('build1', {'status': 'prepared'}, pin=False)
        self.put('export', self.base(chain_segment=seg(0, 100, 'passed')))
        self.assertEqual(self.final()['kernels']['lean']['reason'], 'chain_coverage')

    def test_only_receipts_of_this_run_and_commit_count(self):
        for kwargs in [{'run': '8'}, {'commit': 'f' * 40}]:
            with self.subTest(**kwargs):
                self.setUp()
                self.put('build1', {'status': 'prepared', 'chain_leg': {'build': 'done'}})
                self.put('export', self.base(chain_segment=seg(0, 100)))
                self.put('check1', {'chain_segment': seg(100, 200, 'passed')}, **kwargs)
                data = self.final()
                self.assertEqual(data['kernels']['lean']['reason'], 'chain_coverage')
                self.assertEqual(data['status'], 'not_verified')

    def test_a_capped_chain_is_incomplete_not_a_rejection(self):
        self.put('build1', {'status': 'prepared', 'chain_leg': {'build': 'done'}})
        self.put('export', self.base(chain_segment=seg(0, 100)))
        self.put('check1', {'chain_segment': seg(100, 200), 'chain_leg': {'outcome': {'status': 'incomplete', 'reason': 'check_chain_cap'}}})
        data = self.final()
        self.assertEqual({k: data['kernels']['lean'][k] for k in ['status', 'reason']}, {'status': 'incomplete', 'reason': 'check_chain_cap'})
        # finalize: the verdict is not_verified with a fixed reason line, no kernel says rejected (the issue stays open,
        # submissions.report closes only on a pass or a rejection), and the run ends, which releases the queue lease.
        data['theorems'] = {'Race.bound': {'lean_kernel': 'incomplete', 'nanoda_kernel': 'incomplete', 'reported_axioms': ['propext']}}
        self.assertEqual(verdicts.admission(data, ['Race.bound']), ('not_verified', 'lean_not_passed'))
        self.assertNotIn('rejected', [k.get('status') for k in data['kernels'].values()])
        self.assertEqual(verdicts.reason_line(data, 'lean_not_passed'),
                         'Reason: the kernel check did not finish within the job and hour limits of the check chain.')

    def test_build_and_export_failures(self):
        self.put('build1', {'status': 'prepared', 'request': {}, 'chain_leg': {'build': 'stop', 'outcome': {
            'status': 'rejected', 'reason': 'lean_compile_error', 'diagnostic': 'x'}}})
        data = self.final()
        self.assertEqual(data['kernels']['lean'], {'status': 'rejected', 'reason': 'lean_compile_error', 'diagnostic': 'x'})
        self.assertEqual(data['status'], 'not_verified')
        self.setUp()
        self.put('build1', {'status': 'prepared', 'request': {}, 'chain_leg': {'build': 'continue',
                                                                               'outcome': {'status': 'incomplete', 'reason': 'build_chain_cap'}}})
        self.assertEqual(self.final()['kernels']['lean']['reason'], 'build_chain_cap')
        self.setUp()
        self.put('build1', {'status': 'prepared', 'chain_leg': {'build': 'done'}})
        self.put('export', self.base(chain_export={'status': 'rejected', 'reason': 'lean_compile_error', 'diagnostic': 'd'}))
        lean = self.final()['kernels']['lean']
        self.assertEqual((lean['status'], lean['reason'], lean['diagnostic']), ('rejected', 'lean_compile_error', 'd'))
        # The audit failed: no segment ran.
        self.setUp()
        self.put('build1', {'status': 'prepared', 'chain_leg': {'build': 'done'}})
        self.put('export', self.base(axiom_audit={'status': 'invalid_output'}))
        self.assertEqual(self.final()['kernels']['lean']['status'], 'not_started')
        # Export and audit passed, but no segment record (segment() raised): a verifier problem (Integrations N2).
        self.setUp()
        self.put('build1', {'status': 'prepared', 'chain_leg': {'build': 'done'}})
        self.put('export', self.base())
        data = self.final()
        self.assertEqual({k: data['kernels']['lean'][k] for k in ['status', 'reason']}, {'status': 'incomplete', 'reason': 'no_segment_record'})
        self.assertEqual(data['status'], 'not_verified')
        self.assertEqual(verdicts.reason_line(data, 'lean_not_passed'),
                         'Reason: the kernel check of the check chain did not start. This is a verifier problem; a maintainer looks at it.')

    def test_the_gate_stop_keeps_setup_failed(self):
        self.put('build1', {'schema_version': 1, 'status': 'setup_failed', 'steps': [], 'kernels': {}},
                 gate={'status': 'claimed_only'})
        data = self.final()
        self.assertEqual(data['status'], 'setup_failed')
        self.assertNotIn('chain', data)
        self.assertEqual(json.loads((self.art / 'gate.json').read_text()), {'status': 'claimed_only'})
        # Nothing ran at all: no receipt; finalize writes setup_failed.
        self.setUp()
        self.assertIsNone(self.final())

    def test_a_gate_file_that_does_not_match_its_pin_is_not_copied(self):
        self.put('build1', {'schema_version': 1, 'status': 'setup_failed', 'steps': [], 'kernels': {}},
                 gate={'status': 'proceed'})
        (self.tmp / 'chain-legs/chain-leg-7-1-42-build1/gate.json').write_text(json.dumps({'status': 'claimed_only'}))
        self.final()
        self.assertFalse((self.art / 'gate.json').exists())


class ExportAndSegmentTests(unittest.TestCase):
    """export(), check() and segment() with the units replaced: the files, pins and records around Comparator."""
    def setUp(self):
        tmp = tempfile.TemporaryDirectory(); self.addCleanup(tmp.cleanup)
        self.tmp = Path(tmp.name)
        self.work, self.art = self.tmp / 'work', self.tmp / 'artifacts'
        for target, value in [('WORK', self.work), ('ART', self.art)]:
            p = patch.object(v, target, value); p.start(); self.addCleanup(p.stop)
        p = patch.object(chain, 'EXPORT_ARTIFACT', self.tmp / 'export-artifact'); p.start(); self.addCleanup(p.stop)
        (self.work / 'control/export').mkdir(parents=True); (self.work / 'scratch').mkdir(); self.art.mkdir()
        (self.work / 'stage/.lake/build').mkdir(parents=True)
        v.save({'started_unix': time.time(), 'steps': [], 'kernels': {'lean': {'status': 'not_started'}},
                'axiom_audit': {'status': 'passed'}})
        self.launched = []

    def launch(self, receipt, result='success', code=0):
        def launch_github(kernel, args, deadline):
            self.launched.append((kernel, args, json.loads((self.work / 'control/check-args.json').read_text())))
            scratch = Path(args[args.index('/tmp') - 1])
            self.assertEqual(os.listdir(scratch), [])  # A new empty /tmp for each segment.
            if receipt is not None:
                (scratch / 'segment.json').write_text(json.dumps(receipt))
            return code, result, None, time.monotonic(), {'sampled_peak_cgroup_bytes': 1}
        return patch.object(v, 'launch_github', side_effect=launch_github)

    def fake_verify(self, status='passed', kernel='export'):
        self.verify_calls = []
        def verify(kernels):
            self.verify_calls.append(kernels)
            if kernels == ['audit']:
                # Integrations F1: the audit unit imports the submission modules (submission code runs). Its /tmp is
                # empty, the solution export is already in control/export, and what it writes in /tmp reaches nothing.
                self.assertEqual(os.listdir(self.work / 'scratch'), [])
                self.assertTrue((self.work / 'control/export/solution.export').is_file())
                (self.work / 'scratch/solution.export').write_bytes(b'planted')
                return
            self.assertEqual(kernels, ['export'] if kernel == 'export' else ['challenge'])
            name = 'solution' if kernel == 'export' else 'challenge'
            (self.work / f'scratch/{name}.export').write_bytes(name.encode() * 100)
            data = v.receipt(); data['kernels'][kernel] = {'status': status}; v.save(data)
        return patch.object(v, 'verify', side_effect=verify)

    def test_the_challenge_export_runs_before_unpack_and_moves_out_of_tmp(self):
        build = self.work / 'stage/.lake/build'
        def verify(kernels):
            self.assertEqual(kernels, ['challenge'])
            (build / 'lib/lean').mkdir(parents=True); (build / 'lib/lean/VerifierChallenge.olean').write_bytes(b'o')
            (self.work / 'scratch/challenge.export').write_bytes(b'challenge')
            (self.work / 'scratch/leftover').write_bytes(b'x')
            data = v.receipt(); data['kernels']['challenge'] = {'status': 'passed'}; v.save(data)
        with patch.object(v, 'verify', side_effect=verify):
            chain.challenge()
        self.assertEqual((self.work / 'control/export/challenge.export').read_bytes(), b'challenge')
        # The build folder is the empty folder again (unpack refuses another), and /tmp is empty.
        self.assertEqual(os.listdir(build), [])
        self.assertEqual(os.listdir(self.work / 'scratch'), [])
        self.assertEqual(v.receipt()['chain_challenge'], {'status': 'passed'})
        # Refused after a restore (a build file exists) and after a failed challenge export.
        (build / 'x').write_bytes(b'x')
        with patch.object(v, 'verify') as called, self.assertRaises(RuntimeError):
            chain.challenge()
        called.assert_not_called()
        (build / 'x').unlink()
        with self.fake_verify('pending_review', 'challenge'), self.assertRaises(RuntimeError):
            chain.challenge()
        # A symlink in /tmp is not taken.
        self.setUp()
        def symlinked(kernels):
            os.symlink(self.tmp / 'elsewhere', self.work / 'scratch/challenge.export')
            data = v.receipt(); data['kernels']['challenge'] = {'status': 'passed'}; v.save(data)
        with patch.object(v, 'verify', side_effect=symlinked), self.assertRaises(ValueError):
            chain.challenge()

    def test_export_writes_pinned_files_and_runs_the_segment_at_0(self):
        (self.work / 'control/export/challenge.export').write_bytes(b'challenge' * 100)
        receipt = {'schema': 'bos-segment-v1', 'status': 'stopped', 'from': 0, 'to': 50, 'hash_from': H0, 'hash_to': 'f' * 16,
                   'compare': 'passed'}
        with self.fake_verify(), self.launch(receipt), patch.object(v, 'sandbox_args', side_effect=lambda scratch=None: ['--bind', str(scratch), '/tmp']):
            chain.export()
        data = v.receipt()
        files = data['chain_export']['files']
        self.assertEqual(self.verify_calls, [['export'], ['audit']])
        for name, file in chain.EXPORT_FILES.items():
            self.assertEqual(files[name]['sha256'], v.digest(chain.EXPORT_ARTIFACT / file))
            raw = __import__('subprocess').run(['zstd', '-d', '-q', '-c', str(chain.EXPORT_ARTIFACT / file)], capture_output=True, check=True).stdout
            self.assertEqual(raw, (self.work / 'control/export' / f'{name}.export').read_bytes())
        # The audit's planted file stayed in its /tmp; the pinned file and the segment's file are the export unit's.
        self.assertEqual((self.work / 'control/export/solution.export').read_bytes(), b'solution' * 100)
        self.assertEqual((self.work / 'scratch/solution.export').read_bytes(), b'planted')
        self.assertNotIn('export', data['kernels'])
        kernel, args, check_args = self.launched[0]
        self.assertEqual(kernel, 'check')
        self.assertEqual(check_args[:5], ['--bos-check', str(self.work / 'control/lean.json'),
                                          str(self.work / 'control/export/solution.export'),
                                          str(self.work / 'control/export/challenge.export'), '/tmp/segment.json'])
        self.assertEqual(check_args[5:], ['0', check_args[6], '0', '0'])  # No segment_parts in this receipt.
        self.assertEqual(data['chain_segment']['status'], 'linked')
        self.assertEqual(data['chain_segment']['segment'], receipt)
        self.assertEqual(data['chain_segment']['export_sha256'], files['solution']['sha256'])

    def test_no_segment_after_a_failed_export_or_audit(self):
        with self.assertRaises(RuntimeError):
            chain.export()  # No challenge export in this job.
        (self.work / 'control/export/challenge.export').write_bytes(b'c')
        with self.fake_verify('rejected'), self.launch(None):
            chain.export()
        self.assertEqual(self.launched, [])
        self.assertEqual(self.verify_calls, [['export']])  # No audit after a failed export.
        self.assertEqual(v.receipt()['chain_export'], {'status': 'rejected'})
        self.setUp()
        (self.work / 'control/export/challenge.export').write_bytes(b'c')
        data = v.receipt(); data['axiom_audit'] = {'status': 'invalid_output'}; v.save(data)
        with self.fake_verify(), self.launch(None):
            chain.export()
        self.assertEqual(self.launched, [])
        self.assertNotIn('chain_segment', v.receipt())

    def test_the_profile_segment_parts_reach_comparator(self):
        data = v.receipt(); data['profile'] = {'runner': 'github-chain', 'chain': {'segment_parts': 5}}; v.save(data)
        receipt = {'schema': 'bos-segment-v1', 'status': 'stopped', 'from': 100, 'to': 150, 'hash_from': 'e' * 16,
                   'hash_to': 'f' * 16, 'compare': 'not_run'}
        with self.launch(receipt), patch.object(v, 'sandbox_args', side_effect=lambda scratch=None: ['--bind', str(scratch), '/tmp']):
            chain.segment(SHA, 100, 'e' * 16)
        self.assertEqual(self.launched[0][2][5:], ['100', self.launched[0][2][6], '0', '5'])
        self.assertEqual(v.receipt()['chain_segment']['status'], 'linked')

    def test_check_restores_by_pin_and_records_a_killed_unit(self):
        folder = chain.EXPORT_ARTIFACT; folder.mkdir()
        pins = {}
        for name, file in chain.EXPORT_FILES.items():
            (folder / file).write_bytes(__import__('subprocess').run(v.ZSTD_PACK, input=name.encode() * 50, capture_output=True, check=True).stdout)
            pins[name] = v.digest(folder / file)
        env = {'BOS_EXPORT_SHA256': pins['solution'], 'BOS_CHALLENGE_SHA256': pins['challenge'], 'BOS_CHECK_FROM': '120',
               'BOS_HASH_FROM': 'e' * 16}
        with patch.dict(os.environ, env), self.launch(None, 'oom-kill', 137), \
                patch.object(v, 'sandbox_args', side_effect=lambda scratch=None: ['--bind', str(scratch), '/tmp']):
            chain.check()
        record = v.receipt()['chain_segment']
        self.assertEqual((record['status'], record['reason'], record['from']), ('incomplete', 'out_of_memory', 120))
        self.assertEqual(self.launched[0][2][3:6], ['-', '/tmp/segment.json', '120'])
        self.assertEqual(self.launched[0][2][-1], '0')
        self.assertEqual((self.work / 'control/export/solution.export').read_bytes(), b'solution' * 50)
        self.assertFalse((folder / 'solution.export.zst').exists())
        # A wrong pin or bad inputs: nothing runs.
        for bad in [{'BOS_EXPORT_SHA256': '0' * 64}, {'BOS_CHECK_FROM': '-1'}, {'BOS_CHECK_FROM': '01'}, {'BOS_HASH_FROM': 'x'}]:
            with self.subTest(bad=bad):
                self.setUp(); folder = chain.EXPORT_ARTIFACT; folder.mkdir()
                for name, file in chain.EXPORT_FILES.items():
                    (folder / file).write_bytes(__import__('subprocess').run(v.ZSTD_PACK, input=name.encode() * 50, capture_output=True, check=True).stdout)
                with patch.dict(os.environ, {**env, **bad}), self.launch(None), self.assertRaises(ValueError):
                    chain.check()
                self.assertEqual(self.launched, [])

    def test_a_segment_that_does_not_link_or_has_no_time(self):
        receipt = {'schema': 'bos-segment-v1', 'status': 'stopped', 'from': 100, 'to': 150, 'hash_from': 'd' * 16, 'hash_to': 'f' * 16}
        with self.launch(receipt), patch.object(v, 'sandbox_args', side_effect=lambda scratch=None: ['--bind', str(scratch), '/tmp']):
            chain.segment(SHA, 100, 'e' * 16)
        self.assertEqual(v.receipt()['chain_segment']['status'], 'unlinked')
        data = v.receipt(); data['started_unix'] = time.time() - v.DEADLINE_SECONDS + 60; v.save(data)
        chain.segment(SHA, 100, 'e' * 16)
        self.assertEqual(v.receipt()['chain_segment'], {'export_sha256': SHA, 'from': 100, 'expected_hash_from': 'e' * 16,
                                                         'status': 'not_run', 'reason': 'job_time'})


class AdmissionTests(unittest.TestCase):
    def test_only_the_chain_reason_is_new(self):
        source = (ROOT / 'scripts/verdicts.py').read_text()
        self.assertIn("'total_deadline', 'not_run_chain']", source)
        for reason in ['build_chain_cap', 'check_chain_cap', 'chain_coverage']:
            self.assertIn(reason, verdicts.KERNEL_REASONS)

    def test_the_export_kernel_outcome(self):
        self.assertEqual(verdicts.kernel_outcome('export', 0, 'BOS export: wrote solution 9 bytes\n'),
                         {'status': 'passed', 'reason': 'comparator_acceptance'})
        self.assertEqual(verdicts.kernel_outcome('challenge', 0, 'BOS export: wrote challenge 9 bytes\n')['status'], 'passed')
        # Each unit needs its own line: a solution line does not pass the challenge unit.
        self.assertEqual(verdicts.kernel_outcome('challenge', 0, 'BOS export: wrote solution 9 bytes\n')['status'], 'pending_review')
        self.assertEqual(verdicts.kernel_outcome('export', 1, 'BOS export: wrote solution 9 bytes\n')['status'], 'pending_review')
        bad = "error: Submission/A.lean:3:4: unknown identifier 'x'\nerror: build failed\n"
        self.assertEqual(verdicts.kernel_outcome('export', 1, bad)['reason'], 'lean_compile_error')
        self.assertEqual(verdicts.kernel_outcome('export', 0, '', 'oom-kill')['reason'], 'out_of_memory')


class SelectionTests(unittest.TestCase):
    def test_a_chain_profile_gets_a_chain_entry(self):
        profiles = json.loads((ROOT / 'profiles/direct.json').read_text())
        changed = dict(profiles, dft=dict(profiles['dft'], runner='github-chain'))
        real = Path.read_text
        fake = lambda path, *a, **k: json.dumps(changed) if path.name == 'direct.json' else real(path, *a, **k)
        sub = {'schema_version': 1, 'problem': 'dft', 'bound': '1', 'repo_url': 'https://github.com/a/b', 'commit': 'a' * 40,
               'authors': []}
        with patch.object(Path, 'read_text', fake):
            self.assertEqual(s.matrix_entry(5, 'x', 'issue', sub), {'issue_number': 5, 'login': 'x', 'route': 'issue', 'chain': True})
            self.assertEqual(s.matrix_entry(5, 'x', 'pull_request', sub), {'issue_number': 5, 'login': 'x', 'route': 'pull_request'})
        self.assertEqual(v.chain_targets({'runner': 'github-chain', 'solution_module': 'Submission'}, [['A']], True), 'Submission\n')


class WorkflowTests(unittest.TestCase):
    def setUp(self):
        self.jobs = yaml.safe_load((ROOT / '.github/workflows/submission-check.yml').read_text())['jobs']
        self.caller = yaml.safe_load((ROOT / '.github/workflows/submissions.yml').read_text())

    def runs(self, job):
        return [step.get('run') or step['uses'].split('@')[0] for step in self.jobs[job]['steps']]

    def test_the_graph(self):
        names = ['chain_' + n for n in chain.LEGS] + ['chain_final']
        self.assertEqual([n for n in self.jobs if n.startswith('chain_')], names)
        self.assertEqual(self.caller['jobs']['check']['with']['chain'], '${{ matrix.chain == true }}')
        self.assertEqual(self.jobs['chain_build1']['if'], "inputs.chain && inputs.route == 'issue'")
        for k in range(1, 4):
            prev = 'chain_' + chain.BUILD_LEGS[k - 1]
            job = self.jobs['chain_' + chain.BUILD_LEGS[k]]
            self.assertEqual((job['needs'], job['if']), (prev, f"${{{{ !cancelled() && needs.{prev}.outputs.next == 'true' }}}}"))
        self.assertEqual(self.jobs['chain_export']['needs'], ['chain_' + n for n in chain.BUILD_LEGS])
        self.assertIn("needs.chain_build4.outputs.done == 'true'", self.jobs['chain_export']['if'])
        self.assertEqual(self.jobs['chain_check1']['needs'], 'chain_export')
        for k in range(1, 4):
            prev = 'chain_' + chain.CHECK_LEGS[k - 1]
            job = self.jobs['chain_' + chain.CHECK_LEGS[k]]
            self.assertEqual(job['needs'], ['chain_export', prev])
            self.assertEqual(job['env']['BOS_CHECK_FROM'], f'${{{{ needs.{prev}.outputs.check_from }}}}')
            self.assertEqual(job['env']['BOS_EXPORT_SHA256'], '${{ needs.chain_export.outputs.export_sha256 }}')
        self.assertEqual(self.jobs['chain_final']['needs'], names[:-1])
        self.assertEqual(self.jobs['chain_final']['if'], "${{ always() && inputs.chain && inputs.route == 'issue' }}")

    def test_every_job_is_a_free_hosted_runner_with_read_permissions(self):
        for name, job in self.jobs.items():
            if name.startswith('chain_'):
                self.assertEqual(job['runs-on'], 'ubuntu-latest', name)
                self.assertEqual(set(job['permissions'].values()), {'read'}, name)
                self.assertLessEqual(job['timeout-minutes'], 350, name)

    def test_steps(self):
        head = ['actions/checkout', 'actions/download-artifact', 'python3 scripts/submissions.py materialize']
        setup = ['python3 -m unittest discover -s tests -v', 'python3 scripts/verifier.py prepare', 'python3 scripts/verifier.py setup']
        tail = ['python3 scripts/chain.py leg', 'actions/upload-artifact']
        self.assertEqual(self.runs('chain_build1'), head + ['python3 scripts/submissions.py preflight'] + setup +
                         ['python3 scripts/verifier.py build', 'python3 scripts/verifier.py pack', 'actions/upload-artifact'] + tail)
        for leg in chain.BUILD_LEGS[1:]:
            self.assertEqual(self.runs('chain_' + leg), head + setup + ['actions/download-artifact', 'python3 scripts/verifier.py unpack',
                             'python3 scripts/verifier.py build', 'python3 scripts/verifier.py pack', 'actions/upload-artifact'] + tail)
        self.assertEqual(self.runs('chain_export'), head + ['python3 scripts/submissions.py preflight'] + setup +
                         ['python3 scripts/chain.py challenge', 'python3 scripts/chain.py pick', 'actions/download-artifact',
                          'python3 scripts/verifier.py unpack',
                          'python3 scripts/chain.py export', 'actions/upload-artifact'] + tail)
        for leg in chain.CHECK_LEGS:
            self.assertEqual(self.runs('chain_' + leg), head + setup + ['actions/download-artifact', 'python3 scripts/chain.py check'] + tail)
        self.assertEqual(self.runs('chain_final'), ['actions/checkout', 'actions/download-artifact', 'python3 scripts/chain.py final',
                                                    'python3 scripts/verifier.py finalize', 'actions/upload-artifact'])
        # The receipt that the report job reads.
        upload = self.jobs['chain_final']['steps'][-1]
        self.assertEqual(upload['with']['name'], 'verifier-receipt-and-logs-${{ github.run_id }}-${{ github.run_attempt }}-${{ inputs.issue_number }}')
        # Every leg's last step uploads its receipt; every leg sets BOS_SPLIT and its own leg name.
        for leg in chain.LEGS:
            job = self.jobs['chain_' + leg]
            self.assertEqual(job['env']['BOS_CHAIN_LEG'], leg)
            self.assertEqual(job['env']['BOS_SPLIT'], 'true')
            self.assertEqual(job['outputs']['leg_sha256'], '${{ steps.leg.outputs.leg_sha256 }}')
            self.assertEqual(job['steps'][-1]['with']['name'],
                             f'chain-leg-${{{{ github.run_id }}}}-${{{{ github.run_attempt }}}}-${{{{ inputs.issue_number }}}}-{leg}')
            self.assertEqual(job['steps'][-2]['if'], 'always()')
            tests = next(step for step in job['steps'] if step.get('run') == 'python3 -m unittest discover -s tests -v')
            self.assertEqual(tests['env'], {'BOS_SPLIT': ''})
        # Only build1 and export call the API (the gate); the export gate follows build1's.
        for leg in chain.LEGS:
            gated = any(step.get('run') == 'python3 scripts/submissions.py preflight' for step in self.jobs['chain_' + leg]['steps'])
            self.assertEqual(gated, leg in ['build1', 'export'], leg)
        gate = next(step for step in self.jobs['chain_export']['steps'] if step.get('id') == 'gate')
        self.assertEqual(gate['env']['BOS_BUILD_PROCEED'], '${{ needs.chain_build1.outputs.proceed }}')

    def test_each_pin_comes_from_the_producing_job(self):
        for k in range(1, 4):
            prev = 'chain_' + chain.BUILD_LEGS[k - 1]
            unpack = next(step for step in self.jobs['chain_' + chain.BUILD_LEGS[k]]['steps'] if step.get('id') == 'unpack')
            self.assertEqual(unpack['env'], {'BOS_BUILD_RESULT': f'${{{{ needs.{prev}.result }}}}',
                                             'BOS_BUILD_SHA256': f'${{{{ needs.{prev}.outputs.build_sha256 }}}}',
                                             'BOS_BUILD_RECORD_SHA256': f'${{{{ needs.{prev}.outputs.build_record_sha256 }}}}'})
        unpack = next(step for step in self.jobs['chain_export']['steps'] if step.get('run') == 'python3 scripts/verifier.py unpack')
        self.assertEqual(unpack['env'], {'BOS_BUILD_RESULT': '${{ steps.pick.outputs.result }}',
                                         'BOS_BUILD_SHA256': '${{ steps.pick.outputs.build_sha256 }}',
                                         'BOS_BUILD_RECORD_SHA256': '${{ steps.pick.outputs.build_record_sha256 }}'})
        pick = next(step for step in self.jobs['chain_export']['steps'] if step.get('id') == 'pick')
        self.assertEqual(pick['env'], {'BOS_CHAIN_NEEDS': '${{ toJSON(needs) }}'})
        for name in ['chain_' + n for n in chain.BUILD_LEGS]:
            self.assertEqual(self.jobs[name]['outputs']['build_sha256'], '${{ steps.pack.outputs.build_sha256 }}')
            self.assertEqual(self.jobs[name]['outputs']['build_record_sha256'], '${{ steps.pack.outputs.build_record_sha256 }}')



class ChainProfileTests(unittest.TestCase):
    """prepare (verifier.check_chain_profile): the segmented check is a copy of Replay.lean of one Lean release."""
    def test_only_the_chain_toolchain_with_the_comparator_patches(self):
        good = {'runner': 'github-chain', 'lean_toolchain': v.CHAIN_TOOLCHAIN, 'tools_file': 'profiles/tools-chain.json',
                'chain': {'max_build_jobs': 4, 'max_check_jobs': 4, 'max_hours': 30}}
        request = {'lean_toolchain': v.CHAIN_TOOLCHAIN}
        v.check_chain_profile(good, request)
        for bad, req in [({'lean_toolchain': 'leanprover/lean4:v4.33.1'}, request),
                         ({}, {'lean_toolchain': 'leanprover/lean4:v4.35.0'}),
                         ({'tools_file': 'profiles/tools.json'}, request), ({'tools_file': None}, request),
                         ({'chain': {'max_hours': 31}}, request), ({'chain': {'max_check_jobs': 5}}, request)]:
            profile = {k: x for k, x in {**good, **bad}.items() if x is not None}
            with self.subTest(bad=bad, request=req), self.assertRaises(ValueError):
                v.check_chain_profile(profile, req)
        # Other runners are not checked here.
        v.check_chain_profile({'runner': 'github-split', 'lean_toolchain': 'leanprover/lean4:v4.33.1'}, {})

    def test_every_chain_profile_in_the_repo_passes(self):
        profiles = list(json.loads((ROOT / 'profiles/direct.json').read_text()).values())
        profiles += [json.loads(p.read_text()) for p in sorted((ROOT / 'profiles').glob('*.json'))
                     if p.name not in ['direct.json'] and isinstance(json.loads(p.read_text()), dict)]
        for profile in profiles:
            if isinstance(profile, dict) and profile.get('runner') == 'github-chain':
                v.check_chain_profile(profile, {'lean_toolchain': profile['lean_toolchain']})


if __name__ == '__main__':
    unittest.main()
