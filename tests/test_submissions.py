import copy
import hashlib
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch, Mock
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import submissions as s
import verifier as v
import queue_lease
from verdicts import kernel_outcome
FIXTURE = ROOT / 'tests/fixtures/direct'


def body(problem='dft', bound='1/1000', commit='1'*40):
    return f'### Problem\n\n{problem}\n\n### Repository URL\n\nhttps://github.com/example/proof\n\n### Commit SHA\n\n{commit}\n\n### Bound\n\n{bound}\n'


def issue(number=42, login='submitter', **kwargs):
    return {'number': number, 'state': 'open', 'title': '[Lean submission] test', 'body': body(**kwargs),
            'user': {'login': login}, 'created_at': '2026-10-10T12:00:00Z', 'updated_at': '2026-10-10T12:00:00Z'}


class SubmissionTests(unittest.TestCase):
    def selected(self):
        item = issue()
        selected = s.issue_request(item, s.issue_input(item))
        selected['test_only'] = True
        return selected

    def receipt(self):
        selected = self.selected()
        return {'request': selected['inputs'], 'status': 'not_verified', 'theorem_names': ['Race.bound'],
                'theorems': {'Race.bound': {'lean_kernel': 'passed', 'nanoda_kernel': 'incomplete', 'reported_axioms': ['propext','Classical.choice','Quot.sound']}},
                'kernels': {'lean': {'status': 'passed', 'reason': 'comparator_acceptance'},
                            'nanoda': {'status': 'incomplete', 'reason': 'out_of_memory'}},
                'axiom_audit': {'status': 'passed', 'reported_axioms': {'Race.bound': ['propext','Classical.choice','Quot.sound']}},
                'generated_challenge_sha256': hashlib.sha256(s.challenge_source(selected['submission']).encode()).hexdigest(),
                'run_url': 'https://github.com/bigospeedrun/verifier/actions/runs/123',
                'verifier_commit': 'a'*40, 'checked_at': '2026-10-10T13:00:00Z'}

    def historical_replay(self):
        fixture = json.loads((FIXTURE/'dft-837dc31.json').read_text())
        sub = s.validate_submission(fixture['submission'])
        receipt = json.loads((FIXTURE/'historical-dft-receipt.json').read_text())
        request = s.make_request(sub)
        self.assertEqual(receipt['request'], {k: val for k,val in request.items() if k != 'direct_submission'})
        self.assertEqual(receipt['profile']['challenge_sha256'], hashlib.sha256(s.challenge_source(sub).encode()).hexdigest())
        receipt['request'] = request
        receipt['generated_challenge_sha256'] = receipt['profile']['challenge_sha256']
        receipt['checked_at'] = datetime.fromtimestamp(receipt['finished_unix'],timezone.utc).isoformat().replace('+00:00','Z')
        selected = dict(self.selected(), submission=sub, inputs=request, submission_sha256=s.submission_hash(sub))
        return selected, receipt

    def test_historical_dft_replay_stays_non_importable(self):
        selected, receipt = self.historical_replay()
        result = s.envelope(receipt, selected,'38050668997','1',receipt['verifier_commit'],'https://github.com/bigospeedrun/verifier/actions/runs/38050668997/artifacts/11672731981')
        self.assertTrue(result['test_only'])
        self.assertEqual(result['submission']['bound'],'47171/62500000')
        self.assertTrue(s.passes(receipt,selected))
        self.assertFalse(s.qualifies_for_run(selected['submission'], {'score':'47171/62500000','score_relation':'attained','any_lean_verified_at_bound':True}))

    def test_structured_fields_only(self):
        self.assertEqual(s.parse_body(body())['authors'], [])
        for text in [json.dumps(self.selected()['submission']), body()+'prose', body()+'\n### Extra\n\n1',
                     body().replace('1/1000','2/2000'), body().replace('### Bound','### Problem'),
                     body().replace('https://github.com/example/proof','https://github.com/example/proof\n#eval evil'),
                     body().replace('1/1000','1/0'), body().replace('dft','sssp'), body().replace('1'*40,'main')]:
            with self.subTest(text=text), self.assertRaises(ValueError): s.parse_body(text)

    def test_raw_and_canonical_hashes(self):
        first=body(); second=body().replace('\n','\r\n')
        self.assertEqual(s.submission_hash(s.parse_body(first)),s.submission_hash(s.parse_body(second)))
        self.assertNotEqual(s.body_hash(first),s.body_hash(second))

    def test_exact_targets(self):
        for problem, bound, text in [('3sum','2499/1250','EndStatement.ThreeSum.SolvedInTime'),('apsp','149971/50000','EndStatement.APSP.SolvedInTime'),('dft','1/1000','(1 - (1 : ℝ) / 1000)')]:
            sub=s.parse_body(body(problem,bound)); profile,names=v.validate_request(s.make_request(sub))
            self.assertIn(text,s.challenge_source(sub)); self.assertEqual(names,['Race.bound'])
            self.assertTrue(s.challenge_source(sub).startswith((ROOT/profile['challenge_file']).read_text()))

    def test_lean_pass_nanoda_resource_incomplete_is_admitted(self):
        self.assertTrue(s.passes(self.receipt(),self.selected()))
        for reason in ['timeout','out_of_memory','disk_limit','total_deadline']:
            receipt=self.receipt(); receipt['kernels']['nanoda']['reason']=reason
            self.assertTrue(s.passes(receipt,self.selected()))

    def test_real_rejection_and_ambiguous_failure_block(self):
        for status, reason, expected in [('rejected','nanoda_type_equality_rejection','blocked'),('pending_review','ambiguous_failure','pending_review'),('incomplete','unknown','pending_review')]:
            receipt=self.receipt(); receipt['kernels']['nanoda']={'status':status,'reason':reason}; receipt['theorems']['Race.bound']['nanoda_kernel']=status
            self.assertEqual(s.verdict(receipt,self.selected())[0],expected)

    def test_axioms_are_checked_not_just_audit_status(self):
        for reported in [{'Race.bound':['sorryAx']},{'Other':['propext']},{'Race.bound':'propext'},{}]:
            receipt=self.receipt(); receipt['axiom_audit']['reported_axioms']=reported
            self.assertFalse(s.passes(receipt,self.selected()))

    def test_statement_and_theorem_binding(self):
        for mutate in [lambda r:r['request'].update(commit='0'*40),lambda r:r.update(generated_challenge_sha256='0'*64),lambda r:r.update(theorems={}),lambda r:r.update(theorem_names=['Other'])]:
            receipt=self.receipt(); mutate(receipt)
            self.assertFalse(s.passes(receipt,self.selected()))
        request=self.selected()['inputs'];request['theorem_names']='Other'
        with self.assertRaises(ValueError):v.validate_request(request)

    def test_resource_classification_uses_host_evidence(self):
        self.assertEqual(kernel_outcome('nanoda',1,'oom-kill Result: timeout')['status'],'pending_review')
        self.assertEqual(kernel_outcome('nanoda',1,'','oom-kill'),{'status':'incomplete','reason':'out_of_memory'})
        self.assertEqual(kernel_outcome('nanoda',1,'Nanoda kernel rejected the solution')['status'],'pending_review')
        self.assertEqual(kernel_outcome('nanoda',1,'Nanoda kernel rejected the solution\nassertion failed: self.def_eq(u, v)')['status'],'rejected')

    def test_bound_gate(self):
        for problem,current,better,worse in [('dft','1/1000','1/999','1/1001'),('3sum','2499/1250','1999/1000','2'),('apsp','149971/50000','2999/1000','3')]:
            record={'score':current,'score_relation':'attained','any_lean_verified_at_bound':False}
            self.assertTrue(s.qualifies_for_run(s.parse_body(body(problem,better)),record))
            self.assertTrue(s.qualifies_for_run(s.parse_body(body(problem,current)),record))
            self.assertFalse(s.qualifies_for_run(s.parse_body(body(problem,current)),dict(record, any_lean_verified_at_bound=True)))
            self.assertFalse(s.qualifies_for_run(s.parse_body(body(problem,worse)),record))
        self.assertTrue(s.qualifies_for_run(s.parse_body(body()),{'score':'1/1000','score_relation':'strict-upper-bound'}))

    def test_record_snapshot_matches_board_admission(self):
        data = {'problem_id': '3sum/word-ram', 'records': [
            {'id': 'record', 'score': '1999/1000', 'submission_url': 'https://example.org/record'},
            {'id': 'self', 'score': '1', 'submission_url': 'https://github.com/bigospeedrun/verifier/issues/42'},
            {'id': 'reproduction', 'score': '0', 'submission_url': 'https://example.org/copy'}],
            'record_metadata': {'record': {'eligible_for_record': False}, 'self': {'eligible_for_record': True}, 'reproduction': {'reproduction_of': 'record'}}}
        with patch.object(s, 'site_snapshot', return_value=('a'*40, json.dumps(data).encode())):
            record = s.current_record('3sum', 'https://github.com/bigospeedrun/verifier/issues/42')
        self.assertEqual(record['leader_ids'], ['record'])
        self.assertFalse(record['any_lean_verified_at_bound'])
        self.assertEqual(record['site_commit'], 'a'*40)

    def test_tied_leader_evidence_is_receipt_backed(self):
        rows = [{'id': name, 'score': '1/1000', 'tier': 'verified'} for name in ['a','b']]
        data = {'problem_id': 'exact-dft/uniform-exact-arithmetic', 'records': rows,
                'record_metadata': {'a': {'site_tier': 'verified'}, 'b': {'site_tier': 'claimed'}}}
        def snapshot():
            with patch.object(s,'site_snapshot',return_value=('a'*40,json.dumps(data).encode())):
                return s.current_record('dft','https://github.com/bigospeedrun/verifier/issues/42')
        self.assertEqual(snapshot()['leader_ids'], ['a','b'])
        self.assertTrue(s.qualifies_for_run(self.selected()['submission'],snapshot()))
        rows[0]['rerun_status'] = {'state': 'passed', 'receipt_path': 'sources/receipt.json'}
        self.assertFalse(s.qualifies_for_run(self.selected()['submission'],snapshot()))

    def test_preflight_stops_when_record_advances(self):
        selected = self.selected(); selected['test_only'] = False
        with tempfile.TemporaryDirectory() as tmp:
            old = Path.cwd(); os.chdir(tmp)
            try:
                Path('request').mkdir(); Path('request/request.json').write_text(json.dumps(selected))
                with patch.dict(os.environ, GITHUB_OUTPUT=str(Path(tmp)/'output')), patch.object(queue_lease,'assert_owner'), patch.object(s, 'api', return_value=issue()), patch.object(s, 'current_record', return_value={'score': '1/500', 'score_relation': 'attained'}):
                    s.preflight()
                self.assertIn('proceed=false', Path('output').read_text())
                self.assertEqual(json.loads(Path('artifacts/gate.json').read_text())['status'], 'claimed_only')
            finally: os.chdir(old)

    def test_queue_cap_and_non_improvement_reply(self):
        issues=[issue(13,'author1')]+[issue(i,'author'+str(i)) for i in range(1,13)]+[issue(14,'other',bound='1/10000')]
        posts=[]
        record={'score':'1/2000','score_relation':'attained'}
        with tempfile.TemporaryDirectory() as tmp:
            old=Path.cwd();os.chdir(tmp)
            try:
                with patch.dict(os.environ,GITHUB_OUTPUT=str(Path(tmp)/'output')),patch.object(queue_lease,'acquire',return_value=Mock(state={'page':1,'offset':0},admitted=Mock(return_value=False))),patch.object(s,'current_record',return_value=record),patch.object(s,'api',side_effect=lambda p,data=None: posts.append(data) if data is not None else issues if p.startswith('issues?') else []):
                    s.select()
                self.assertEqual(len(list(Path('requests').glob('*.json'))),9)
                self.assertTrue(Path('requests/13.json').exists())
                self.assertFalse(Path('requests/1.json').exists())
                self.assertEqual(posts,[])  # The selector stops as soon as ten are selected.
            finally:os.chdir(old)

    def test_comment_markers_are_not_admission_state(self):
        item=issue();request=s.issue_request(item,s.issue_input(item))
        marker=s.marker_for(42,request['submission_sha256'],request['issue_body_sha256'])
        for login,expected in [('attacker',True),('github-actions[bot]',True)]:
            comment={'user':{'login':login,'type':'Bot' if 'bot' in login else 'User'},'body':marker}
            with tempfile.TemporaryDirectory() as tmp:
                old=Path.cwd();os.chdir(tmp)
                try:
                    with patch.dict(os.environ,GITHUB_OUTPUT=str(Path(tmp)/'output')),patch.object(queue_lease,'acquire',return_value=Mock(state={'page':1,'offset':0},admitted=Mock(return_value=False))),patch.object(s,'api',side_effect=lambda p:[item] if p.startswith('issues?') else [comment]),patch.object(s,'current_record',return_value={'score':'1/2000','score_relation':'attained'}):s.select()
                    self.assertEqual(Path('requests/42.json').exists(),expected)
                finally:os.chdir(old)

    def test_fixture_never_materializes(self):
        with tempfile.TemporaryDirectory() as tmp:
            old=Path.cwd();os.chdir(tmp)
            try:
                Path('requests').mkdir();Path('requests/42.json').write_text(json.dumps(self.selected()))
                with patch.dict(os.environ,ISSUE_NUMBER='42'),self.assertRaises(ValueError):s.materialize()
            finally:os.chdir(old)

    def test_report_separates_upload_from_comment_and_marks_stale(self):
        selected=self.selected();receipt=self.receipt();calls=[]
        artifact={'id':99,'name':'fixture','digest':'sha256:'+'f'*64,'archive_url':'https://github.com/bigospeedrun/verifier/actions/runs/123/artifacts/99'}
        with tempfile.TemporaryDirectory() as tmp:
            old=Path.cwd();os.chdir(tmp)
            try:
                Path('request').mkdir();Path('result').mkdir()
                Path('request/request.json').write_text(json.dumps(selected));Path('result/receipt.json').write_text(json.dumps(receipt))
                def fake_api(path,data=None):
                    if data is None:return issue(commit='2'*40)
                    calls.append(data)
                with patch.object(s,'api',side_effect=fake_api),patch.object(s,'receipt_artifact',return_value=artifact),patch.dict(os.environ,GITHUB_RUN_ID='123',GITHUB_RUN_ATTEMPT='1',GITHUB_SHA='a'*40):
                    s.report();self.assertEqual(calls,[]);s.publish()
                result=json.loads(Path('published/direct-submission.json').read_text())
                self.assertEqual(result['status'],'fixture_only');self.assertEqual(result['verification_status'],'passed');self.assertFalse(result['importable'])
                self.assertIn('older or closed',calls[0]['body'])
            finally:os.chdir(old)

    def test_module_headers_and_manifest(self):
        with tempfile.TemporaryDirectory() as tmp:
            stage=Path(tmp);(stage/'Submission').mkdir();(stage/'Submission/A.lean').write_text('module\npublic import Mathlib\n');(stage/'Submission.lean').write_text('module\npublic import Submission.A\n')
            self.assertEqual(v.plan_sources(stage,'Submission'),[['Submission.A','Submission']])
        self.assertIn('0df444a360eaa60ab8c11dca51a86af692955474',v.lakefile(['Submission'],'profiles/anthropic-lake-manifest.json'))


if __name__=='__main__':unittest.main()
