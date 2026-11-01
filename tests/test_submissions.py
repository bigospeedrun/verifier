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
import derivation
import verifier as v
import queue_lease
from verdicts import kernel_outcome, compile_error_comment
FIXTURE = ROOT / 'tests/fixtures/direct'


def body(problem='dft', bound='1/1000', commit='1'*40):
    return f'### Problem\n\n{problem}\n\n### Repository URL\n\nhttps://github.com/example/proof\n\n### Commit SHA\n\n{commit}\n\n### Bound\n\n{bound}\n'


def issue(number=42, login='submitter', **kwargs):
    return {'number': number, 'state': 'open', 'title': '[Lean submission] test', 'body': body(**kwargs),
            'user': {'login': login}, 'created_at': '2026-10-10T12:00:00Z', 'updated_at': '2026-10-10T12:00:00Z'}


class SubmissionTests(unittest.TestCase):
    def setUp(self):
        # The selector's derivation report never reads GitHub in these tests.
        offline = patch.object(derivation.Reader, 'get', side_effect=derivation.NotComputed('offline'))
        offline.start(); self.addCleanup(offline.stop)
        no_release = patch.object(s, 'release')  # The release pass has its own tests.
        no_release.start(); self.addCleanup(no_release.stop)

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

    def test_compile_error_rejected_but_resources_remain_incomplete(self):
        log='error: Submission.lean:15:2: Type mismatch: After simplification\nerror: build failed'
        outcome=kernel_outcome('lean',1,log,'exit-code')
        self.assertEqual(outcome['reason'],'lean_compile_error')
        dep='error: FixedPointTheorems/cubical_sperner_prep.lean:790:4: failed to compile definition, consider marking it as noncomputable\nerror: build failed'
        self.assertEqual(kernel_outcome('lean',1,dep,'exit-code')['reason'],'lean_compile_error')
        self.assertEqual(kernel_outcome('lean',1,dep.replace('failed to compile definition, consider marking it as noncomputable','Invalid field `card`'),'exit-code')['reason'],'lean_compile_error')
        self.assertEqual(kernel_outcome('lean',1,dep.replace('FixedPointTheorems/cubical_sperner_prep','VerifierChallenge'),'exit-code')['status'],'pending_review')
        self.assertEqual(outcome['status'],'rejected')
        self.assertEqual(kernel_outcome('lean',1,log,'oom-kill')['status'],'incomplete')
        self.assertEqual(kernel_outcome('lean',1,'error: build failed','exit-code')['status'],'pending_review')
        self.assertEqual(kernel_outcome('lean',0,log)['status'],'pending_review')
        outcome['diagnostic']='error @nmamano <b> `[link]`\nnext'
        comment=compile_error_comment({'kernels':{'lean':outcome}})
        self.assertNotIn('@nmamano',comment)
        self.assertNotIn('<b>',comment)
        self.assertIn('Compile error:',comment)

    def test_statement_mismatch_is_named_in_the_result_comment(self):
        # Issue #61 (2026-10-24): the commit proved Bound (37615398 / 10000000 : ℚ), the challenge states the reduced
        # 18807699/5000000, and the comment said only "Not verified".
        log="Build completed successfully (3100 jobs).\nuncaught exception: Challenge and solution theorem statement do not match: 'Race.bound'\n"
        outcome=kernel_outcome('lean',1,log,'exit-code')
        self.assertEqual(outcome,{'status':'pending_review','reason':'statement_mismatch','theorem':'Race.bound'})
        comment=compile_error_comment({'kernels':{'lean':outcome}})
        self.assertIn("theorem statement does not match the challenge: `Race.bound`",comment)
        self.assertEqual(comment.count('\n'),2)
        # Resource evidence still wins, a zero exit is no mismatch, and only the nanoda-free lean kernel reports it.
        self.assertEqual(kernel_outcome('lean',1,log,'oom-kill')['status'],'incomplete')
        self.assertEqual(kernel_outcome('lean',0,log)['reason'],'missing_acceptance')
        self.assertEqual(kernel_outcome('nanoda',1,log)['reason'],'ambiguous_failure')
        # A name outside the pattern is not quoted.
        for bad in ["Race.bound`@x","a b",'x'*101]:
            self.assertEqual(kernel_outcome('lean',1,log.replace('Race.bound',bad))['reason'],'ambiguous_failure')
        forged={'kernels':{'lean':dict(outcome,theorem='`@nmamano [x](y)')}}
        self.assertIn('match the challenge: `the theorem`',compile_error_comment(forged))
        self.assertNotIn('@nmamano',compile_error_comment(forged))

    def test_bound_gate(self):
        for problem,current,better,worse in [('dft','1/1000','1/999','1/1001'),('3sum','2499/1250','1999/1000','2'),('apsp','149971/50000','2999/1000','3')]:
            record={'score':current,'score_relation':'attained','any_lean_verified_at_bound':False}
            self.assertTrue(s.qualifies_for_run(s.parse_body(body(problem,better)),record))
            self.assertTrue(s.qualifies_for_run(s.parse_body(body(problem,current)),record))
            self.assertFalse(s.qualifies_for_run(s.parse_body(body(problem,current)),dict(record, any_lean_verified_at_bound=True)))
            self.assertFalse(s.qualifies_for_run(s.parse_body(body(problem,worse)),record))
        self.assertTrue(s.qualifies_for_run(s.parse_body(body()),{'score':'1/1000','score_relation':'strict-upper-bound'}))

    def board(self, problem, rows, verified=()):
        """A site board: rows (id, score[, relation]); ids in verified have a Lean Verified receipt."""
        records, meta = [], {}
        for row in rows:
            rid, score = row[0], row[1]
            r = {'id': rid, 'score': score, 'submission_url': f'https://example.org/{rid}'}
            if len(row) > 2: r['score_relation'] = row[2]
            if rid in verified: r['rerun_status'] = {'state': 'passed', 'receipt_path': f'sources/{rid}.json'}
            records.append(r); meta[rid] = {'site_tier': 'verified' if rid in verified else 'claimed'}
        return {'problem_id': s.MODEL_IDS[problem], 'records': records, 'record_metadata': meta}

    def gate(self, problem, data, url='https://github.com/bigospeedrun/verifier/issues/42'):
        with patch.object(s, 'site_snapshot', return_value=('a'*40, json.dumps(data).encode())):
            return s.current_record(problem, url)

    def test_open_endpoint_is_weaker_than_an_attained_tie(self):
        # Worker 2, 2026-10-17: on exponent boards min() picked the endpoint over an attained tie.
        for problem,score in [('dft','1/1000'),('3sum','1999/1000'),('apsp','2999/1000')]:
            record=self.gate(problem,self.board(problem,[('open',score,'strict-upper-bound'),('closed',score)],verified={'open','closed'}))
            self.assertEqual((record['leader_ids'],record['score_relation']),(['closed'],'attained'),problem)
            # An attained submission at an open endpoint's score improves on it.
            self.assertTrue(s.qualifies_for_run(s.parse_body(body(problem,score)),{'score':score,'score_relation':'strict-upper-bound','any_lean_verified_at_bound':True}),problem)

    def test_the_gate_is_the_best_lean_verified_row(self):
        # Nil ruling 2026-10-20: a Claimed row never blocks a proof run; the best Lean Verified row does.
        data = self.board('3sum', [('claimed-best', '19/10'), ('record', '1999/1000'), ('self', '1'), ('reproduction', '0'), ('classical-baseline', '2')],
                          verified={'record', 'self', 'reproduction'})
        data['records'][2]['submission_url'] = 'https://github.com/bigospeedrun/verifier/issues/42'
        data['record_metadata']['reproduction']['reproduction_of'] = 'record'
        record = self.gate('3sum', data)
        self.assertEqual((record['score'], record['leader_ids'], record['any_lean_verified_at_bound']), ('1999/1000', ['record'], True))
        self.assertEqual(record['site_commit'], 'a'*40)
        # Worse than the Claimed leader 1.9 but better than the Lean Verified 1.999: it runs.
        self.assertTrue(s.qualifies_for_run(s.parse_body(body('3sum', '999/500')), record))
        # A tie with the Lean Verified leader and a worse bound do not.
        self.assertFalse(s.qualifies_for_run(s.parse_body(body('3sum', '1999/1000')), record))
        self.assertFalse(s.qualifies_for_run(s.parse_body(body('3sum', '2')), record))

    def test_tied_leader_evidence_is_receipt_backed(self):
        # A Claimed row at the same bound is not a leader; only the receipt-backed row is.
        data = self.board('dft', [('a', '1/1000'), ('b', '1/1000'), ('classical-baseline', '1/2000')], verified={'a'})
        record = self.gate('dft', data)
        self.assertEqual((record['leader_ids'], record['any_lean_verified_at_bound']), (['a'], True))
        self.assertFalse(s.qualifies_for_run(self.selected()['submission'], record))
        # Without a receipt (site_tier verified alone) the row is not Lean Verified: the baseline gates.
        data = self.board('dft', [('a', '1/1000'), ('classical-baseline', '1/2000')])
        data['record_metadata']['a']['site_tier'] = 'verified'
        record = self.gate('dft', data)
        self.assertEqual((record['leader_ids'], record['any_lean_verified_at_bound']), (['classical-baseline'], False))
        self.assertTrue(s.qualifies_for_run(self.selected()['submission'], record))

    def test_a_board_without_lean_verified_rows_gates_on_the_baseline_or_refuses(self):
        record = self.gate('apsp', self.board('apsp', [('claimed', '2999/1000'), ('classical-baseline', '3')]))
        self.assertEqual((record['score'], record['leader_ids'], record['any_lean_verified_at_bound']), ('3', ['classical-baseline'], False))
        self.assertTrue(s.qualifies_for_run(s.parse_body(body('apsp', '3')), record))  # a tie with the baseline runs
        with self.assertRaisesRegex(ValueError, 'refuse to guess'):
            self.gate('apsp', self.board('apsp', [('claimed', '2999/1000')]))

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
                with patch.dict(os.environ,GITHUB_OUTPUT=str(Path(tmp)/'output')),patch.object(queue_lease,'acquire',return_value=Mock(state={'page':1,'offset':0},admitted=Mock(return_value=False))),patch.object(s,'current_record',return_value=record),patch.object(s,'api',side_effect=lambda p,data=None: posts.append(data) if data is not None else issues if p.startswith('issues?') else []),patch.object(s,'acknowledge'):
                    s.select()
                self.assertEqual(len(list(Path('requests').glob('*.json'))),9)
                self.assertTrue(Path('requests/13.json').exists())
                self.assertFalse(Path('requests/1.json').exists())
                # The selector stops as soon as ten are selected: no Claimed reply to #14; only derivation reports.
                self.assertEqual([p for p in posts if not p['body'].startswith(derivation.MARKER)],[])
                self.assertEqual(sorted(json.loads(Path(f'requests/{n}.json').read_text())['derivation']['status'] for n in [13]),['not_computed'])
            finally:os.chdir(old)

    def test_a_claimed_only_issue_gets_one_report_and_closes(self):
        item=issue(14,'other',bound='1/10000');calls=[]
        digest=s.issue_request(item,s.issue_input(item))['submission_sha256']
        def api(p,data=None,method=None):
            if data is not None:calls.append((method,p,data));return {}
            return [item] if p.startswith('issues?') else []
        with tempfile.TemporaryDirectory() as tmp:
            old=Path.cwd();os.chdir(tmp)
            try:
                with patch.dict(os.environ,GITHUB_OUTPUT=str(Path(tmp)/'output')),patch.object(queue_lease,'acquire',return_value=Mock(state={'page':1,'offset':0},admitted=Mock(return_value=False))),\
                     patch.object(s,'current_record',return_value={'score':'1/2000','score_relation':'attained'}),patch.object(s,'api',side_effect=api),patch.object(s,'acknowledge'):
                    s.select()
            finally:os.chdir(old)
        self.assertEqual([c[:2] for c in calls if not c[2].get('body','').startswith(derivation.MARKER)],[(None,'issues/14/comments'),('PATCH','issues/14')])
        report=[c for c in calls if c[1]=='issues/14/comments' and c[2]['body'].startswith('<!-- bos-claimed-v1')][0]
        self.assertTrue(report[2]['body'].startswith(f'<!-- bos-claimed-v1 14 {digest} -->'))
        self.assertEqual(calls[-1][2],{'state':'closed','state_reason':'not_planned'})
        # The report is already there (an earlier close failed): only the close is sent again.
        reported={'user':{'login':'github-actions[bot]','type':'Bot'},'body':report[2]['body']}
        calls.clear()
        def api2(p,data=None,method=None):
            if data is not None:calls.append((method,p,data));return {}
            return [item] if p.startswith('issues?') else [reported]
        with tempfile.TemporaryDirectory() as tmp:
            old=Path.cwd();os.chdir(tmp)
            try:
                with patch.dict(os.environ,GITHUB_OUTPUT=str(Path(tmp)/'output')),patch.object(queue_lease,'acquire',return_value=Mock(state={'page':1,'offset':0},admitted=Mock(return_value=False))),\
                     patch.object(s,'current_record',return_value={'score':'1/2000','score_relation':'attained'}),patch.object(s,'api',side_effect=api2),patch.object(s,'acknowledge'):
                    s.select()
            finally:os.chdir(old)
        self.assertEqual([c for c in calls if c[1]=='issues/14'],[('PATCH','issues/14',{'state':'closed','state_reason':'not_planned'})])
        self.assertFalse([c for c in calls if c[1]=='issues/14/comments' and c[2]['body'].startswith('<!-- bos-claimed-v1')])

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
                    if data is None:return [] if '/comments' in path else issue(commit='2'*40)
                    calls.append(data)
                with patch.object(s,'api',side_effect=fake_api),patch.object(s,'receipt_artifact',return_value=artifact),patch.dict(os.environ,GITHUB_RUN_ID='123',GITHUB_RUN_ATTEMPT='1',GITHUB_SHA='a'*40):
                    s.report();self.assertEqual(calls,[]);s.publish()
                result=json.loads(Path('published/direct-submission.json').read_text())
                self.assertEqual(result['status'],'fixture_only');self.assertEqual(result['verification_status'],'passed');self.assertFalse(result['importable'])
                self.assertIn('older or closed',calls[0]['body'])
                self.assertIn('TEST ONLY: proof checks passed',calls[0]['body'])
            finally:os.chdir(old)

    def live(self):
        return s.issue_request(issue(), s.issue_input(issue()))

    def status_report(self, receipt, gate=None, test_only=False, derivation=None):
        selection=self.live();selection['test_only']=test_only
        if derivation is not None:selection['derivation']=derivation
        receipt['request']=selection['inputs'];artifact={'id':99,'name':'fixture','digest':'sha256:'+'f'*64,'archive_url':'https://github.com/bigospeedrun/verifier/actions/runs/123/artifacts/99'}
        with tempfile.TemporaryDirectory() as tmp:
            old=Path.cwd();os.chdir(tmp)
            try:
                Path('request').mkdir();Path('result').mkdir();Path('published').mkdir()
                Path('request/request.json').write_text(json.dumps(selection));Path('result/receipt.json').write_text(json.dumps(receipt))
                if gate:Path('result/gate.json').write_text(json.dumps(gate))
                calls=[]
                def fake_api(path,data=None,method=None):
                    if data is None:return [] if '/comments' in path else issue()
                    calls.append((method,path,data))
                import pr_submissions
                self.review=Mock()
                with patch.object(s,'api',side_effect=fake_api),patch.object(s,'receipt_artifact',return_value=artifact),patch.dict(os.environ,GITHUB_RUN_ID='123',GITHUB_RUN_ATTEMPT='1',GITHUB_SHA='a'*40),patch.object(pr_submissions,'hold_ping',self.review):
                    s.report();s.publish()
                self.envelope=json.loads(Path('published/direct-submission.json').read_text())
                return json.loads(Path('published-comment.json').read_text()),calls
            finally:os.chdir(old)

    def test_final_pass_closes_the_issue_as_completed(self):
        comment,calls=self.status_report(self.receipt())
        self.assertEqual(comment['close'],'completed')
        self.assertIn('To submit a stronger bound, open a new issue. This issue now closes.',comment['body'])
        self.assertEqual(calls[0][1],'issues/42/comments');self.assertEqual(calls[0][2],{'body':comment['body']})
        self.assertEqual(calls[1],('PATCH','issues/42',{'state':'closed','state_reason':'completed'}))

    def test_a_derivation_hold_keeps_a_pass_open_unimportable_and_pings_once(self):
        held={'status':'computed','hold':True}
        comment,calls=self.status_report(self.receipt(),derivation=held)
        self.assertNotIn('close',comment);self.assertEqual(comment['hold']['derivation'],held)
        self.assertIn('Held for maintainer review',comment['body'])
        self.assertEqual(len(calls),1)  # The comment only: no close.
        live=self.live()
        self.review.assert_called_once_with(42,'issue',live['submission_sha256'],live['issue_body_sha256'],held)
        self.assertFalse(self.envelope['importable']);self.assertEqual(self.envelope['derivation'],held)
        # No hold: the normal pass closes and stays importable; a held rejection still closes.
        comment,calls=self.status_report(self.receipt(),derivation={'status':'computed','hold':False})
        self.assertEqual(comment['close'],'completed');self.assertTrue(self.envelope['importable']);self.review.assert_not_called()
        rejected=self.receipt();rejected['kernels']['lean']['status']='rejected'
        comment,_=self.status_report(rejected,derivation=held)
        self.assertEqual(comment['close'],'not_planned');self.assertNotIn('hold',comment)

    def test_a_result_links_its_board_and_the_release_and_claimed_close_too(self):
        # Lead, 2026-10-25: each final result names the race page on bigospeedrun.com.
        dft='https://bigospeedrun.com/exact-dft'
        self.assertEqual(s.board_line('average-sensitivity'),'Average sensitivity board: https://bigospeedrun.com/other/average-sensitivity')
        self.assertEqual(s.board_line('nope'),'')
        comment,_=self.status_report(self.receipt())
        self.assertTrue(comment['body'].endswith('\n\nExact discrete Fourier transform board: '+dft))
        rejected=self.receipt();rejected['kernels']['lean']['status']='rejected'
        comment,_=self.status_report(rejected)
        self.assertTrue(comment['body'].endswith('\n\nExact discrete Fourier transform board: '+dft))
        comment,_=self.status_report(self.receipt(),test_only=True)
        self.assertNotIn(dft,comment['body'])
        posted=[]
        with patch.object(s,'comment_once',side_effect=lambda n,b,*a,**k:posted.append(b)),patch.object(s,'api'):
            s.close_claimed(42,'d'*64,'issue','dft')
        self.assertTrue(posted[0].endswith('\n\nExact discrete Fourier transform board: '+dft))

    def test_genuine_rejection_closes_the_issue_as_not_planned(self):
        receipt=self.receipt();receipt['kernels']['lean']['status']='rejected';receipt['axiom_audit']={'status':'incomplete'}
        comment,calls=self.status_report(receipt)
        self.assertEqual(comment['close'],'not_planned')
        self.assertIn('To submit a corrected proof, open a new issue. This issue now closes.',comment['body'])
        self.assertEqual(calls[1],('PATCH','issues/42',{'state':'closed','state_reason':'not_planned'}))

    def test_a_not_verified_result_gives_its_reason_on_the_second_line_and_keeps_the_site_phrases(self):
        # (g) The site parses the first line and the two NOT_FINAL phrases (bigospeedrun/site data/direct_refresh.py);
        # keep them byte for byte. (d) The reason comes after the first line.
        commit=self.live()['submission']['commit']
        rejected=self.receipt();rejected['kernels']['lean']={'status':'rejected','reason':'lean_kernel_rejection'}
        comment,_=self.status_report(rejected)
        lines=comment['body'].split('\n')
        self.assertRegex(lines[0],r'^<!-- bos-direct-v1 42 [0-9a-f]{64} [0-9a-f]{64} -->$')
        self.assertEqual(lines[1],f'Not verified for source commit `{commit}`.')
        self.assertEqual(lines[2],"Reason: Lean's kernel rejected the proof.")
        self.assertEqual(lines[3],'')
        self.assertIn('This result belongs to an older or closed submission. The current issue is not verified by this result.',s.Path(s.__file__).read_text())
        self.assertIn('This submission remains Claimed; no proof run started.',s.Path(s.__file__).read_text())
        comment,_=self.status_report(self.receipt(),gate={'status':'claimed_only','reason':'record_or_issue_changed','record_gate':{'score':'1/2000','score_relation':'attained'}})
        self.assertIn('remains Claimed; no proof run started',comment['body'])
        # A pass has no reason line.
        comment,_=self.status_report(self.receipt())
        self.assertNotIn('Reason:',comment['body'])

    def test_a_deterministic_setup_failure_closes_and_a_temporary_one_stays_open(self):
        # (e) verifier#89, 2026-10-30: a zip-only repository failed setup and stayed open with no reason.
        missing={'schema_version':1,'status':'setup_failed','steps':[],'kernels':{},'error':'solution module is missing'}
        comment,calls=self.status_report(missing)
        self.assertEqual(comment['close'],'not_planned')
        self.assertIn('Reason: the submission has no Submission.lean at the root of its source. The verifier reads Lean files only, not an archive.',comment['body'])
        self.assertIn('To submit a corrected proof, open a new issue. This issue now closes.',comment['body'])
        self.assertEqual(calls[1],('PATCH','issues/42',{'state':'closed','state_reason':'not_planned'}))
        # Untrusted or unknown error text is never quoted, and a temporary failure stays open.
        for error in ['clone failed: network', 'solution module is missing @everyone', None]:
            receipt={'schema_version':1,'status':'setup_failed','steps':[],'kernels':{}}
            if error:receipt['error']=error
            comment,calls=self.status_report(receipt)
            self.assertNotIn('close',comment);self.assertEqual(len(calls),1)
            self.assertIn('Reason: the verifier setup failed before the proof check. This can be a temporary problem; a maintainer looks at it.',comment['body'])
            self.assertNotIn('network',comment['body']);self.assertNotIn('@everyone',comment['body'])

    def test_ambiguous_result_stays_open(self):
        receipt=self.receipt();receipt['kernels']['lean']['status']='incomplete'
        comment,calls=self.status_report(receipt)
        self.assertNotIn('close',comment)
        self.assertEqual(len(calls),1)

    def test_test_only_result_never_closes(self):
        rejected=self.receipt();rejected['kernels']['lean']['status']='rejected'
        for receipt in [self.receipt(),rejected]:
            comment,calls=self.status_report(receipt,test_only=True)
            self.assertNotIn('close',comment)
            self.assertEqual(len(calls),1)

    def test_claimed_only_result_closes_with_its_claimed_report(self):
        # Lead, 2026-10-23 (PR #52): a claimed-only submission closes; the site keeps it Claimed by the marker.
        comment,calls=self.status_report(self.receipt(),gate={'status':'claimed_only','reason':'record_or_issue_changed','record_gate':{'score':'1/2000','score_relation':'attained'}})
        self.assertNotIn('close',comment)
        self.assertIn('no proof run started',comment['body'])
        live=self.live()
        self.assertEqual(comment['claimed'],live['submission_sha256'])
        self.assertEqual(len(calls),3)
        self.assertTrue(calls[1][2]['body'].startswith(f"<!-- bos-claimed-v1 42 {live['submission_sha256']} -->"))
        self.assertIn('stays listed as Claimed',calls[1][2]['body'])
        self.assertEqual(calls[2],('PATCH','issues/42',{'state':'closed','state_reason':'not_planned'}))

    def test_module_headers_and_manifest(self):
        with tempfile.TemporaryDirectory() as tmp:
            stage=Path(tmp);(stage/'Submission').mkdir();(stage/'Submission/A.lean').write_text('module\npublic import Mathlib\n');(stage/'Submission.lean').write_text('module\npublic import Submission.A\n')
            self.assertEqual(v.plan_sources(stage,'Submission'),[['Submission.A','Submission']])
        self.assertIn('0df444a360eaa60ab8c11dca51a86af692955474',v.lakefile(['Submission'],'profiles/anthropic-lake-manifest.json'))



class BoundDigitsTests(unittest.TestCase):
    """At most 40 digits per integer (Nil, 2026-10-21; issue #35 needed 19)."""
    def sub(self, problem, bound):
        return {'schema_version': 1, 'problem': problem, 'bound': bound, 'repo_url': 'https://github.com/a/b', 'commit': 'a' * 40, 'authors': []}

    def test_19_and_40_digits_are_accepted_and_41_is_not(self):
        for problem, bound in [('3sum', '4800698571997281331/2500000000000000000'), ('dft', '1/' + '9' * 40),
                               ('dft', '1' + '0' * 38 + '1/' + '3' + '0' * 39)]:
            with self.subTest(bound=bound):
                self.assertEqual(s.validate_submission(self.sub(problem, bound))['bound'], bound)
                # The Lean target holds the exact integers, with no rounding.
                n, d = bound.split('/')
                source = s.challenge_source(self.sub(problem, bound))
                self.assertIn(n, source); self.assertIn(d, source)
        for bound in ['9' * 41, '1/' + '9' * 41, '1' + '0' * 40 + '/3']:
            with self.subTest(bound=bound), self.assertRaisesRegex(ValueError, 'at most 40 digits'):
                s.validate_submission(self.sub('dft', bound))
        # The gate compares exact fractions: a 19-digit bound just below the gate qualifies.
        record = {'score': '192027945701/100000000000', 'score_relation': 'attained', 'any_lean_verified_at_bound': True}
        self.assertTrue(s.qualifies_for_run(self.sub('3sum', '4800698571997281331/2500000000000000000'), record))
        self.assertFalse(s.qualifies_for_run(self.sub('3sum', '4800698642525000001/2500000000000000000'), record))


class CommentOnceTests(unittest.TestCase):
    """Two publisher watchers raced on test issue #48 (2026-10-23): the oldest copy stays."""
    LINK = 'https://github.com/bigospeedrun/verifier/actions/runs/1/artifacts/2'

    def race(self, own_id, other_id):
        bot = lambda i: {'id': i, 'user': {'login': 'github-actions[bot]', 'type': 'Bot'}, 'body': f'[Receipt]({self.LINK})'}
        reads, deleted = [0], []
        def call(path, data=None, method=None):
            if method == 'DELETE':
                deleted.append(path); raise ValueError('no JSON body')
            if data is not None:
                return {'id': own_id}
            reads[0] += 1
            # First read: nothing yet (both watchers pass the check); later reads: both copies.
            return [] if reads[0] == 1 else [bot(other_id), bot(own_id)]
        self.assertTrue(s.comment_once(48, f'Checkpoint\n\n[Receipt]({self.LINK})', call))
        return deleted

    def test_the_newer_copy_deletes_itself_and_the_older_stays(self):
        self.assertEqual(self.race(own_id=11, other_id=10), ['issues/comments/11'])
        self.assertEqual(self.race(own_id=10, other_id=11), [])

    def test_a_failed_cleanup_does_not_fail_the_post(self):
        calls = []
        def call(path, data=None, method=None):
            if data is not None:
                calls.append(path); return {'id': 3}
            if calls:
                raise OSError('read failed after the post')
            return []
        self.assertTrue(s.comment_once(48, f'[Receipt]({self.LINK})', call))
        self.assertEqual(calls, ['issues/48/comments'])

    def test_a_comment_without_a_key_is_posted_once_without_a_rescan(self):
        calls = []
        s.comment_once(5, 'plain text', lambda path, data=None, method=None: calls.append((path, data)) or {'id': 1})
        self.assertEqual(calls, [('issues/5/comments', {'body': 'plain text'})])


class ReleaseTests(unittest.TestCase):
    """The lead's derivations entry in the site's review-decisions.json releases a held result (2026-10-23)."""
    DIGEST = 'd' * 64

    def run_release(self, item, pings, decision='approved', head='a' * 40, digest=None):
        import pr_submissions as pr
        calls = []
        decisions = {'derivations': [{'id': ('direct-pr-' if 'pull_request' in item else 'direct-issue-') + '7',
                                      'submission_sha256': digest or self.DIGEST, 'decision': decision}]}
        def api(path, data=None, method=None):
            if data is not None or method:
                calls.append((method, path, data)); return {}
            if path == 'issues/7': return item
            if path == 'pulls/7': return {'head': {'sha': head}}
            if path.startswith('issues/7/comments'): return pings
            raise AssertionError(path)
        with patch.object(s, 'api', side_effect=api), patch.object(pr, 'site_file', return_value=json.dumps(decisions).encode()):
            s.release()
        return calls

    def ping(self, version, digest=None, login='github-actions[bot]'):
        import pr_submissions as pr
        return {'user': {'login': login, 'type': 'Bot' if 'bot' in login else 'User'},
                'body': f'{pr.HOLD_MARKER}7 {digest or self.DIGEST} {version} -->\nHeld'}

    def test_an_approval_merges_a_held_pr_at_its_held_head_only(self):
        pr_item = {'number': 7, 'state': 'open', 'pull_request': {}}
        calls = self.run_release(pr_item, [self.ping('a' * 40)])
        self.assertEqual(calls, [('PUT', 'pulls/7/merge', {'sha': 'a' * 40, 'merge_method': 'squash'}), ('DELETE', 'issues/7/labels/verification-needs-review', None)])
        self.assertEqual(self.run_release(pr_item, [self.ping('a' * 40)], head='b' * 40), [])  # The head moved.
        self.assertEqual(self.run_release(pr_item, [self.ping('a' * 40, login='attacker')]), [])  # Not the bot's ping.
        self.assertEqual(self.run_release(pr_item, [self.ping('a' * 40, digest='e' * 64)]), [])  # Another version's digest.
        self.assertEqual(self.run_release(pr_item, [self.ping('a' * 40)], decision='rejected'), [])
        self.assertEqual(self.run_release(dict(pr_item, state='closed'), [self.ping('a' * 40)]), [])

    def test_an_approval_closes_a_held_issue_with_the_same_body(self):
        item = issue(7)
        calls = self.run_release(item, [self.ping(s.body_hash(item['body']))])
        self.assertEqual([c[:2] for c in calls], [(None, 'issues/7/comments'), ('PATCH', 'issues/7'), ('DELETE', 'issues/7/labels/verification-needs-review')])
        self.assertEqual(calls[1][2], {'state': 'closed', 'state_reason': 'completed'})
        self.assertTrue(calls[0][2]['body'].endswith('\n\nExact discrete Fourier transform board: https://bigospeedrun.com/exact-dft'))
        self.assertEqual(self.run_release(item, [self.ping('f' * 64)]), [])  # The body was edited after the hold.
        # Two held versions of the same submission: the current body matches the second ping.
        self.assertEqual(len(self.run_release(item, [self.ping('f' * 64), self.ping(s.body_hash(item['body']))])), 3)

    def test_a_released_item_that_is_closed_loses_the_review_label_only(self):
        # Issue #56 (2026-10-24): released and closed, but verification-needs-review stayed.
        label = [{'name': 'verification-needs-review'}]
        delete = [('DELETE', 'issues/7/labels/verification-needs-review', None)]
        closed = dict(issue(7), state='closed', state_reason='completed', labels=label)
        self.assertEqual(self.run_release(closed, []), delete)
        self.assertEqual(self.run_release(dict(closed, labels=[]), []), [])  # Already gone: no call.
        self.assertEqual(self.run_release(dict(closed, state_reason='not_planned'), []), [])  # Not a release.
        merged = {'number': 7, 'state': 'closed', 'pull_request': {'merged_at': '2026-10-24T00:00:00Z'}, 'labels': label}
        self.assertEqual(self.run_release(merged, []), delete)
        self.assertEqual(self.run_release(dict(merged, pull_request={'merged_at': None}), []), [])  # Closed unmerged.

    def test_a_label_already_removed_is_not_an_error(self):
        import pr_submissions as pr, urllib.error
        item = issue(7)
        decisions = {'derivations': [{'id': 'direct-issue-7', 'submission_sha256': self.DIGEST, 'decision': 'approved'}]}
        def api(path, data=None, method=None):
            if method == 'DELETE':
                raise urllib.error.HTTPError(path, 404, 'Label does not exist', {}, None)
            if data is not None or method: return {}
            if path == 'issues/7': return item
            return [self.ping(s.body_hash(item['body']))]
        with patch.object(s, 'api', side_effect=api), patch.object(pr, 'site_file', return_value=json.dumps(decisions).encode()), \
             patch('builtins.print') as printed:
            s.release()
        printed.assert_not_called()

    def test_a_scan_out_of_budget_defers_a_qualifying_issue_without_reserving_it(self):
        import queue_lease
        lease = Mock(state={'page': 1, 'offset': 0}, admitted=Mock(return_value=False))
        def report(reader, *args, defer=False):
            if defer: raise derivation.Defer()
            return {'status': 'not_computed', 'hold': False}
        with tempfile.TemporaryDirectory() as tmp:
            old = Path.cwd(); os.chdir(tmp)
            try:
                with patch.dict(os.environ, GITHUB_OUTPUT=str(Path(tmp)/'output')), patch.object(queue_lease, 'acquire', return_value=lease), \
                     patch.object(s, 'current_record', return_value={'score': '1/2000', 'score_relation': 'attained'}), \
                     patch.object(s, 'api', side_effect=lambda p, data=None: [issue(5), issue(6, 'other')] if p.startswith('issues?') else []), \
                     patch.object(s, 'acknowledge'), patch.object(s, 'release'), patch.object(derivation, 'safe_report', side_effect=report):
                    s.select()
                self.assertEqual(list(Path('requests').glob('*.json')), [])
                lease.reserve.assert_not_called()
                self.assertEqual(lease.state, {'page': 1, 'offset': 0})  # The next scan starts at #5 again.
            finally: os.chdir(old)

    def test_safe_report_defers_only_after_other_reads_of_the_scan(self):
        reader = derivation.Reader(limit=0)
        files = lambda: ({'A.lean': ('a' * 40, 1)}, s.REPOSITORY)
        # A fresh reader with no budget at all: not computed, not deferred (an oversized submission cannot wait forever).
        self.assertEqual(derivation.safe_report(reader, 'dft', 'x', 'direct-issue-1', files, defer=True)['reason'], 'API budget used')
        reader.calls = 1
        with self.assertRaises(derivation.Defer):
            derivation.safe_report(reader, 'dft', 'x', 'direct-issue-1', files, defer=True)
        self.assertEqual(derivation.safe_report(reader, 'dft', 'x', 'direct-issue-1', files)['status'], 'not_computed')
        with patch.object(derivation, 'compute', side_effect=s.ScanLimit('scan')):
            with self.assertRaises(derivation.Defer):
                derivation.safe_report(derivation.Reader(), 'dft', 'x', 'direct-issue-1', files, defer=True)


class AcknowledgeTests(unittest.TestCase):
    """Every open submission gets one reply per version at the next scan (issue #35, 2026-10-21)."""
    def setUp(self):
        no_release = patch.object(s, 'release')
        no_release.start(); self.addCleanup(no_release.stop)

    def run_ack(self, items, comments, pulls=None, proof=True, race=None):
        posts, deleted, self.proof_calls = [], [], 0
        ids = iter(range(1000, 2000))
        def api(path, data=None, method=None):
            if method == 'DELETE':
                deleted.append(int(path.rsplit('/', 1)[1])); raise ValueError('empty 204 body')
            if data is not None:
                n = path.split('/')[1]; c = {'id': next(ids), 'user': BOT, 'body': data['body']}
                posts.append((path, data['body'])); comments.setdefault(n, []).append(c)
                if race:  # Another run posted the same reply first (an older id).
                    comments[n].insert(0, {'id': 5, 'user': BOT, 'body': data['body']})
                return dict(c)
            if path.startswith('issues?'):return items
            if '/comments?' in path:
                n = path.split('/')[1]; page = int(path.rsplit('page=', 1)[1])
                return list(comments.get(n, []))[100 * (page - 1):100 * page]
            raise AssertionError(path)
        def candidate(pull):
            self.proof_calls += 1; return proof
        import pr_submissions as pr
        with patch.object(s, 'api', side_effect=api), patch.object(pr, 'api', side_effect=lambda path: (pulls or {})[path]), \
             patch.object(pr, 'proof_candidate', side_effect=candidate):
            s.acknowledge()
        self.deleted = deleted
        return posts

    def issue(self, number, bound='1/2'):
        body = f'### Problem\n\ndft\n\n### Repository URL\n\nhttps://github.com/a/b\n\n### Commit SHA\n\n{"a"*40}\n\n### Bound\n\n{bound}'
        return {'number': number, 'title': s.TITLE + ' x', 'state': 'open', 'body': body}

    def test_a_form_error_is_answered_once_per_version(self):
        item = self.issue(35, '1/' + '9' * 41)
        comments = {}
        posts = self.run_ack([item], comments)
        self.assertEqual(len(posts), 1)
        self.assertIn('an integer or a fraction p/q (no decimals), with at most 40 digits in each', posts[0][1])
        self.assertTrue(posts[0][1].startswith(s.ACK + '35 ' + s.body_hash(item['body'])))
        self.assertEqual(self.run_ack([item], comments), [])
        # An edited body is a new version and gets a new reply.
        edited = dict(item, body=item['body'].replace('1/' + '9' * 41, '1/3'))
        self.assertEqual(len(self.run_ack([edited], comments)), 1)

    def test_a_valid_submission_with_an_earlier_reply_is_skipped(self):
        item = self.issue(36)
        digest = s.submission_hash(s.issue_input(item))
        comments = {'36': [{'id': 1, 'user': BOT, 'body': '<!-- bos-claimed-v1 36 ' + digest + ' -->'}]}
        self.assertEqual(self.run_ack([item], comments), [])
        # A person's comment is no reply.
        comments = {'36': [{'id': 1, 'user': {'login': 'x', 'type': 'User'}, 'body': digest}]}
        posts = self.run_ack([item], comments)
        self.assertEqual(len(posts), 1); self.assertIn('Received.', posts[0][1])

    def test_prs_are_answered_by_kind_and_other_issues_are_skipped(self):
        pr_item = {'number': 40, 'title': 'audit: x', 'pull_request': {}}
        other = {'number': 41, 'title': 'A question', 'state': 'open', 'body': 'hi'}
        pulls = {'pulls/40': {'number': 40, 'head': {'sha': 'c' * 40}, 'changed_files': 1}}
        posts = self.run_ack([pr_item, other], {}, pulls, proof=False)
        self.assertEqual(len(posts), 1); self.assertIn('starts no proof run', posts[0][1])
        posts = self.run_ack([pr_item], {}, pulls, proof=True)
        self.assertIn('verifier queue', posts[0][1])
        # A result comment that names the head counts as the reply, and the PR files are not read for it.
        self.assertEqual(self.run_ack([pr_item], {'40': [{'id': 1, 'user': BOT, 'body': '<!-- bos-pr-v2 40 ' + 'c' * 40 + ' -->'}]}, pulls), [])
        self.assertEqual(self.proof_calls, 0)

    def test_an_overlapping_run_leaves_one_reply(self):
        # Two runs post the same marker: the newer reply (this run's) is deleted, the oldest stays.
        comments = {}
        posts = self.run_ack([self.issue(37)], comments, race=True)
        self.assertEqual(len(posts), 1); self.assertEqual(self.deleted, [1000])
        # Alone, a run deletes nothing.
        self.run_ack([self.issue(38)], {}); self.assertEqual(self.deleted, [])

    def test_a_thread_longer_than_ten_pages_gets_no_reply(self):
        other = [{'id': i, 'user': {'login': 'x', 'type': 'User'}, 'body': 'x'} for i in range(1000)]
        self.assertEqual(self.run_ack([self.issue(39)], {'39': other}), [])
        # Nine full pages and a short tenth page are read: the reply on page 5 counts.
        item = self.issue(42); marker = s.ACK + '42 ' + s.body_hash(item['body']) + ' -->'
        long = other[:950]; long[450] = {'id': 9999, 'user': BOT, 'body': marker}
        self.assertEqual(self.run_ack([item], {'42': long}), [])

    def test_a_failed_item_does_not_stop_the_others(self):
        # 2026-10-21 18:47Z: the comment on the first PR failed (HTTP 403), and no later item got a reply.
        import urllib.error
        items = [{'number': 21, 'title': 'statement: x', 'pull_request': {}}, self.issue(35, '1/3')]
        pulls = {'pulls/21': {'number': 21, 'head': {'sha': 'c' * 40}, 'changed_files': 1}}
        real = s.api
        posts = []
        def api(path, data=None, method=None):
            if data is not None and path == 'issues/21/comments':
                raise urllib.error.HTTPError(path, 403, 'Forbidden', None, None)
            if data is not None:
                posts.append(path); return {'id': 7}
            if path.startswith('issues?'):return items
            if '/comments?' in path:return []
            raise AssertionError(path)
        import pr_submissions as pr
        with patch.object(s, 'api', side_effect=api), patch.object(pr, 'api', side_effect=lambda path: pulls[path]), \
             patch.object(pr, 'proof_candidate', return_value=False):
            s.acknowledge()
        self.assertEqual(posts, ['issues/35/comments'])

    def test_the_pass_has_its_own_cap(self):
        items = [self.issue(n) for n in range(100, 130)]
        with patch.object(s, 'ACK_CALLS', 7):
            with self.assertRaises(s.AckLimit):
                self.run_ack(items, {})

    def test_an_error_stops_only_the_acknowledgement_pass(self):
        import http.client
        for error in [OSError('down'), http.client.IncompleteRead(b'x'), RuntimeError('x'), s.AckLimit('cap')]:
            with self.subTest(error=type(error).__name__), tempfile.TemporaryDirectory() as tmp, \
                 patch.dict(os.environ, GITHUB_OUTPUT=str(Path(tmp) / 'output')), \
                 patch.object(s, 'acknowledge', side_effect=error), patch.object(queue_lease, 'acquire', return_value=None) as acquire:
                s.select_bounded()
                acquire.assert_called_once()  # Selection continues to the lease after the failed pass.


BOT = {'login': 'github-actions[bot]', 'type': 'Bot'}

if __name__=='__main__':unittest.main()
