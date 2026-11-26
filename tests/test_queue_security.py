import base64
import io
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
import urllib.error
from unittest.mock import Mock, patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'scripts'))
import queue_lease as q
import submissions as s


class QueueSecurityTests(unittest.TestCase):
    def setUp(self):
        import derivation
        # The selector's release pass and derivation reports never read GitHub in these tests.
        for target in [patch.object(s, 'release'), patch.object(derivation.Reader, 'get', side_effect=derivation.NotComputed('offline'))]:
            target.start(); self.addCleanup(target.stop)

    def test_active_batch_cannot_be_replaced(self):
        def api(path, data=None, method=None):
            if path.startswith('git/ref/'):return {'object':{'sha':'old'}}
            if path=='git/commits/old':return {'message':json.dumps({'run_id':'12','run_attempt':'1','page':2,'offset':4}),'tree':{'sha':'tree'}}
            if path=='actions/runs/12':return {'status':'in_progress'}
            self.fail('Active lease must not write '+path)
        with patch.dict(os.environ,GITHUB_RUN_ID='13',GITHUB_RUN_ATTEMPT='1'),patch.object(s,'api',side_effect=api):
            self.assertIsNone(q.acquire())

    def test_a_dispatched_run_that_is_not_admitted_fails_and_names_the_holder(self):
        def api(path, data=None, method=None):
            if path.startswith('git/ref/'):return {'object':{'sha':'old'}}
            if path=='git/commits/old':return {'message':json.dumps({'run_id':'12','run_attempt':'1','page':2,'offset':4}),'tree':{'sha':'tree'}}
            if path=='actions/runs/12':return {'status':'in_progress'}
            self.fail('Active lease must not write '+path)
        for event,fails in [('workflow_dispatch',True),('schedule',False)]:
            with tempfile.TemporaryDirectory() as tmp, patch.dict(os.environ,GITHUB_RUN_ID='13',GITHUB_RUN_ATTEMPT='1',
                    GITHUB_EVENT_NAME=event,GITHUB_OUTPUT=str(Path(tmp)/'output')), patch.object(s,'api',side_effect=api), \
                    patch('sys.stdout',new_callable=io.StringIO) as out:
                if fails:
                    with self.assertRaises(SystemExit) as caught:q.main()
                    self.assertEqual(caught.exception.code,1)
                    self.assertIn('not admitted: lease held by run 12',out.getvalue())
                else:
                    q.main();self.assertEqual(out.getvalue(),'')
                self.assertEqual((Path(tmp)/'output').read_text(),'admitted=false\n')

    def test_cas_loser_cannot_launch_batch(self):
        writes=[]
        def api(path,data=None,method=None):
            if path.startswith('git/ref/'):return {'object':{'sha':'old'}}
            if path=='git/commits/old':return {'message':json.dumps({'run_id':'12','run_attempt':'1','page':2,'offset':4}),'tree':{'sha':'tree'}}
            if path=='actions/runs/12':return {'status':'completed'}
            if path=='git/commits':
                self.assertEqual(data['parents'],['old']);return {'sha':'contender'}
            if path.startswith('git/refs/'):
                writes.append(data)
                raise urllib.error.HTTPError('local',422,'not fast forward',{},None)
            self.fail(path)
        with patch.dict(os.environ,GITHUB_RUN_ID='13',GITHUB_RUN_ATTEMPT='1'),patch.object(s,'api',side_effect=api):
            self.assertIsNone(q.acquire())
        self.assertEqual(writes,[{'sha':'contender','force':False}])

    def test_scan_resumes_after_bounded_invalid_candidates(self):
        lease=Mock(state={'page':1,'offset':0},admitted=Mock(return_value=False))
        items=[{'number':i,'user':{'login':str(i)},'state':'open','title':'not a submission'} for i in range(1,51)]
        calls=[]
        def api(path,data=None,method=None):
            calls.append(path)
            return items if path.startswith('issues?') else []
        with tempfile.TemporaryDirectory() as tmp:
            old=Path.cwd();os.chdir(tmp)
            try:
                with patch.dict(os.environ,GITHUB_OUTPUT=str(Path(tmp)/'output')),patch.object(q,'acquire',return_value=lease),patch.object(s,'api',side_effect=api),patch.object(s,'acknowledge'):
                    s.select()
                    self.assertEqual(lease.state,{'page':1,'offset':40})
                    self.assertLessEqual(len(calls),41)
                    self.assertIn('selected=false',Path('output').read_text())
                    s.select()
                    self.assertEqual(lease.state['page'],2)
            finally:os.chdir(old)

    def test_network_budget_rejects_before_another_request(self):
        with patch.object(s,'SCAN_BUDGET',{'calls':400,'deadline':float('inf')}),self.assertRaises(s.ScanLimit):
            s.scan_check('issues/4/comments')

    def test_old_attempt_cannot_restart_after_lease_changes(self):
        replies=[{'object':{'sha':'state'}},{'message':json.dumps({'run_id':'13','run_attempt':'2'})}]
        with patch.dict(os.environ,GITHUB_RUN_ID='13',GITHUB_RUN_ATTEMPT='1'),patch.object(s,'api',side_effect=replies),self.assertRaisesRegex(ValueError,'another run/attempt'):
            q.assert_owner()

    def test_marker_at_comment_101_cannot_replay_admitted_issue(self):
        from test_submissions import issue
        item=issue()
        request=s.issue_request(item,s.issue_input(item))
        key=q.admission_key(request)
        ledger={key}
        lease=Mock(state={'page':1,'offset':0},admitted=Mock(side_effect=lambda k:k in ledger))
        ordinary=[{'user':{'login':'someone','type':'User'},'body':'comment'}]*100
        marker={'user':{'login':'github-actions[bot]','type':'Bot'},
                'body':s.marker_for(42,request['submission_sha256'],request['issue_body_sha256'])}
        calls=[]
        def api(path,data=None,method=None):
            calls.append(path)
            if path.startswith('issues?'):return [item]
            if 'comments' in path:return [marker] if 'page=2' in path else ordinary
            self.fail(path)
        with tempfile.TemporaryDirectory() as tmp:
            old=Path.cwd();os.chdir(tmp)
            try:
                with patch.dict(os.environ,GITHUB_OUTPUT=str(Path(tmp)/'output')),patch.object(q,'acquire',return_value=lease),patch.object(s,'api',side_effect=api),patch.object(s,'current_record') as record,patch.object(s,'acknowledge'):
                    s.select()
                    s.select()  # A second cursor cycle still cannot replay it.
                self.assertFalse(Path('requests/42.json').exists())
                lease.reserve.assert_not_called()
                record.assert_not_called()
            finally:os.chdir(old)
        self.assertFalse(any('page=2' in call for call in calls))

    def test_pr_head_dedup_ignores_comment_history(self):
        import pr_submissions as pr
        head='a'*40
        key=q.admission_key({'route':'pull_request','pr_number':42,'head_sha':head})
        lease=Mock(admitted=Mock(side_effect=lambda candidate:candidate==key))
        with patch.object(pr,'api',return_value={'number':42,'head':{'sha':head}}),patch.object(pr,'inspect_pr') as inspect:
            self.assertIsNone(pr.select_candidate({'number':42},lease))
            inspect.assert_not_called()
        new_key=q.admission_key({'route':'pull_request','pr_number':42,'head_sha':'b'*40})
        self.assertNotEqual(key,new_key)

    def test_admission_record_has_bounded_direct_lookup_and_no_eviction(self):
        key='a'*64
        raw=s.canonical({'schema_version':1,'key':key,'run_id':'12','run_attempt':'1'}).encode()
        lease=q.Lease('commit',{'run_id':'13','run_attempt':'1'},'old-tree')
        with patch.object(s,'api',return_value={'type':'file','size':len(raw),'content':base64.b64encode(raw).decode()}) as api:
            self.assertTrue(lease.admitted(key))
            api.assert_called_once_with('contents/'+q.admission_path(key)+'?ref=commit')
        with patch.object(s,'api',return_value={'sha':'new-tree'}) as api,patch.object(lease,'save') as save:
            lease.reserve('b'*64)
            self.assertEqual(api.call_args.args[1]['base_tree'],'old-tree')
            self.assertEqual(len(api.call_args.args[1]['tree']),1)
            self.assertLess(len(api.call_args.args[1]['tree'][0]['content']),1024)
            save.assert_called_once()

    def test_reservation_failure_emits_no_runnable_request(self):
        from test_submissions import issue
        lease=Mock(state={'page':1,'offset':0},admitted=Mock(return_value=False),reserve=Mock(side_effect=ValueError('CAS failed')))
        with tempfile.TemporaryDirectory() as tmp:
            old=Path.cwd();os.chdir(tmp)
            try:
                with patch.dict(os.environ,GITHUB_OUTPUT=str(Path(tmp)/'output')),patch.object(q,'acquire',return_value=lease),patch.object(s,'api',side_effect=lambda path:[issue()] if path.startswith('issues?') else []),patch.object(s,'current_record',return_value={'score':'1/2000','score_relation':'attained'}),self.assertRaisesRegex(ValueError,'CAS failed'):
                    s.select()
                self.assertFalse(Path('requests/42.json').exists())
                self.assertNotIn('selected=true',Path('output').read_text())
            finally:os.chdir(old)

    def test_no_trusted_workflow_uses_fork_named_concurrency_groups(self):
        workflows=Path(__file__).resolve().parents[1]/'.github/workflows'
        self.assertFalse((workflows/'pr-verify.yml').exists())
        for path in workflows.glob('*.yml'):
            text=path.read_text()
            self.assertNotIn('concurrency:',text)
            self.assertNotIn('pull_request:',text)
            self.assertNotIn('pull_request_target:',text)


if __name__=='__main__':unittest.main()


class FakeGitHub:
    """A tiny in-memory GitHub for the lease ref: commits (message, tree), trees (path -> text), runs and the issue."""
    def __init__(self, issue, old_run='555', old_attempt='1', owner_status='completed', record=True, old_head='b' * 40):
        from test_submissions import issue as make
        self.issue = issue
        self.trees = {'t0': {'queue.json': '{}\n'}}
        self.commits = {'c0': {'message': json.dumps({'schema_version': 1, 'page': 1, 'offset': 0, 'run_id': '444', 'run_attempt': '1'}), 'tree': 't0'}}
        self.head, self.n = 'c0', 0
        self.runs = {'444': {'status': owner_status, 'head_sha': 'd' * 40}, '999': {'status': 'completed', 'head_sha': 'a' * 40}, old_run: {'status': 'completed', 'head_sha': old_head}}
        self.key = q.admission_key(s.issue_request(issue, s.issue_input(issue)))
        if record:
            self.trees['t0'][q.admission_path(self.key)] = s.canonical({'schema_version': 1, 'key': self.key, 'run_id': old_run, 'run_attempt': old_attempt}) + '\n'
        self.writes = []

    def api(self, path, data=None, method=None):
        if path == f"issues/{self.issue['number']}":
            return self.issue
        if path == 'git/ref/' + q.REF:
            return {'object': {'sha': self.head}}
        if path.startswith('git/commits/'):
            return {'message': self.commits[path.split('/')[-1]]['message'], 'tree': {'sha': self.commits[path.split('/')[-1]]['tree']}}
        if path.startswith('actions/runs/') and path.count('/') == 2:
            return self.runs[path.split('/')[-1]]
        if path == 'git/trees':
            self.n += 1
            tree = dict(self.trees[data['base_tree']])
            for entry in data['tree']:
                if entry.get('sha', 1) is None:
                    tree.pop(entry['path'], None)
                else:
                    tree[entry['path']] = entry['content']
            self.trees[f't{self.n}'] = tree
            return {'sha': f't{self.n}'}
        if path == 'git/commits':
            self.n += 1
            self.commits[f'c{self.n}'] = {'message': data['message'], 'tree': data['tree']}
            return {'sha': f'c{self.n}'}
        if path.startswith('git/refs/') and method == 'PATCH':
            if data['force'] is not False or self.head != 'c%d' % (int(data['sha'][1:]) - 1) and False:
                raise AssertionError('the ref must move without force')
            self.head = data['sha']
            self.writes.append(data)
            return {}
        if path.startswith('contents/'):
            name, sha = path[len('contents/'):].split('?ref=')
            text = self.trees[self.commits[sha]['tree']].get(name)
            if text is None:
                raise urllib.error.HTTPError('local', 404, 'missing', {}, None)
            return {'type': 'file', 'size': len(text), 'content': base64.b64encode(text.encode()).decode()}
        raise AssertionError('unexpected API call ' + path)

    def tree(self):
        return self.trees[self.commits[self.head]['tree']]


RECEIPTS = Path(__file__).resolve().parent / 'fixtures' / 'receipts'


def receipt_fixture(name):
    """A real receipt of a public run (the artifact's receipt.json, unchanged), read as data."""
    return json.loads((RECEIPTS / (name + '.json')).read_text())


class RequeueTests(unittest.TestCase):
    NEW = 'a' * 40
    OLD = 'b' * 40

    def run_requeue(self, fake, status='208-timeout-45012852925', trusted=True, reason='dft split fixes the timeout', sha=None, **kw):
        sha = sha or self.NEW
        blobs = {'scripts/x.py': {'sha': '1' * 40, 'mode': '100644'}}
        trust = {'controller_blobs': {}, 'previous_controller_blobs': {'z' * 40: blobs if trusted else {}}}
        with patch.dict(os.environ, GITHUB_RUN_ID='999', GITHUB_RUN_ATTEMPT='1'), patch.object(s, 'api', side_effect=fake.api), \
                patch.object(q, 'controller_blobs', return_value=blobs), patch.object(q, 'site_trust', return_value=trust), \
                patch.object(q, 'old_receipt', return_value=status if isinstance(status, dict) else receipt_fixture(status)) as receipt:
            entry = q.requeue(kw.pop('number', fake.issue['number']), reason, sha, 'maintainer')
        return entry, receipt

    def issue(self, **kw):
        from test_submissions import issue
        return issue(**kw)

    def test_a_timeout_on_our_side_is_requeued_by_removing_exactly_one_record(self):
        fake = FakeGitHub(self.issue(), old_head=self.OLD)
        before = dict(fake.trees['t0'])
        entry, receipt = self.run_requeue(fake)
        receipt.assert_called_once_with('555', '1', 42)
        after = fake.tree()
        self.assertEqual(set(before) - set(after), {q.admission_path(fake.key)})
        self.assertEqual(set(after) - set(before), {f'requeued/42-{self.NEW[:12]}.json'})
        self.assertTrue(all(after[p] == before[p] for p in before if p in after))
        self.assertEqual(json.loads(after[f'requeued/42-{self.NEW[:12]}.json']), entry)
        self.assertEqual((entry['old_run'], entry['old_decision'], entry['old_verifier_commit'], entry['new_verifier_commit'], entry['actor'], entry['run_id']),
                         ('555', 'timeout', self.OLD, self.NEW, 'maintainer', '999'))
        self.assertEqual([w['force'] for w in fake.writes], [False, False])  # the acquire commit, then the requeue commit
        # The scan now sees no reservation for this version of the issue.
        lease = q.Lease(fake.head, {}, 't')
        with patch.object(s, 'api', side_effect=fake.api):
            self.assertFalse(lease.admitted(fake.key))

    def test_the_guard_allows_one_requeue_per_issue_per_verifier_commit(self):
        fake = FakeGitHub(self.issue(), old_head=self.OLD)
        self.run_requeue(fake)
        # The scan admits it again at the next 30-minute scan (a new record by a later run), and it times out again at the same commit.
        fake.trees[fake.commits[fake.head]['tree']][q.admission_path(fake.key)] = s.canonical(
            {'schema_version': 1, 'key': fake.key, 'run_id': '777', 'run_attempt': '1'}) + '\n'
        fake.runs['777'] = {'status': 'completed', 'head_sha': self.NEW}
        with self.assertRaisesRegex(q.Refused, 'already ran on this verifier commit'):
            self.run_requeue(fake)
        # Even with an old run on other code, the guard of this commit refuses a second requeue.
        fake.runs['777']['head_sha'] = self.OLD
        with self.assertRaisesRegex(q.Refused, 'already requeued at verifier commit'):
            self.run_requeue(fake)
        # A newer verifier commit may requeue once more.
        entry, _ = self.run_requeue(fake, sha='c' * 40)
        self.assertEqual(entry['new_verifier_commit'], 'c' * 40)

    def refused(self, fake, pattern, **kw):
        before = dict(fake.trees), len(fake.commits)
        with self.assertRaisesRegex(q.Refused, pattern):
            self.run_requeue(fake, **kw)
        # Nothing but the lease acquire commit (same tree as before) was written.
        self.assertEqual(fake.trees['t0'], before[0]['t0'])
        self.assertEqual(len(fake.trees), len(before[0]))

    def test_refusals_change_no_tree(self):
        fake = FakeGitHub(self.issue(), old_head=self.OLD)
        for name in ['208-passed-final-45048554930', '208-passed-lean-stage-45048554930', '187-chain-passed-44945639361',
                     '207-chain-smoke-passed-44984387435', '157-oom-41997136601', '173-audit-incomplete-42325142385', '61-not-verified-40120914934']:
            with self.subTest(receipt=name):
                self.refused(fake, 'is a verdict on the proof or a stop that is not', status=name)
        self.refused(fake, 'does not list the controller blobs', trusted=False)
        self.refused(FakeGitHub(self.issue(), old_head=self.NEW), 'already ran on this verifier commit')
        self.refused(FakeGitHub(self.issue(), record=False), 'no admission record')
        self.refused(fake, 'printable ASCII', reason='')
        self.refused(fake, 'printable ASCII', reason='x' * 201)
        self.refused(fake, 'printable ASCII', reason='bad\nline')
        self.refused(fake, 'not a number', number='4; echo')
        self.refused(fake, 'full sha', sha='abc')

    OVERFLOW = ("Running nanoda kernel on solution\nnanoda kernel num_threads: 4\n\nthread 'thread_1' (3054) has overflowed its stack\n"
                'fatal runtime error: stack overflow, aborting\nnanoda kernel rejected the solution\nuncaught exception: nanoda exited with 134\n')

    def test_a_nanoda_stack_overflow_is_requeued_once_and_read_from_the_nanoda_log(self):
        # verifier#226 (Lead, 2026-11-26): Lean kernel and axiom audit passed; nanoda overflowed its 32 MiB worker stack. The real
        # receipt of run 45853495131 says only pending_review / ambiguous_failure, so the overflow comes from the last attempt's log.
        import verdicts
        real = receipt_fixture('226-nanoda-stack-45853495131')
        self.assertTrue(verdicts.nanoda_stack_candidate(real))
        self.assertEqual([p.stem for p in RECEIPTS.glob('*.json') if verdicts.nanoda_stack_candidate(receipt_fixture(p.stem))],
                         ['226-nanoda-stack-45853495131'])
        fake = FakeGitHub(self.issue(), old_head=self.OLD)
        with patch.object(q, 'old_nanoda_log', return_value=self.OVERFLOW) as log:
            entry, _ = self.run_requeue(fake, status=real, reason='nanoda stack 256 MiB')
        log.assert_called_once_with('555', '1', 42)
        self.assertEqual(entry['old_decision'], 'nanoda_stack')
        # Refused: no overflow in the log (another nanoda failure), a run that already had the largest stack, a Lean or audit failure.
        for log_text, change in [('uncaught exception: nanoda exited with 1\n', None),
                                 (self.OVERFLOW, lambda r: r['kernels']['nanoda']['attempts'][-1].update(nanoda_stack_mib=4096)),
                                 (self.OVERFLOW, lambda r: r['kernels']['lean'].update(status='rejected')),
                                 (self.OVERFLOW, lambda r: r['axiom_audit'].update(status='incomplete')),
                                 (self.OVERFLOW, lambda r: r.update(verification_stage='lean'))]:
            receipt = receipt_fixture('226-nanoda-stack-45853495131')
            if change:
                change(receipt)
            with self.subTest(log=log_text[:30], change=change is not None), patch.object(q, 'old_nanoda_log', return_value=log_text):
                self.refused(FakeGitHub(self.issue(), old_head=self.OLD), 'is a verdict on the proof or a stop that is not', status=receipt)
        # A run at 1024 MiB may still go to 4096.
        receipt = receipt_fixture('226-nanoda-stack-45853495131'); receipt['kernels']['nanoda']['attempts'][-1]['nanoda_stack_mib'] = 1024
        self.assertTrue(verdicts.nanoda_stack_candidate(receipt))

    def test_the_old_nanoda_log_is_the_last_attempts_part(self):
        log = 'build\nVERIFIER nanoda: oom-kill, the check starts again with 2 nanoda threads\nsecond\n'
        with patch.object(q, 'old_files', return_value={'nanoda.log': log.encode()}):
            self.assertEqual(q.old_nanoda_log('555', '1', 42), 'second\n')
        with patch.object(q, 'old_files', return_value={'nanoda.log': b'only\n'}):
            self.assertEqual(q.old_nanoda_log('555', '1', 42), 'only\n')
        with patch.object(q, 'old_files', return_value={}), self.assertRaisesRegex(q.Refused, 'no nanoda log'):
            q.old_nanoda_log('555', '1', 42)

    def test_a_held_lease_refuses_and_names_the_holder(self):
        fake = FakeGitHub(self.issue(), old_head=self.OLD, owner_status='in_progress')
        with patch.object(q, 'holder', return_value='444'):
            with self.assertRaisesRegex(q.Refused, 'lease held by run 444'):
                self.run_requeue(fake)
        self.assertEqual(fake.writes, [])

    def test_only_an_open_submission_issue_is_requeued(self):
        closed = self.issue()
        closed['state'] = 'closed'
        fake = FakeGitHub(self.issue())
        fake.issue = closed
        with self.assertRaisesRegex(q.Refused, 'not an open submission issue'):
            self.run_requeue(fake)
        pull = self.issue()
        pull['pull_request'] = {'url': 'x'}
        fake.issue = pull
        with self.assertRaisesRegex(q.Refused, 'not an open submission issue'):
            self.run_requeue(fake)
        labelled = self.issue()
        labelled['labels'] = [{'name': 'test'}]
        fake.issue = labelled
        with self.assertRaisesRegex(q.Refused, 'maintainer test issue'):
            self.run_requeue(fake)
        # An edited form is a new key: it has no record, and the scan admits it by itself.
        edited = self.issue(bound='1/7')
        fake.issue = edited
        with self.assertRaisesRegex(q.Refused, 'no admission record'):
            self.run_requeue(fake)

    def test_the_one_rule_for_a_result_without_a_verdict_on_real_receipts(self):
        # verdicts.no_verdict is the site importer's rule (setup / timeout / chain). Real receipts of public runs, unchanged.
        import verdicts
        expected = {'208-timeout-45012852925': 'timeout', '99-timeout-41393097953': 'timeout', '187-timeout-42648121034': 'timeout',
                    '182-timeout-42525033842': 'timeout', '99-setup-41494392206': 'setup', '187-setup-42584814300': 'setup',
                    '208-passed-final-45048554930': None, '208-passed-lean-stage-45048554930': None, '187-chain-passed-44945639361': None,
                    '207-chain-smoke-passed-44984387435': None, '157-oom-41997136601': None, '173-audit-incomplete-42325142385': None,
                    '61-not-verified-40120914934': None, '226-nanoda-stack-45853495131': None}
        self.assertEqual(sorted(expected), sorted(p.stem for p in RECEIPTS.glob('*.json')))
        for name, decision in expected.items():
            with self.subTest(receipt=name):
                self.assertEqual(verdicts.no_verdict(receipt_fixture(name)), decision)
        # No real chain stop exists yet (no result comment names one): these are copies of the real chain receipt of run 44945639361
        # (profile runner github-chain) with the Lean kernel changed to what chain.py writes.
        def chain(reason, status='incomplete'):
            r = receipt_fixture('187-chain-passed-44945639361')
            r['status'] = 'not_verified'
            r['kernels']['lean'] = {'status': status, 'reason': reason}
            return r
        for reason, decision in [('check_chain_cap', 'timeout'), ('build_chain_cap', 'timeout'), ('chain_coverage', 'chain'), ('no_segment_record', 'chain'),
                                 ('no_segment_receipt', 'chain'), ('export_not_run', 'chain'), ('out_of_memory', None), ('disk_limit', None)]:
            with self.subTest(chain_reason=reason):
                self.assertEqual(verdicts.no_verdict(chain(reason)), decision)
        # A rejection or a forbidden axiom is a verdict, never a stop, even inside a timeout receipt.
        rejected = receipt_fixture('208-timeout-45012852925')
        rejected['kernels']['lean'] = {'status': 'rejected'}
        self.assertIsNone(verdicts.no_verdict(rejected))
        forbidden = receipt_fixture('208-timeout-45012852925')
        forbidden['axiom_audit'] = {'status': 'passed', 'reported_axioms': {'Race.bound': ['propext', 'sorryAx']}}
        self.assertIsNone(verdicts.no_verdict(forbidden))
        # A setup failure that is the submission's own fault (SETUP_ERRORS) is final: not requeued.
        own = receipt_fixture('187-setup-42584814300')
        own['error'] = 'solution module is missing'
        self.assertIsNone(verdicts.no_verdict(own))
        # A setup failure after a check started is not a setup failure before any check.
        for change, decision in [({'axiom_audit': {'status': 'passed'}}, None), ({'kernels': {'lean': {'status': 'incomplete'}}}, None),
                                 ({'kernels': {'nanoda': {'status': 'passed'}}}, None), ({'kernels': {'nanoda': {'status': 'pending'}}}, 'setup')]:
            late = dict(receipt_fixture('187-setup-42584814300'), **change)
            self.assertEqual(verdicts.no_verdict(late), decision, change)
        for junk in [None, [], 'x', {'kernels': [], 'axiom_audit': 'x'}]:
            self.assertIsNone(verdicts.no_verdict(junk))

    def test_the_requeue_accepts_the_real_receipts_that_end_without_a_verdict(self):
        for name in ['208-timeout-45012852925', '99-timeout-41393097953', '187-setup-42584814300']:
            with self.subTest(receipt=name):
                entry, _ = self.run_requeue(FakeGitHub(self.issue(), old_head=self.OLD), status=name)
                self.assertEqual(entry['old_decision'], 'setup' if 'setup' in name else 'timeout')

    def test_the_key_is_the_one_that_the_scan_writes(self):
        import derivation
        item = self.issue()
        lease = Mock(state={'page': 1, 'offset': 0}, admitted=Mock(return_value=False))
        with tempfile.TemporaryDirectory() as tmp:
            old = Path.cwd(); os.chdir(tmp)
            try:
                def api(path, data=None, method=None):
                    if path.startswith('issues?'):
                        return [dict(item, labels=[])]
                    return []
                with patch.dict(os.environ, GITHUB_OUTPUT=str(Path(tmp) / 'output')), patch.object(q, 'acquire', return_value=lease), \
                        patch.object(s, 'api', side_effect=api), patch.object(s, 'current_record', return_value={'any_lean_verified_at_bound': False}), \
                        patch.object(s, 'qualifies_for_run', return_value=True), patch.object(s, 'acknowledge'), patch.object(s, 'release'), patch.object(derivation, 'safe_report', return_value={}), \
                        patch.object(derivation, 'safe_post'):
                    s.select()
            finally:
                os.chdir(old)
        self.assertEqual(lease.reserve.call_count, 1)
        self.assertEqual(lease.reserve.call_args[0][0], FakeGitHub(item).key)

    def test_the_blob_set_rule_is_the_importers(self):
        with tempfile.TemporaryDirectory() as tmp:
            import subprocess
            def git(*a):return subprocess.run(['git', '-C', tmp, '-c', 'user.name=T', '-c', 'user.email=t@example.invalid', *a], check=True, capture_output=True, text=True).stdout.strip()
            git('init', '-q')
            for rel, text in {'scripts/a.py': 'a\n', 'docs/x.md': 'd\n', 'submissions/dft/x/A.lean': 's\n', 'auto-research.md': 'r\n', 'auto-research/n.md': 'r\n'}.items():
                path = Path(tmp) / rel
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text)
            git('add', '-A'); git('commit', '-q', '-m', 'one')
            sha = git('rev-parse', 'HEAD')
            blobs = q.controller_blobs(sha, tmp)
            self.assertEqual(sorted(blobs), ['docs/x.md', 'scripts/a.py'])
            self.assertEqual(blobs['scripts/a.py'], {'sha': git('rev-parse', 'HEAD:scripts/a.py'), 'mode': '100644'})
        self.assertTrue(q.site_trusts(blobs, {'controller_blobs': {}, 'previous_controller_blobs': {'x': blobs}}))
        self.assertTrue(q.site_trusts(blobs, {'controller_blobs': blobs}))
        self.assertFalse(q.site_trusts(blobs, {'controller_blobs': {}, 'previous_controller_blobs': {'x': dict(blobs, extra=blobs['docs/x.md'])}}))

    def test_the_old_receipt_is_the_final_one_and_never_the_lean_stage_one(self):
        import io, zipfile, hashlib
        import pr_submissions as pr
        def archive(status):
            buf = io.BytesIO()
            with zipfile.ZipFile(buf, 'w') as z:
                z.writestr('receipt.json', json.dumps({'status': status}))
            return buf.getvalue()
        base = 'verifier-receipt-and-logs-555-1-42'
        raw = archive('timeout')
        final = {'id': 8, 'name': base, 'digest': 'sha256:' + hashlib.sha256(raw).hexdigest()}
        lean = {'id': 7, 'name': base + '-lean', 'digest': 'sha256:' + hashlib.sha256(archive('passed')).hexdigest()}
        with patch.object(s, 'api', return_value={'artifacts': [{'id': 1, 'name': 'other'}, lean, final]}), patch.object(pr, 'api', return_value=raw) as download:
            self.assertEqual(q.old_receipt('555', '1', 42), {'status': 'timeout'})
            download.assert_called_once_with('actions/artifacts/8/zip', raw=True)
        # Only the Lean-stage receipt, or an expired final one: refused ("no final receipt").
        for listed in [[lean], [dict(final, expired=True), lean], [{'id': 1, 'name': 'other'}]]:
            with patch.object(s, 'api', return_value={'artifacts': listed}), self.assertRaisesRegex(q.Refused, 'no final receipt'):
                q.old_receipt('555', '1', 42)
        with patch.object(s, 'api', return_value={'artifacts': [final]}), patch.object(pr, 'api', return_value=raw + b'x'), self.assertRaises(ValueError):
            q.old_receipt('555', '1', 42)  # the artifact digest does not match

    def test_the_log_line_holds_no_workflow_command(self):
        # A refusal text can hold a little data of an issue or a receipt: one printable line, no "::".
        for text in ['bad\n::set-output name=x::y', 'a::b', 'tab\there \x1b[31m', 'x' * 1000]:
            with patch.dict(os.environ, REQUEUE_ISSUE='42', REQUEUE_REASON='r', GITHUB_SHA='a' * 40), patch.object(q, 'requeue', side_effect=q.Refused(text)), \
                    patch('sys.stdout', new_callable=io.StringIO) as out:
                with self.assertRaises(SystemExit) as caught:
                    q.requeue_main()
                self.assertEqual(caught.exception.code, 1)
            line = out.getvalue()
            self.assertEqual(line.count('\n'), 1)
            self.assertTrue(line.startswith('::error::requeue refused: '))
            self.assertNotIn('::', line[len('::error::'):])
            self.assertTrue(line.isascii() and all(32 <= ord(c) < 127 for c in line.rstrip('\n')))
            self.assertLessEqual(len(line), 440)
        # The issue form error repeats no text of the error (a future message could quote the issue).
        fake = FakeGitHub(self.issue())
        with patch.object(s, 'issue_input', side_effect=ValueError('::error::x\n::set-output name=z::1')), patch.object(q, 'controller_blobs', return_value={}), \
                patch.object(q, 'site_trust', return_value={'controller_blobs': {}}), patch.object(s, 'api', side_effect=fake.api):
            with self.assertRaises(q.Refused) as caught:
                q.requeue(42, 'r', 'a' * 40, 'maintainer')
        self.assertNotIn('set-output', str(caught.exception))
        self.assertIn('ValueError', str(caught.exception))

    def test_the_untrusted_path_copy_has_the_sites_three_cases(self):
        # data/direct_refresh.py untrusted_path of the site: submissions/, auto-research.md and auto-research/.
        for path in ['submissions/dft/x/A.lean', 'auto-research.md', 'auto-research/notes.md']:
            self.assertTrue(q.untrusted_path(path), path)
        for path in ['scripts/verifier.py', 'docs/auto-research.md', 'auto-research-notes.md', 'tests/submissions/x', 'submissions', '.github/workflows/submissions.yml']:
            self.assertFalse(q.untrusted_path(path), path)

    def test_the_workflow_runs_the_requeue_alone_and_never_the_scan(self):
        import yaml
        flow = yaml.safe_load((Path(__file__).resolve().parents[1] / '.github/workflows/submissions.yml').read_text())
        jobs = flow['jobs']
        self.assertIn('requeue_issue', flow[True]['workflow_dispatch']['inputs'])
        self.assertEqual(jobs['requeue']['permissions'], {'contents': 'write', 'issues': 'read', 'actions': 'read'})
        self.assertIn("format('{0}', inputs.requeue_issue) != ''", jobs['requeue']['if'])
        self.assertIn("format('{0}', inputs.requeue_issue) == ''", jobs['select']['if'])
        steps = jobs['requeue']['steps']
        self.assertEqual(steps[-1]['run'], 'python3 scripts/queue_lease.py requeue')
        # User values enter as environment variables, never in a shell line.
        self.assertEqual(sorted(steps[-1]['env']), ['GH_TOKEN', 'REQUEUE_ISSUE', 'REQUEUE_REASON'])
        self.assertNotIn('${{', steps[-1]['run'])
