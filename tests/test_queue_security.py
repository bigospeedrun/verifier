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
