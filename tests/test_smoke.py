import copy
import sys
from pathlib import Path
import unittest
import os
import tempfile
import json
from unittest.mock import patch, Mock
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import smoke
import submissions as s

class SmokeTests(unittest.TestCase):
    def test_only_exact_legacy_fixture_can_be_enabled(self):
        sub={'schema_version':1,'problem':'dft','repo_url':smoke.REPO,'commit':smoke.PIN,'bound':smoke.BOUND,'authors':[]}
        selected={'test_only':True,'live_smoke':smoke.TAG,'submission':smoke.issue_submission(sub)}
        self.assertTrue(smoke.active(selected))
        for field,value in [('test_only',False),('live_smoke','anything')]:
            self.assertFalse(smoke.active(dict(selected,**{field:value})))
        with self.assertRaises(ValueError):smoke.issue_submission(dict(sub,commit='a'*40))

    def test_report_normalizes_only_authenticated_fixed_smoke(self):
        sub=s.validate_submission({'schema_version':1,'problem':'dft','repo_url':smoke.REPO,'commit':smoke.PIN,'bound':smoke.BOUND,'authors':[]})
        selected={'test_only':True,'live_smoke':smoke.TAG,'submission':smoke.issue_submission(sub)}
        with patch.object(s,'issue_input',return_value=sub):
            self.assertEqual(s.report_submission({},selected),selected['submission'])
            self.assertEqual(s.report_submission({},dict(selected,test_only=False)),sub)
        with patch.object(s,'issue_input',return_value=dict(sub,commit='a'*40)):
            with self.assertRaises(ValueError):s.report_submission({},selected)

    def test_pr_smoke_has_fixed_problem_bound_and_test_folder(self):
        selected={'test_only':True,'live_smoke':smoke.TAG,'route':'pull_request',
                  'submission':{'problem':'dft','bound':smoke.BOUND},'source_subdir':'submissions/dft/nmamano-smoke-dft-837dc31'}
        self.assertTrue(smoke.active(selected))
        self.assertFalse(smoke.active(dict(selected,source_subdir='submissions/dft/nmamano-real-proof')))

    def test_smoke_dispatch_requires_scoped_trusted_step(self):
        with tempfile.TemporaryDirectory() as tmp:
            event=Path(tmp)/'event.json';event.write_text(json.dumps({'inputs':{'smoke_route':'pull_request','smoke_number':'2'}}))
            with patch.dict(os.environ,GITHUB_EVENT_NAME='workflow_dispatch',GITHUB_EVENT_PATH=str(event),BOS_SMOKE_DISPATCH=''):
                self.assertIsNone(smoke.requested())
            with patch.dict(os.environ,GITHUB_EVENT_NAME='workflow_dispatch',GITHUB_EVENT_PATH=str(event),BOS_SMOKE_DISPATCH='1'):
                self.assertEqual(smoke.requested()['smoke_route'],'pull_request')


class CatalanSmokeTests(unittest.TestCase):
    """The split-build smoke: a maintainer test issue with the fixture form, test_only, never imported, nothing posted."""
    def setUp(self):
        tmp=tempfile.TemporaryDirectory();self.addCleanup(tmp.cleanup);self.tmp=Path(tmp.name)
        old=Path.cwd();os.chdir(self.tmp);self.addCleanup(os.chdir,old)

    def issue(self,number=48,labels=('test',),association='CONTRIBUTOR',**fields):
        # CONTRIBUTOR: the job token's view of a private organization member (issue #68).
        from test_submissions import issue
        problem,bound,repo,commit=smoke.CATALAN_FIXTURE
        item=issue(number,**{'problem':problem,'bound':bound,'commit':commit,**fields})
        item['body']=item['body'].replace('https://github.com/example/proof',repo)
        return dict(item,labels=[{'name':name} for name in labels],author_association=association)

    def dispatch(self,item=None,actor='Submitter'):
        item=item or self.issue()
        event=self.tmp/'event.json';event.write_text(json.dumps({'inputs':{'smoke_route':'issue','smoke_number':str(item['number'])}}))
        with patch.dict(os.environ,GITHUB_EVENT_NAME='workflow_dispatch',GITHUB_EVENT_PATH=str(event),BOS_SMOKE_DISPATCH='1',
                        GITHUB_OUTPUT=str(self.tmp/'output'),GITHUB_ACTOR=actor),patch.object(s,'api',return_value=item) as api:
            self.assertTrue(smoke.dispatch(None))
        api.assert_called_once_with(f"issues/{item['number']}")
        return item,json.loads(Path(f"requests/{item['number']}.json").read_text())

    def test_no_issue_form_applies_the_test_label(self):
        # The label test admits a Catalan smoke, so only a user with triage rights may set it. An issue form can
        # apply labels by itself (labels: in .github/ISSUE_TEMPLATE); none may apply test (lead, 2026-10-27).
        import re
        forms=sorted((Path(__file__).resolve().parents[1]/'.github/ISSUE_TEMPLATE').iterdir())
        self.assertTrue(forms)
        for form in forms:
            text=form.read_text()
            with self.subTest(form=form.name):
                self.assertNotRegex(text,r'(?im)^\s*labels\s*:')
                self.assertIsNone(re.search(r'(?im)^\s*-?\s*["\']?test["\']?\s*$',text))

    def test_fixture(self):
        self.assertEqual(smoke.CATALAN_FIXTURE,('catalan','1091','https://github.com/bigospeedrun/verifier-smoke-catalan',
                                                'a3d48494df743e8dbf2dd5acb70dbe27759069e0'))

    def test_dispatch_selects_one_split_issue_entry(self):
        item,selected=self.dispatch()
        self.assertEqual(smoke.fixture(selected['submission']),smoke.CATALAN_FIXTURE)
        self.assertEqual(selected['submission'],s.issue_input(item))
        self.assertEqual((selected['test_only'],selected['live_smoke'],selected['lease_kind']),(True,smoke.CATALAN_TAG,'smoke'))
        self.assertTrue(smoke.active(selected));self.assertTrue(smoke.silent(selected))
        out=(self.tmp/'output').read_text()
        self.assertIn('matrix='+s.canonical({'include':[{'issue_number':48,'login':'submitter','route':'issue','split':True}]}),out)
        for field,value in [('test_only',False),('live_smoke',smoke.TAG),('live_smoke',smoke.AS_TAG),('route','pull_request'),
                            ('submission',dict(selected['submission'],bound='1090'))]:
            with self.subTest(field=field,value=value):
                self.assertFalse(smoke.active(dict(selected,**{field:value})))
                self.assertFalse(smoke.silent(dict(selected,**{field:value})))
        # The other smokes are not silent.
        sub=s.validate_submission({'schema_version':1,'problem':'dft','repo_url':smoke.REPO,'commit':smoke.PIN,'bound':smoke.BOUND,'authors':[]})
        self.assertFalse(smoke.silent({'test_only':True,'live_smoke':smoke.TAG,'submission':smoke.issue_submission(sub)}))

    def test_only_a_maintainer_test_issue_with_the_fixture_form(self):
        for item in [self.issue(labels=()),self.issue(labels=('bug',)),
                     self.issue(bound='1090'),self.issue(commit='b'*40)]:
            with self.subTest(labels=item['labels'],association=item['author_association'],body=item['body']),self.assertRaises(ValueError):
                self.dispatch(item)
        # Only the dispatching maintainer's own issue (GITHUB_ACTOR, case-insensitive).
        for actor in ['someone-else','']:
            with self.subTest(actor=actor),self.assertRaises(ValueError):
                self.dispatch(self.issue(),actor=actor)
        # No issue form at all: the existing smoke code refuses it too (issue_input gives None).
        for item in [dict(self.issue(),state='closed'),dict(self.issue(),title='A question')]:
            with self.subTest(item=item['title']),self.assertRaises((ValueError,AttributeError)):
                self.dispatch(item)
        self.assertFalse(Path('requests').exists())

    def test_preflight_binds_the_issue_body_and_skips_the_record_gate(self):
        import queue_lease
        item,selected=self.dispatch()
        Path('request').mkdir(exist_ok=True);Path('request/request.json').write_text(s.canonical(selected))
        with patch.dict(os.environ,GITHUB_OUTPUT=str(self.tmp/'output')),patch.object(queue_lease,'assert_owner') as owner,\
             patch.object(s,'api',return_value=item),patch.object(s,'current_record') as record:
            (self.tmp/'output').write_text('');s.preflight()
            owner.assert_called_once_with(queue_lease.SMOKE_REF);record.assert_not_called()
            self.assertEqual((self.tmp/'output').read_text(),'proceed=true\n')
            # An edited form is no longer the fixture: preflight stops, so no check runs.
            Path('request/request.json').write_text(s.canonical(selected));(self.tmp/'output').write_text('')
            with patch.object(s,'api',return_value=dict(item,body=item['body'].replace('1091','1092'))),self.assertRaises(ValueError):
                s.preflight()
            self.assertEqual((self.tmp/'output').read_text(),'')

    def test_the_report_posts_nothing(self):
        item,selected=self.dispatch()
        Path('request').mkdir(exist_ok=True);Path('request/request.json').write_text(s.canonical(selected))
        Path('result').mkdir();Path('result/receipt.json').write_text('{}')
        artifact={'id':1,'name':'verifier-receipt-and-logs-9-1-48','digest':None,'archive_url':'https://github.com/bigospeedrun/verifier/actions/runs/9/artifacts/1'}
        with patch.dict(os.environ,GITHUB_RUN_ID='9',GITHUB_RUN_ATTEMPT='1',GITHUB_SHA='b'*40,ISSUE_NUMBER='48'),\
             patch.object(s,'receipt_artifact',return_value=artifact),patch.object(s,'api',return_value=item):
            s.report()
        result=json.loads(Path('published/direct-submission.json').read_text())
        self.assertEqual((result['test_only'],result['status'],result['importable']),(True,'fixture_only',False))
        self.assertTrue(json.loads(Path('published-comment.json').read_text())['silent'])
        with patch.object(s,'api') as api,patch.object(s,'comment_once') as comment:
            s.publish()
        api.assert_not_called();comment.assert_not_called()

    def test_the_checkpoint_watcher_posts_nothing(self):
        import live_publish as live
        _,selected=self.dispatch()
        event=self.tmp/'run.json';event.write_text(json.dumps({'workflow_run':{'id':123,'run_attempt':1}}))
        def api(path,data=None):
            if path=='actions/runs/123':return {'run_attempt':1,'status':'in_progress'}
            if path.startswith('actions/runs/123/artifacts'):
                return {'artifacts':[{'id':1,'name':'direct-requests-123-1'},{'id':2,'name':'verifier-receipt-and-logs-123-1-48-lean'}]}
            raise AssertionError(path)
        for value,calls in [(selected,0),(dict(selected,live_smoke=smoke.TAG),1)]:
            raw=s.canonical(value).encode()
            with self.subTest(calls=calls),patch.dict(os.environ,GITHUB_EVENT_PATH=str(event)),patch.object(live.p,'api',side_effect=api),\
                 patch.object(live.p,'validate_run_identity'),patch.object(live,'archive',return_value={'48.json':raw}) as archive,\
                 patch.object(live,'publish_issue') as publish,patch.object(live.p,'label_review') as label,patch.object(live.time,'sleep'):
                live.watch()
            self.assertEqual(publish.call_count,calls);label.assert_not_called()
            self.assertEqual(archive.call_count,1)  # Only the selection artifact is read.

    def test_the_scan_posts_nothing_on_the_test_issue(self):
        import queue_lease
        item=self.issue()
        posts=[]
        def api(path,data=None,method=None):
            if data is not None or method is not None:posts.append(path);return {'id':1}
            if path.startswith('issues?'):return [item]
            if '/comments?' in path:return []
            raise AssertionError(path)
        lease=Mock(state={'page':1,'offset':0},admitted=Mock(return_value=False))
        with patch.dict(os.environ,GITHUB_OUTPUT=str(self.tmp/'output')),patch.object(s,'api',side_effect=api),\
             patch.object(s,'release'),patch.object(queue_lease,'acquire',return_value=lease),patch.object(smoke,'requested',return_value=None):
            s.select_bounded()
        self.assertEqual(posts,[])
        lease.reserve.assert_not_called()
        # Without the label, the acknowledgement pass answers the closed problem as before.
        item=self.issue(labels=())
        with patch.object(s,'api',side_effect=api):
            s.acknowledge()
        self.assertEqual(posts,['issues/48/comments'])

if __name__=='__main__':unittest.main()

class SubsetSumSmokeTests(unittest.TestCase):
    """The Subset Sum smoke before that problem opens (Lead, 2026-11-01): darkhipo's proof, cloned from its own repository
    (issue #94), on a maintainer test issue only, test_only, never imported, nothing posted, no record gate."""
    def setUp(self):
        tmp=tempfile.TemporaryDirectory();self.addCleanup(tmp.cleanup);self.tmp=Path(tmp.name)
        old=Path.cwd();os.chdir(self.tmp);self.addCleanup(os.chdir,old)

    def issue(self,labels=('test',),**fields):
        from test_submissions import issue
        problem,bound,repo,commit=smoke.SS_FIXTURE
        item=issue(95,**{'problem':problem,'bound':bound,'commit':commit,**fields})
        item['body']=item['body'].replace('https://github.com/example/proof',repo)
        return dict(item,labels=[{'name':name} for name in labels])

    def dispatch(self,item,actor='Submitter'):
        event=self.tmp/'event.json';event.write_text(json.dumps({'inputs':{'smoke_route':'issue','smoke_number':'95'}}))
        with patch.dict(os.environ,GITHUB_EVENT_NAME='workflow_dispatch',GITHUB_EVENT_PATH=str(event),BOS_SMOKE_DISPATCH='1',
                        GITHUB_OUTPUT=str(self.tmp/'output'),GITHUB_ACTOR=actor),patch.object(s,'api',return_value=item):
            self.assertTrue(smoke.dispatch(None))
        return json.loads(Path('requests/95.json').read_text())

    def test_fixture(self):
        self.assertEqual(smoke.SS_FIXTURE,('subset-sum','3/4','https://github.com/darkhipo/subset-sum-mitm',
                                           '6c0652068fe17f08ce0087e424a4a8b98bd2664b'))
        self.assertIn('subset-sum',s.CLOSED)

    def test_dispatch_selects_one_silent_issue_entry_while_subset_sum_is_closed(self):
        selected=self.dispatch(self.issue())
        self.assertEqual(smoke.fixture(selected['submission']),smoke.SS_FIXTURE)
        self.assertEqual((selected['test_only'],selected['live_smoke'],selected['lease_kind']),(True,smoke.SS_TAG,'smoke'))
        self.assertTrue(selected['record_gate']['test_only'])
        self.assertTrue(smoke.active(selected));self.assertTrue(smoke.silent(selected))
        self.assertEqual(selected['inputs']['challenge_file'],'challenges/subset-sum/Statement.lean')
        self.assertIn('matrix='+s.canonical({'include':[{'issue_number':95,'login':'submitter','route':'issue'}]}),(self.tmp/'output').read_text())
        for field,value in [('test_only',False),('live_smoke',smoke.CATALAN_TAG),('route','pull_request'),
                            ('submission',dict(selected['submission'],bound='2/3'))]:
            with self.subTest(field=field,value=value):
                self.assertFalse(smoke.active(dict(selected,**{field:value})))

    def test_only_a_maintainer_test_issue_with_the_fixture_form(self):
        for item in [self.issue(labels=()),self.issue(bound='2/3'),self.issue(commit='b'*40)]:
            with self.subTest(body=item['body'],labels=item['labels']),self.assertRaises(ValueError):
                self.dispatch(item)
        with self.assertRaises(ValueError):
            self.dispatch(self.issue(),actor='someone-else')
        self.assertFalse(Path('requests').exists())
