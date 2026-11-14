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
                                           '8b105f01848fc0e370abfa3a23ed5c3de463f321'))

    def test_dispatch_selects_one_silent_issue_entry(self):
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


class SnakySmokeTests(SubsetSumSmokeTests):
    """The Snaky smoke that must pass before that problem opens (Lead, 2026-11-02): darkhipo's proof of the bound 20,
    cloned from its own repository (issue #106), on a maintainer test issue only, test_only, silent, no record gate."""
    def issue(self,labels=('test',),**fields):
        from test_submissions import issue
        problem,bound,repo,commit=smoke.SNAKY_FIXTURE
        item=issue(95,**{'problem':problem,'bound':bound,'commit':commit,**fields})
        item['body']=item['body'].replace('https://github.com/example/proof',repo)
        return dict(item,labels=[{'name':name} for name in labels])

    def test_fixture(self):
        self.assertEqual((smoke.SNAKY_FIXTURE,smoke.SNAKY_TAG),(('snaky','20','https://github.com/darkhipo/snaky-twenty',
                                                                 'f6248dc39a05a6c5665240d860d2dbb95db707d9'),'snaky-f6248dc-v1'))
        self.assertEqual(smoke.SILENT[smoke.SNAKY_TAG],smoke.SNAKY_FIXTURE)
        self.assertNotIn('snaky',s.CLOSED)

    def test_dispatch_selects_one_silent_issue_entry(self):
        selected=self.dispatch(self.issue())
        self.assertEqual(smoke.fixture(selected['submission']),smoke.SNAKY_FIXTURE)
        self.assertEqual((selected['test_only'],selected['live_smoke'],selected['lease_kind']),(True,smoke.SNAKY_TAG,'smoke'))
        self.assertTrue(selected['record_gate']['test_only'])
        self.assertTrue(smoke.active(selected));self.assertTrue(smoke.silent(selected))
        self.assertEqual(selected['inputs']['challenge_file'],'challenges/other-snaky/VerifierStatement.lean')
        for field,value in [('test_only',False),('live_smoke',smoke.SS_TAG),('route','pull_request'),
                            ('submission',dict(selected['submission'],bound='19'))]:
            with self.subTest(field=field,value=value):
                self.assertFalse(smoke.active(dict(selected,**{field:value})))

    def test_only_a_maintainer_test_issue_with_the_fixture_form(self):
        for item in [self.issue(labels=()),self.issue(bound='19'),self.issue(bound='21'),self.issue(commit='b'*40)]:
            with self.subTest(body=item['body'],labels=item['labels']),self.assertRaises(ValueError):
                self.dispatch(item)
        with self.assertRaises(ValueError):
            self.dispatch(self.issue(),actor='someone-else')
        self.assertFalse(Path('requests').exists())


class SnakyMutationTests(SubsetSumSmokeTests):
    """The Snaky runs that must fail before that problem opens (Lead, 2026-11-02, verifier #106): our own repository,
    proofs by sorry, each on a maintainer test issue only, test_only, silent, no record gate."""
    def issue(self,labels=('test',),tag='snaky-m2-cell-eca2430-v1',**fields):
        from test_submissions import issue
        problem,bound,repo,commit=smoke.SNAKY_MUTATIONS[tag]
        item=issue(95,**{'problem':problem,'bound':bound,'commit':commit,**fields})
        item['body']=item['body'].replace('https://github.com/example/proof',repo)
        return dict(item,labels=[{'name':name} for name in labels])

    def test_fixture(self):
        repo='https://github.com/bigospeedrun/verifier-smoke-snaky'
        self.assertEqual({tag:(b,c[:7]) for tag,(p,b,r,c) in smoke.SNAKY_MUTATIONS.items() if (p,r)==('snaky',repo)},
                         {'snaky-control-c89f809-v1':('20','c89f809'),'snaky-m1-bound19-c89f809-v1':('19','c89f809'),
                          'snaky-m2-cell-eca2430-v1':('20','eca2430'),'snaky-m3-symmetry-73041ba-v1':('20','73041ba'),
                          'snaky-m4-freshness-299e232-v1':('20','299e232'),'snaky-m5-legality-9ddfaee-v1':('20','9ddfaee')})
        # Snaky opened on 2026-11-03 after these runs.
        self.assertNotIn('snaky',s.CLOSED)

    def test_dispatch_selects_one_silent_issue_entry(self):
        for tag,pinned in smoke.SNAKY_MUTATIONS.items():
            with self.subTest(tag=tag):
                selected=self.dispatch(self.issue(tag=tag))
                self.assertEqual(smoke.fixture(selected['submission']),pinned)
                self.assertEqual((selected['test_only'],selected['live_smoke'],selected['lease_kind']),(True,tag,'smoke'))
                self.assertTrue(selected['record_gate']['test_only'])
                self.assertTrue(smoke.active(selected));self.assertTrue(smoke.silent(selected))
                self.assertEqual(selected['inputs']['challenge_file'],'challenges/other-snaky/VerifierStatement.lean')
                for field,value in [('test_only',False),('live_smoke',smoke.SS_TAG),('route','pull_request'),
                                    ('submission',dict(selected['submission'],bound='18'))]:
                    with self.subTest(field=field,value=value):
                        self.assertFalse(smoke.active(dict(selected,**{field:value})))

    def test_only_a_maintainer_test_issue_with_the_fixture_form(self):
        # Another bound or commit is no fixture: 21 is in range, and the m2 commit with the bound 19 is not pinned.
        for item in [self.issue(labels=()),self.issue(bound='21'),self.issue(bound='19'),self.issue(commit='b'*40)]:
            with self.subTest(body=item['body'],labels=item['labels']),self.assertRaises(ValueError):
                self.dispatch(item)
        with self.assertRaises(ValueError):
            self.dispatch(self.issue(),actor='someone-else')
        self.assertFalse(Path('requests').exists())


class DirectedSsspSmokeTests(SubsetSumSmokeTests):
    """The directed SSSP runs before that problem opens (Nil's GO, 2026-11-03): our own scratch repository, one branch per
    case (Lead, 2026-11-03), on a maintainer test issue only, test_only, silent, no record gate."""
    TAGS = {smoke.SSSP_TAG: smoke.SSSP_FIXTURE, **smoke.SSSP_MUTATIONS}

    def issue(self,labels=('test',),tag=None,**fields):
        from test_submissions import issue
        problem,bound,repo,commit=self.TAGS[tag or smoke.SSSP_TAG]
        item=issue(95,**{'problem':problem,'bound':bound,'commit':commit,**fields})
        item['body']=item['body'].replace('https://github.com/example/proof',repo)
        return dict(item,labels=[{'name':name} for name in labels])

    def test_fixture(self):
        repo='https://github.com/bigospeedrun/sssp-lean-scratch'
        self.assertEqual({tag:(b,c[:7]) for tag,(p,b,r,c) in self.TAGS.items() if (p,r)==('directed-sssp',repo)},
                         {'sssp-9891923-v1':('n log^3/4 ; n log^11/12','9891923'),
                          'sssp-control-5238e61-v1':('n log^3/4 ; n log^11/12','5238e61'),
                          'sssp-m1-cap-floor-9be59eb-v1':('n log^3/4 ; n log^11/12','9be59eb'),
                          'sssp-m2-b-5238e61-v1':('n log^4/5 ; n log^11/12','5238e61'),
                          'sssp-m3-time-5238e61-v1':('n log^3/4 ; n log^5/6','5238e61'),
                          'sssp-m4-fallback-f06285b-v1':('n log^3/4 ; n log^11/12','f06285b'),
                          'sssp-m5-exact-a922982-v1':('n log^3/4 ; n log^11/12','a922982')})
        self.assertTrue(set(self.TAGS.items())<=set(smoke.SILENT.items()))
        self.assertNotIn('directed-sssp',s.CLOSED)

    def test_dispatch_selects_one_silent_issue_entry(self):
        for tag,pinned in self.TAGS.items():
            with self.subTest(tag=tag):
                selected=self.dispatch(self.issue(tag=tag))
                self.assertEqual(smoke.fixture(selected['submission']),pinned)
                self.assertEqual((selected['test_only'],selected['live_smoke'],selected['lease_kind']),(True,tag,'smoke'))
                self.assertTrue(selected['record_gate']['test_only'])
                self.assertTrue(smoke.active(selected));self.assertTrue(smoke.silent(selected))
                self.assertEqual(selected['inputs']['challenge_file'],'challenges/directed-sssp/VerifierStatement.lean')
                for field,value in [('test_only',False),('live_smoke',smoke.SS_TAG),('route','pull_request'),
                                    ('submission',dict(selected['submission'],bound='n ; n log'))]:
                    with self.subTest(field=field,value=value):
                        self.assertFalse(smoke.active(dict(selected,**{field:value})))

    def test_only_a_maintainer_test_issue_with_the_fixture_form(self):
        # Another bound or commit is no fixture: the smoke bound on another commit, or the control with another bound.
        for item in [self.issue(labels=()),self.issue(bound='n ; n log'),self.issue(commit='b'*40),
                     self.issue(tag='sssp-control-5238e61-v1',bound='n log^1/2 ; n log')]:
            with self.subTest(body=item['body'],labels=item['labels']),self.assertRaises(ValueError):
                self.dispatch(item)
        with self.assertRaises(ValueError):
            self.dispatch(self.issue(),actor='someone-else')
        self.assertFalse(Path('requests').exists())

    def test_the_agent_line_of_a_maintainer_test_issue(self):
        # An agent opens the test issue with the agent line (as #127, 2026-11-03). The smoke path removes it before the
        # form is read; the body digest still binds the whole body. A real submission with the line is a form error.
        import queue_lease
        line='This is an agent for Nil (BOS Integrations), writing for [Big O Speedrun](https://bigospeedrun.com).\n\n'
        item=self.issue();item['body']=line+item['body']
        selected=self.dispatch(item)
        self.assertEqual(smoke.fixture(selected['submission']),smoke.SSSP_FIXTURE)
        self.assertEqual(selected['submission'],s.parse_body(item['body'][len(line):]))
        self.assertEqual(selected['issue_body_sha256'],s.body_hash(item['body']))
        Path('request').mkdir(exist_ok=True);Path('request/request.json').write_text(s.canonical(selected))
        with patch.dict(os.environ,GITHUB_OUTPUT=str(self.tmp/'output')),patch.object(queue_lease,'assert_owner'),\
             patch.object(s,'api',return_value=item),patch.object(s,'current_record') as record:
            (self.tmp/'output').write_text('');s.preflight()
            record.assert_not_called()
            self.assertEqual((self.tmp/'output').read_text(),'proceed=true\n')
        self.assertEqual(s.report_submission(item,selected),selected['submission'])
        for text in [item['body'],item['body'].replace('\n','\r\n')]:
            with self.subTest(text=text),self.assertRaises(ValueError):
                s.parse_body(text)
        with self.assertRaises(ValueError):
            s.issue_input(item)
        # Only a pinned fixture, only one exact line, only at the top.
        form=self.issue()['body']
        for body in [line+self.issue(bound='n ; n log')['body'],line+line+form,form+line,
                     line.replace('Nil','Bob')+form,line.replace('.com)','.com/x)')+form,line[:-1]+form]:
            with self.subTest(body=body),self.assertRaises(ValueError):
                self.dispatch(dict(self.issue(),body=body))


class PrimeGapsSmokeTests(SubsetSumSmokeTests):
    """The prime gaps runs before that problem opens (task cbea6e9e): our own fixture repository, one branch per case,
    on a maintainer test issue only, test_only, silent, no record gate."""
    TAGS = {smoke.PG_TAG: smoke.PG_FIXTURE, **smoke.PG_MUTATIONS}

    def issue(self,labels=('test',),tag=None,**fields):
        from test_submissions import issue
        problem,bound,repo,commit=self.TAGS[tag or smoke.PG_TAG]
        item=issue(95,**{'problem':problem,'bound':bound,'commit':commit,**fields})
        item['body']=item['body'].replace('https://github.com/example/proof',repo)
        return dict(item,labels=[{'name':name} for name in labels])

    def test_fixture(self):
        repo='https://github.com/bigospeedrun/verifier-smoke-prime-gaps'
        self.assertEqual({tag:(b,c[:7]) for tag,(p,b,r,c) in self.TAGS.items() if (p,r)==('prime-gaps',repo)},
                         {'prime-gaps-abc6a6e-v1':('246','abc6a6e'),'prime-gaps-control-1b31b82-v1':('246','1b31b82'),
                          'prime-gaps-m1-bound245-1b31b82-v1':('245','1b31b82'),'prime-gaps-m2-strict-ff005c1-v1':('246','ff005c1'),
                          'prime-gaps-m3-eventually-f707281-v1':('246','f707281'),'prime-gaps-m4-two-steps-ce76e48-v1':('246','ce76e48'),
                          'prime-gaps-m5-prime-de38d4d-v1':('246','de38d4d')})
        self.assertTrue(set(self.TAGS.items())<=set(smoke.SILENT.items()))
        self.assertNotIn('prime-gaps',s.CLOSED)

    def test_dispatch_selects_one_silent_issue_entry(self):
        for tag,pinned in self.TAGS.items():
            with self.subTest(tag=tag):
                selected=self.dispatch(self.issue(tag=tag))
                self.assertEqual(smoke.fixture(selected['submission']),pinned)
                self.assertEqual((selected['test_only'],selected['live_smoke'],selected['lease_kind']),(True,tag,'smoke'))
                self.assertTrue(selected['record_gate']['test_only'])
                self.assertTrue(smoke.active(selected));self.assertTrue(smoke.silent(selected))
                self.assertEqual(selected['inputs']['challenge_file'],'challenges/prime-gaps/Statement.lean')

    def test_only_a_maintainer_test_issue_with_the_fixture_form(self):
        for item in [self.issue(labels=()),self.issue(bound='240'),self.issue(commit='b'*40),
                     self.issue(tag='prime-gaps-control-1b31b82-v1',bound='244')]:
            with self.subTest(body=item['body'],labels=item['labels']),self.assertRaises(ValueError):
                self.dispatch(item)
        with self.assertRaises(ValueError):
            self.dispatch(self.issue(),actor='someone-else')
        self.assertFalse(Path('requests').exists())


class ThreeSatSmokeTests(SubsetSumSmokeTests):
    """The 3-SAT runs before that problem opens (task 07840cc3, verifier #192): our own fixture repository, one branch per
    case, on a maintainer test issue only, test_only, silent, no record gate. They run on the check chain."""
    TAGS = {smoke.SAT_TAG: smoke.SAT_FIXTURE, **smoke.SAT_MUTATIONS}

    def issue(self,labels=('test',),tag=None,**fields):
        from test_submissions import issue
        problem,bound,repo,commit=self.TAGS[tag or smoke.SAT_TAG]
        item=issue(95,**{'problem':problem,'bound':bound,'commit':commit,**fields})
        item['body']=item['body'].replace('https://github.com/example/proof',repo)
        return dict(item,labels=[{'name':name} for name in labels])

    def test_fixture(self):
        repo='https://github.com/bigospeedrun/verifier-smoke-3sat'
        self.assertEqual({tag:(b,c[:7]) for tag,(p,b,r,c) in self.TAGS.items() if (p,r)==('3sat',repo)},
                         {'3sat-f76c997-v1':('1/2','f76c997'),'3sat-control-a11e206-v1':('1/2','a11e206'),
                          '3sat-m1-bound3-5-a11e206-v1':('3/5','a11e206'),'3sat-m2-width-e92f108-v1':('1/2','e92f108'),
                          '3sat-m3-verdict-2639f4c-v1':('1/2','2639f4c'),'3sat-m4-uniform-1872c8e-v1':('1/2','1872c8e'),
                          '3sat-m5-clause-667994f-v1':('1/2','667994f')})
        self.assertTrue(set(self.TAGS.items())<=set(smoke.SILENT.items()))
        self.assertIn('3sat',s.CLOSED)

    def test_dispatch_selects_one_silent_issue_entry(self):
        for tag,pinned in self.TAGS.items():
            with self.subTest(tag=tag):
                selected=self.dispatch(self.issue(tag=tag))
                self.assertEqual(smoke.fixture(selected['submission']),pinned)
                self.assertEqual((selected['test_only'],selected['live_smoke'],selected['lease_kind']),(True,tag,'smoke'))
                self.assertTrue(selected['record_gate']['test_only'])
                self.assertTrue(smoke.active(selected));self.assertTrue(smoke.silent(selected))
                self.assertEqual(selected['inputs']['challenge_file'],'challenges/3sat/VerifierStatement.lean')

    def test_only_a_maintainer_test_issue_with_the_fixture_form(self):
        for item in [self.issue(labels=()),self.issue(bound='2/5'),self.issue(commit='b'*40),
                     self.issue(tag='3sat-control-a11e206-v1',bound='1/3')]:
            with self.subTest(body=item['body'],labels=item['labels']),self.assertRaises(ValueError):
                self.dispatch(item)
        with self.assertRaises(ValueError):
            self.dispatch(self.issue(),actor='someone-else')
        self.assertFalse(Path('requests').exists())


class HeilbronnSmokeTests(SubsetSumSmokeTests):
    """The Heilbronn runs before that problem opens (Lead, 2026-11-03, verifier #105): our own repository, on a
    maintainer test issue only, test_only, silent, no record gate. The smoke has the bound 0, which the public form refuses."""
    TAGS = {smoke.HB_TAG: smoke.HB_FIXTURE, **smoke.HB_MUTATIONS}

    def issue(self,labels=('test',),tag=None,**fields):
        from test_submissions import issue
        problem,bound,repo,commit=self.TAGS[tag or smoke.HB_TAG]
        item=issue(95,**{'problem':problem,'bound':bound,'commit':commit,**fields})
        item['body']=item['body'].replace('https://github.com/example/proof',repo)
        return dict(item,labels=[{'name':name} for name in labels])

    def test_fixture(self):
        repo='https://github.com/bigospeedrun/verifier-smoke-heilbronn'
        self.assertEqual({tag:(b,c[:7]) for tag,(p,b,r,c) in self.TAGS.items() if (p,r)==('heilbronn-triangle',repo)},
                         {'heilbronn-42a4e7a-v1':('0','42a4e7a'),'heilbronn-control-c471bc6-v1':('1/50893237','c471bc6'),
                          'heilbronn-m1-bound-c471bc6-v1':('1/50893238','c471bc6'),'heilbronn-m2-area-c869f25-v1':('1/50893237','c869f25'),
                          'heilbronn-m3-square-27734ae-v1':('1/50893237','27734ae'),'heilbronn-m4-constant-6c77d88-v1':('1/50893237','6c77d88'),
                          'heilbronn-m5-distinct-9a86923-v1':('1/50893237','9a86923')})
        self.assertTrue(set(self.TAGS.items())<=set(smoke.SILENT.items()))
        # Heilbronn opened on 2026-11-03 after these runs; the public form still refuses 0.
        self.assertNotIn('heilbronn-triangle',s.CLOSED)

    def test_dispatch_selects_one_silent_issue_entry(self):
        for tag,pinned in self.TAGS.items():
            with self.subTest(tag=tag):
                selected=self.dispatch(self.issue(tag=tag))
                self.assertEqual(smoke.fixture(selected['submission']),pinned)
                self.assertEqual((selected['test_only'],selected['live_smoke'],selected['lease_kind']),(True,tag,'smoke'))
                self.assertTrue(selected['record_gate']['test_only'])
                self.assertTrue(smoke.active(selected));self.assertTrue(smoke.silent(selected))
                self.assertEqual(selected['inputs']['challenge_file'],'challenges/heilbronn-triangle/VerifierStatement.lean')
                for field,value in [('test_only',False),('live_smoke',smoke.SS_TAG),('route','pull_request'),
                                    ('submission',dict(selected['submission'],bound='1/7'))]:
                    with self.subTest(field=field,value=value):
                        self.assertFalse(smoke.active(dict(selected,**{field:value})))
        # The smoke's own form passes the report and preflight readers only for the active smoke.
        selected=self.dispatch(self.issue())
        self.assertEqual(s.report_submission(dict(self.issue(),state='open'),selected)['bound'],'0')
        with self.assertRaisesRegex(ValueError,'must be positive'):
            s.report_submission(dict(self.issue(),state='open'),dict(selected,test_only=False))

    def test_only_a_maintainer_test_issue_with_the_fixture_form(self):
        # Another bound or commit is no fixture: the bound 0 on another commit, or the smoke commit with another bound.
        for item in [self.issue(labels=()),self.issue(bound='1/7'),self.issue(commit='b'*40),
                     self.issue(tag='heilbronn-control-c471bc6-v1',bound='0')]:
            with self.subTest(body=item['body'],labels=item['labels']),self.assertRaises(ValueError):
                self.dispatch(item)
        with self.assertRaises(ValueError):
            self.dispatch(self.issue(),actor='someone-else')
        self.assertFalse(Path('requests').exists())
        # The public scan reads the same form as a form error.
        with self.assertRaisesRegex(ValueError,'must be positive for heilbronn-triangle'):
            s.issue_input(dict(self.issue(),state='open'))

    def test_preflight_reads_the_smoke_form_with_bound_0(self):
        import queue_lease
        item=dict(self.issue(),state='open')
        selected=self.dispatch(item)
        Path('request').mkdir(exist_ok=True);Path('request/request.json').write_text(s.canonical(selected))
        with patch.dict(os.environ,GITHUB_OUTPUT=str(self.tmp/'output')),patch.object(queue_lease,'assert_owner'),\
             patch.object(s,'api',return_value=item),patch.object(s,'current_record') as record:
            (self.tmp/'output').write_text('');s.preflight()
            record.assert_not_called()
            self.assertEqual((self.tmp/'output').read_text(),'proceed=true\n')

