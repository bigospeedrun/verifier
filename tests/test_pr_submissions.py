import copy
import hashlib
import io
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
import urllib.error
from unittest.mock import patch
import zipfile

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import pr_submissions as p
import submissions as s
import verifier as v


class PRTests(unittest.TestCase):
    def setUp(self):
        self.folder = 'submissions/3sum/alice-proof'
        self.manifest = b'{"problem":"3sum","bound":"1999/1000"}\n'
        self.pr = {'number': 7, 'state': 'open', 'changed_files': 2, 'user': {'login': 'alice'},
                   'created_at': '2026-10-10T10:00:00Z',
                   'head': {'sha': 'a'*40, 'repo': {'full_name': 'alice/verifier'}},
                   'base': {'sha': 'b'*40, 'ref': 'main', 'repo': {'full_name': s.REPOSITORY}}}
        self.files = [{'filename': self.folder + '/' + name, 'status': 'added'} for name in ['manifest.json','Submission.lean']]
        self.entries = {x['filename']: {'mode':'100644','type':'blob','sha':p.blob_sha(self.manifest) if x['filename'].endswith('json') else 'c'*40,'size':len(self.manifest)} for x in self.files}

    def request(self):
        sub=s.validate_submission({'schema_version':1,'problem':'3sum','bound':'1999/1000','repo_url':'https://github.com/'+s.REPOSITORY,'commit':'a'*40,'authors':[],'source_subdir':self.folder})
        _, records=p.validate_layout(self.pr,self.files,False,self.entries)
        return {'schema_version':2,'route':'pull_request','test_only':False,'pr_number':7,
                'pr_url':'https://github.com/bigospeedrun/verifier/pull/7','pr_submitter_login':'alice',
                'pr_created_at':self.pr['created_at'],'head_sha':'a'*40,'base_sha':'b'*40,'verifier_commit':'b'*40,
                'submission':sub,'inputs':s.make_request(sub),'submission_sha256':s.submission_hash(sub),
                'source_subdir':self.folder,'manifest_utf8':self.manifest.decode(),'manifest_sha256':p.digest(self.manifest),
                'changed_files':records,'changed_files_sha256':p.digest(s.canonical(records).encode()),'gate':'ready'}

    def receipt(self):
        request=self.request()
        return {'schema_version':1,'checked_at':'2026-10-10T12:00:00Z','request':request['inputs'],'profile':s.selected_profile(request['submission']),
                'theorem_names':['Race.bound'],'theorems':{'Race.bound':{'lean_kernel':'passed','nanoda_kernel':'passed','reported_axioms':['propext']}},
                'kernels':{'lean':{'status':'passed'},'nanoda':{'status':'passed'}},
                'axiom_audit':{'status':'passed','exit_code':0,'reported_axioms':{'Race.bound':['propext']}},
                'generated_challenge_sha256':p.digest(s.challenge_source(request['submission']).encode()),
                'verifier_commit':'b'*40,'run_url':'https://github.com/bigospeedrun/verifier/actions/runs/123','artifact_sha256':{}}

    def test_only_one_new_login_owned_folder(self):
        self.assertEqual(p.validate_layout(self.pr,self.files,False,self.entries)[0],self.folder)
        for filename in ['.github/workflows/pr-verify.yml','scripts/verifier.py','challenges/dft/Evil.lean',
                         'submissions/3sum/bob-proof/Submission.lean',self.folder+'/../evil.lean',self.folder+'/lakefile.lean',self.folder+'/Submission.olean']:
            files=copy.deepcopy(self.files);files[0]['filename']=filename
            with self.subTest(filename=filename),self.assertRaises(p.LayoutError):p.validate_layout(self.pr,files,False,self.entries)
        with self.assertRaises(p.LayoutError):p.validate_layout(self.pr,self.files,True,self.entries)
        files=copy.deepcopy(self.files);files[0]['status']='modified'
        with self.assertRaises(p.LayoutError):p.validate_layout(self.pr,files,False,self.entries)

    def test_symlink_submodule_mode_and_truncated_diff_rejected(self):
        for mode,kind in [('120000','blob'),('160000','commit'),('100755','blob')]:
            entries=copy.deepcopy(self.entries);entries[self.files[0]['filename']].update(mode=mode,type=kind)
            with self.assertRaises(p.LayoutError):p.validate_layout(self.pr,self.files,False,entries)
        with self.assertRaises(p.LayoutError):p.validate_layout(dict(self.pr,changed_files=3),self.files,False,self.entries)

    def test_manifest_exact_fields(self):
        self.assertEqual(p.parse_manifest(self.manifest,'3sum')['bound'],'1999/1000')
        for raw in [b'{"problem":"3sum","bound":"1999/1000","command":"evil"}',
                    b'{"problem":"3sum","bound":"1999/1000","bound":"1"}',
                    b'{"problem":"3sum","bound":"3998/2000"}',b'{"problem":"apsp","bound":"1"}']:
            with self.assertRaises(ValueError):p.parse_manifest(raw,'3sum')

    def test_pr_subdir_bound_into_request(self):
        request=self.request()['inputs'];profile,names=v.validate_request(request)
        self.assertEqual(request['source_subdir'],self.folder);self.assertEqual(names,['Race.bound'])
        request['source_subdir']='../../scripts'
        with self.assertRaises(ValueError):v.validate_request(request)

    def test_prepare_stages_only_pr_lean_files(self):
        selected=self.request()
        def clone(url,sha,dest,label):
            folder=dest/self.folder;folder.mkdir(parents=True)
            (folder/'Submission.lean').write_text('theorem Race.bound : True := by trivial\n')
            (dest/'Submission.lean').write_text('wrong root\n')
        tree=(f'100644 blob {"a"*40}\t{self.folder}/Submission.lean\0'+f'100644 blob {"b"*40}\tSubmission.lean\0').encode()
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);event=root/'request.json';event.write_text(json.dumps(selected))
            with patch.object(v,'ART',root/'artifacts'),patch.object(v,'WORK',root/'work'),patch.object(v,'clone',side_effect=clone),patch.object(v.subprocess,'check_output',return_value=tree),patch.dict(os.environ,BOS_REQUEST_PATH=str(event),BOS_VERIFIER_COMMIT='b'*40):
                v.prepare()
                self.assertIn('theorem Race.bound',(root/'work/stage/Submission.lean').read_text())
                self.assertEqual(v.receipt()['source_file_count'],1)

    def select_with_files(self, paths, statuses=None, changed_files=None):
        class Lease:
            def admitted(self, key): return False
        files=[{'filename':path,'status':'added'} for path in paths]
        for file,previous in zip(files,statuses or []):
            if previous:file.update(status='renamed',previous_filename=previous)
        pr=copy.deepcopy(self.pr);pr['changed_files']=len(files) if changed_files is None else changed_files
        def api(path,*args,**kwargs):
            if path=='pulls/7':return pr
            if path.startswith('pulls/7/files'):
                page=int(path.rsplit('page=',1)[1])
                return files[100*(page-1):100*page]
            raise AssertionError(path)
        with patch.object(p,'api',side_effect=api),patch.dict(os.environ,{'GITHUB_SHA':'b'*40}):
            return p.select_candidate({'number':7},Lease())

    def test_research_and_statement_prs_are_not_proof_candidates(self):
        for paths in [['auto-research/audits/2026-10-14-alice-x/README.md','auto-research/audits/2026-10-14-alice-x/RESULT.json'],
                      ['challenges/subset-sum/Statement.lean','challenges/subset-sum/README.md'],
                      ['auto-research.md']]:
            with self.subTest(paths=paths):self.assertIsNone(self.select_with_files(paths))

    def test_mixed_rename_and_oversized_prs_stay_validated(self):
        cases=[(['auto-research/audits/x/README.md',self.folder+'/Submission.lean'],None,None),
               (['auto-research/audits/x/Submission.lean'],[self.folder+'/Submission.lean'],None),
               (['auto-research/audits/x/README.md'],None,2),
               (['auto-research/audits/x/f%d.md'%i for i in range(501)],None,None)]
        for paths,previous,changed in cases:
            with self.subTest(paths=paths[:2]):
                selected=self.select_with_files(paths,previous,changed)
                self.assertEqual(selected['gate'],'invalid_layout')
                self.assertEqual(p.outcome(None,selected,'success')[0],'close')

    def test_auto_outcomes(self):
        req=self.request();receipt=self.receipt()
        self.assertEqual(p.outcome(receipt,req,'success')[0],'merge')
        for kernel in ['lean','nanoda']:
            bad=copy.deepcopy(receipt);bad['kernels'][kernel]['status']='rejected';bad['theorems']['Race.bound'][kernel+'_kernel']='rejected'
            self.assertEqual(p.outcome(bad,req,'failure')[0],'close')
        bad=copy.deepcopy(receipt);bad['kernels']['lean'].update(status='rejected',reason='lean_compile_error');bad['axiom_audit'].update(status='not_completed_or_rejected',reported_axioms={})
        self.assertEqual(p.outcome(bad,req,'success')[0],'close')
        bad=copy.deepcopy(receipt);bad['axiom_audit'].update(status='invalid_output',reported_axioms={'Race.bound':['sorryAx']})
        self.assertEqual(p.outcome(bad,req,'failure')[0],'close')
        for conclusion in ['cancelled','timed_out','startup_failure']:
            self.assertEqual(p.outcome(receipt,req,conclusion)[0],'keep_open')
        bad=copy.deepcopy(receipt);bad['kernels']['lean']['status']='incomplete'
        self.assertEqual(p.outcome(bad,req,'failure')[0],'keep_open')
        self.assertEqual(p.outcome(None,dict(req,gate='claimed_only'),'success')[0],'claimed_only')
        self.assertEqual(p.outcome(None,req,'failure')[0],'keep_open')

    def test_nanoda_resource_incomplete_can_merge_after_lean_pass(self):
        receipt=self.receipt();receipt['kernels']['nanoda']={'status':'incomplete','reason':'out_of_memory'}
        receipt['theorems']['Race.bound']['nanoda_kernel']='incomplete'
        self.assertEqual(p.outcome(receipt,self.request(),'failure')[0],'merge')
        receipt['kernels']['nanoda']['reason']='unknown'
        self.assertEqual(p.outcome(receipt,self.request(),'failure')[0],'keep_open')

    def test_artifact_zip_digest_and_paths(self):
        def zip_bytes(name):
            out=io.BytesIO()
            with zipfile.ZipFile(out,'w') as z:z.writestr(name,'{}')
            return out.getvalue()
        raw=zip_bytes('pr-request.json');meta={'digest':'sha256:'+p.digest(raw)}
        self.assertIn('pr-request.json',p.read_archive(raw,meta))
        with self.assertRaises(ValueError):p.read_archive(raw,{'digest':'sha256:'+'0'*64})
        raw=zip_bytes('../evil.py')
        with self.assertRaises(ValueError):p.read_archive(raw,{'digest':'sha256:'+p.digest(raw)})

    def test_run_identity_and_fixture_rejection(self):
        run={'repository':{'full_name':s.REPOSITORY},'head_repository':{'full_name':s.REPOSITORY},
             'head_sha':'b'*40,'head_branch':'main','path':p.WORKFLOW,'event':'schedule','status':'completed','workflow_id':55}
        with patch.object(p,'api',return_value={'id':55}):
            p.validate_run(run,self.request(),self.pr)
            for key,value in [('head_sha','0'*40),('event','pull_request'),('path','.github/workflows/evil.yml')]:
                with self.assertRaises(ValueError):p.validate_run(dict(run,**{key:value}),self.request(),self.pr)
            with self.assertRaises(ValueError):p.validate_run(run,dict(self.request(),test_only=True),self.pr)

    def publish_fixture(self, mutate_pr=None, unsafe=False, conclusion='success', omit_receipt=False, publisher_attempt='2', change_before_close=False, run_event='schedule', artifact_size=None, stage='final', rejection=False, merged_by_other=False, hold=False, gate='ready'):
        request=dict(self.request(),gate=gate)
        if hold:request['derivation']={'status':'computed','hold':True,'closest':{'key':'direct-pr-41','url':'https://github.com/bigospeedrun/verifier/pull/41'}}
        receipt=self.receipt();buf=io.BytesIO()
        suffix='-lean' if stage=='lean' else ''
        if stage=='lean':
            receipt['verification_stage']='lean'
            receipt['kernels']['nanoda']={'status':'pending','reason':'advisory_queued'}
            receipt['theorems']['Race.bound']['nanoda_kernel']='pending'
        if rejection:
            receipt['kernels']['nanoda']={'status':'rejected','reason':'nanoda_type_equality_rejection'}
            receipt['theorems']['Race.bound']['nanoda_kernel']='rejected'
        if gate!='ready':
            # A skipped proof leaves verifier.py finalize's placeholder: no provenance, no steps.
            receipt={'schema_version':1,'status':'setup_failed','steps':[],'kernels':{},'run_url':None,'verifier_commit':None,
                     'verification_stage':stage,'total_wall_seconds':0.0,'theorems':{},'artifact_sha256':{}}
        with zipfile.ZipFile(buf,'w') as z:
            z.writestr('pr-request.json',json.dumps(request))
            if not omit_receipt:z.writestr('receipt.json',json.dumps(receipt))
        raw=buf.getvalue();calls=[]
        pr=copy.deepcopy(self.pr)
        if mutate_pr:mutate_pr(pr)
        run={'id':123,'run_attempt':1,'repository':{'full_name':s.REPOSITORY},'head_repository':{'full_name':s.REPOSITORY},'head_sha':'b'*40,'head_branch':'main','path':p.WORKFLOW,'event':'schedule','status':'completed','workflow_id':55,'conclusion':conclusion}
        run['event']=run_event
        pr_reads=0
        pending_merge,self.sleeps=[],[]
        def api(path,data=None,method=None,raw=False):
            nonlocal pr_reads
            if data is not None:
                calls.append((path,data,method))
                if path.endswith('/merge') and merged_by_other:
                    # merged_by_other: 'other' (the other watcher merged first; GitHub declines this merge),
                    # 'lost' (this merge succeeded but its reply failed), 'moved' (merged at a newer head),
                    # 'no' (declined, not merged).
                    if merged_by_other=='other':pr.update(merged=True,merge_commit_sha='d'*40);return {'merged':False}
                    if merged_by_other=='lost':
                        pr.update(merged=True,merge_commit_sha='d'*40)
                        raise urllib.error.HTTPError(path,502,'Bad Gateway',None,None)
                    if merged_by_other=='moved':pr.update(merged=True,merge_commit_sha='d'*40);pr['head']['sha']='e'*40;return {'merged':False}
                    if merged_by_other=='late':pending_merge.append(2);return {'merged':False}  # the other merge shows on the 2nd read
                    return {'merged':False}
                return {'merged':True,'sha':'d'*40} if path.endswith('/merge') else {}
            if path=='actions/runs/123':return run
            if path=='actions/runs/123/artifacts?per_page=100':return {'artifacts':[{'id':99,'name':'pr-verification-123-1-7'+suffix,'size_in_bytes':len(buf.getvalue()) if artifact_size is None else artifact_size,'expired':False,'digest':'sha256:'+p.digest(buf.getvalue())}]}
            if path=='actions/artifacts/99/zip':return buf.getvalue()
            if path=='pulls/7':
                pr_reads+=1
                if pending_merge:
                    pending_merge[0]-=1
                    if pending_merge[0]<=0:pending_merge.clear();pr.update(merged=True,state='closed',merge_commit_sha='d'*40)
                if change_before_close and pr_reads>1:
                    pr['head']['sha']='e'*40
                return pr
            if path=='actions/workflows/submissions.yml':return {'id':55}
            if path.startswith('issues/7/comments?'):return []
            raise AssertionError(path)
        with tempfile.TemporaryDirectory() as tmp:
            old=Path.cwd();os.chdir(tmp)
            try:
                event=Path('event.json');event.write_text(json.dumps({'workflow_run':{'id':123,'run_attempt':1}}))
                with patch.dict(os.environ,GITHUB_EVENT_PATH=str(event),GITHUB_SHA='b'*40,GITHUB_RUN_ID='456',GITHUB_RUN_ATTEMPT=publisher_attempt),patch.object(p,'api',side_effect=api),patch.object(p.time,'sleep',side_effect=self.sleeps.append),patch.object(p,'inspect_pr',return_value=dict(request,head_sha=pr['head']['sha'])),patch.object(p,'validate_controller',side_effect=(unsafe if isinstance(unsafe,Exception) else p.LayoutError('protected workflow changed')) if unsafe else None):
                    artifact=api('actions/runs/123/artifacts?per_page=100')['artifacts'][0]
                    p.publish_pr(artifact,stage=stage)
                published=Path('published/pr-submission-7'+suffix+'.json')
                return (json.loads(published.read_text()) if published.exists() else None),calls
            finally:os.chdir(old)

    def test_publisher_merge_uses_atomic_sha(self):
        result,calls=self.publish_fixture()
        self.assertEqual(result['disposition'],'merge');self.assertEqual(result['merge_commit'],'d'*40)
        merge=[c for c in calls if c[0].endswith('/merge')][0]
        self.assertEqual(merge[1]['sha'],'a'*40);self.assertEqual(merge[2],'PUT')

    def test_a_final_pr_result_links_its_board(self):
        # Lead, 2026-10-25: a final result names the race page in one neutral line.
        def result_comment(**kwargs):
            _,calls=self.publish_fixture(**kwargs)
            return [c[1]['body'] for c in calls if c[0]=='issues/7/comments' and '<!-- bos-pr-v2 ' in c[1]['body']][0]
        self.assertTrue(result_comment().endswith('\n\n3SUM board: https://bigospeedrun.com/3sum'))
        self.assertTrue(result_comment(rejection=True).endswith('\n\n3SUM board: https://bigospeedrun.com/3sum'))
        self.assertNotIn('bigospeedrun.com/3sum',result_comment(hold=True))

    def test_a_derivation_hold_keeps_a_passing_pr_open_at_both_stages(self):
        for stage in ['lean','final']:
            result,calls=self.publish_fixture(hold=True,stage=stage)
            self.assertEqual(result['disposition'],'keep_open');self.assertFalse(result['importable'])
            self.assertIn('Held for maintainer review',result['reason'])
            self.assertFalse([c for c in calls if c[0].endswith('/merge') or c[0]=='pulls/7'])
            self.assertEqual([c[1] for c in calls if c[0]=='issues/7/labels'],[{'labels':['verification-needs-review']}])
            self.assertTrue(result['request']['derivation']['hold'])
            pings=[c[1]['body'] for c in calls if c[0]=='issues/7/comments' and p.HOLD_MARKER in c[1]['body']]
            self.assertEqual(len(pings),1)
            self.assertTrue(pings[0].startswith(f"{p.HOLD_MARKER}7 {self.request()['submission_sha256']} {'a'*40} -->"))
            self.assertIn('[direct-pr-41](https://github.com/bigospeedrun/verifier/pull/41)',pings[0])
            self.assertIn('"id":"direct-pr-7"',pings[0]);self.assertIn('merges this PR',pings[0])
        # A maintainer merged the held PR by hand: the recovery publication is the accepted merge.
        result,calls=self.publish_fixture(hold=True,mutate_pr=lambda pr:pr.update(state='closed',merged=True,merge_commit_sha='d'*40))
        self.assertEqual((result['disposition'],result['importable'],result['merge_commit']),('merge',True,'d'*40))
        # A held proof that Lean rejects still closes.
        result,_=self.publish_fixture(hold=True,rejection=True)
        self.assertEqual(result['disposition'],'close')

    def test_the_hold_ping_quotes_only_validated_links(self):
        calls=[]
        with patch.object(p,'api',side_effect=lambda path,data=None,method=None:calls.append((path,data)) or ([] if data is None else {})):
            p.hold_ping(9,'issue','d'*64,'e'*64,{'closest':{'key':'direct-pr-41](https://evil.example)','url':'https://evil.example'}})
        body=[d['body'] for path,d in calls if path=='issues/9/comments' and d][0]
        self.assertNotIn('evil',body);self.assertIn('an earlier submission',body);self.assertIn('closes this issue',body)
        with self.assertRaises(ValueError):p.hold_ping(9,'issue','bad','e'*64,{})

    def test_a_claimed_only_pr_is_reported_once_as_claimed_only(self):
        # PR #52 (2026-10-23): the placeholder receipt of a skipped run was reported as "Receipt run mismatch".
        result,calls=self.publish_fixture(gate='claimed_only')
        self.assertEqual((result['disposition'],result['importable']),('claimed_only',False))
        comments=[c[1]['body'] for c in calls if c[0]=='issues/7/comments']
        self.assertEqual(len(comments),1);self.assertIn('**claimed_only**',comments[0])
        self.assertFalse([c for c in calls if 'labels' in c[0] or c[0].endswith('/merge')])
        # Lead, 2026-10-23: the PR then closes; the site keeps it Claimed by this report for its head.
        self.assertIn('stays listed as Claimed',comments[0])
        self.assertEqual([c for c in calls if c[0]=='pulls/7'],[('pulls/7',{'state':'closed'},'PATCH')])
        # The Lean checkpoint of a skipped run publishes nothing; the final publication reports the gate.
        result,calls=self.publish_fixture(gate='claimed_only',stage='lean')
        self.assertEqual((result,calls),(None,[]))

    def test_publisher_attempt_and_raw_receipt_hash(self):
        for attempt in ['1','2']:
            result,_=self.publish_fixture(publisher_attempt=attempt)
            self.assertEqual(result['publisher_run_attempt'],attempt)
            self.assertEqual(result['receipt_sha256'],p.digest(json.dumps(self.receipt()).encode()))
            self.assertNotEqual(result['receipt_sha256'],p.digest(s.canonical(self.receipt()).encode()))
            self.assertEqual((result['run_id'],result['run_attempt']),('123','1'))
        result,_=self.publish_fixture(omit_receipt=True)
        self.assertIsNone(result['receipt_sha256'])
        self.assertFalse(result['importable'])

    def test_committed_pr_fixture_raw_receipt_binding(self):
        fixture=ROOT/'tests/fixtures/direct'
        envelope=json.loads((fixture/'pr-envelope.json').read_text())
        raw=(fixture/'pr-receipt.json').read_bytes()
        self.assertEqual(envelope['receipt_sha256'],p.digest(raw))
        self.assertEqual(envelope['receipt'],json.loads(raw))
        self.assertTrue(envelope['test_only'])
        self.assertTrue(envelope['request']['test_only'])
        self.assertFalse(envelope['importable'])

    def test_publication_recovery_after_merge_does_not_merge_twice(self):
        result,calls=self.publish_fixture(mutate_pr=lambda pr:pr.update(state='closed',merged=True,merge_commit_sha='d'*40))
        self.assertTrue(result['importable'])
        self.assertEqual(result['merge_commit'],'d'*40)
        comments=[c for c in calls if c[0]=='issues/7/comments']
        self.assertEqual(len(comments),1)
        self.assertIn('Final verification result',comments[0][1]['body'])
        self.assertIn('nanoda: passed',comments[0][1]['body'])
        self.assertIn('Axiom audit: passed',comments[0][1]['body'])
        self.assertNotIn('nanoda_pending',comments[0][1]['body'])
        self.assertFalse(any(c[0].endswith('/merge') for c in calls))

    def test_changed_head_stays_open_for_new_check(self):
        # Even an incompatible new manifest/diff belongs to the newer run.
        result,calls=self.publish_fixture(mutate_pr=lambda pr:pr['head'].update(sha='e'*40),unsafe=True)
        self.assertEqual(result['disposition'],'keep_open')
        self.assertFalse(result['importable'])
        self.assertFalse(any(c[0].endswith('/merge') or c[2]=='PATCH' or c[0].endswith('/labels') for c in calls))

    def test_unsafe_controller_at_verified_head_closes(self):
        result,calls=self.publish_fixture(unsafe=True)
        self.assertEqual(result['disposition'],'close')
        self.assertFalse(any(c[0].endswith('/merge') for c in calls))
        self.assertTrue(any(c[2]=='PATCH' and c[1]=={'state':'closed'} for c in calls))

    def test_an_unreadable_trust_list_keeps_the_pr_open_at_publication(self):
        for stage in ['lean','final']:
            with self.subTest(stage=stage):
                result,calls=self.publish_fixture(unsafe=p.TrustUnavailable('Trusted verifier revisions are unavailable (URLError); review required'),stage=stage)
                self.assertEqual(result['disposition'],'keep_open')
                self.assertFalse(any(c[0].endswith('/merge') for c in calls))
                self.assertFalse(any(c[1]=={'state':'closed'} for c in calls))

    def test_a_declined_merge_of_a_merged_verified_head_is_the_merge(self):
        # The other watcher merged first, or this merge succeeded and its reply was lost: an importable merge, no review.
        for stage in ['lean','final']:
            for case in ['other','lost']:
                with self.subTest(stage=stage,case=case):
                    result,calls=self.publish_fixture(stage=stage,merged_by_other=case)
                    self.assertEqual((result['disposition'],result['importable'],result['merge_commit']),('merge',True,'d'*40))
                    self.assertFalse(any('labels' in c[0] or '@nmamano' in str(c[1]) for c in calls))
        # Merged at a newer head: the newer commit has its own check.
        result,calls=self.publish_fixture(merged_by_other='moved')
        self.assertEqual((result['disposition'],result['importable'],result['merge_commit']),('keep_open',False,None))
        self.assertIn('newer commit',result['reason'])
        # 2026-11-01, #91: two publisher runs of one verify run; the other merge shows only on a later read.
        for stage in ['lean','final']:
            with self.subTest(stage=stage,case='late'):
                result,calls=self.publish_fixture(stage=stage,merged_by_other='late')
                self.assertEqual((result['disposition'],result['importable'],result['merge_commit']),('merge',True,'d'*40))
                self.assertFalse(any('labels' in c[0] or '@nmamano' in str(c[1]) for c in calls))
                self.assertEqual(self.sleeps,[3])
        # Declined at the same head and not merged: review, with the label and the ping, after the short re-reads.
        result,calls=self.publish_fixture(merged_by_other='no')
        self.assertEqual(self.sleeps,list(p.MERGE_SETTLE_SECONDS))
        self.assertEqual((result['disposition'],result['importable']),('keep_open',False))
        self.assertTrue(any(c[0].endswith('/labels') for c in calls))
        self.assertTrue(any('@nmamano' in str(c[1]) for c in calls))

    def test_lean_checkpoint_merges_before_nanoda(self):
        result,calls=self.publish_fixture(stage='lean')
        self.assertEqual(result['disposition'],'merge')
        self.assertEqual(result['verification_stage'],'lean')
        self.assertEqual(result['receipt']['kernels']['nanoda']['status'],'pending')
        self.assertTrue(any(c[0].endswith('/merge') for c in calls))

    def test_nanoda_rejection_blocks_already_merged_proof(self):
        result,calls=self.publish_fixture(rejection=True,mutate_pr=lambda pr:pr.update(state='closed',merged=True,merge_commit_sha='d'*40))
        self.assertEqual(result['disposition'],'blocked')
        self.assertFalse(result['importable'])
        self.assertEqual(result['merge_commit'],'d'*40)
        self.assertTrue(any('@nmamano' in c[1].get('body','') for c in calls))
        self.assertFalse(any(c[0].endswith('/merge') for c in calls))

    def test_close_rechecks_head_after_rejection(self):
        result,calls=self.publish_fixture(unsafe=True,change_before_close=True)
        self.assertEqual(result['disposition'],'keep_open')
        self.assertIn('close skipped',result['reason'])
        self.assertFalse(any(c[2]=='PATCH' for c in calls))

    def test_untrusted_run_and_oversized_metadata_reject_before_download(self):
        with self.assertRaisesRegex(ValueError,'Untrusted'):
            self.publish_fixture(run_event='pull_request')
        with self.assertRaisesRegex(ValueError,'API size'):
            self.publish_fixture(artifact_size=p.MAX_ARCHIVE+1)

    def test_stream_download_has_hard_cap_without_content_length(self):
        stream=io.BytesIO(b'x'*1025);stream.headers={}
        with patch.object(p,'MAX_ARCHIVE',1024),self.assertRaisesRegex(ValueError,'download limit'):
            p.bounded_read(stream)
        self.assertEqual(stream.tell(),1025)
        stream=io.BytesIO(b'small');stream.headers={'Content-Length':'1025'}
        with patch.object(p,'MAX_ARCHIVE',1024),self.assertRaises(ValueError):p.bounded_read(stream)
        self.assertEqual(stream.tell(),0)

    def test_cancelled_run_stays_open_labeled(self):
        result,calls=self.publish_fixture(conclusion='cancelled')
        self.assertEqual(result['disposition'],'keep_open')
        self.assertTrue(any(c[0]=='issues/7/labels' for c in calls))
        self.assertFalse(any(c[2]=='PATCH' for c in calls))



    def test_a_running_verify_run_may_show_queued_between_jobs(self):
        # 2026-10-20 20:47:59Z: the select job had ended and the check job had not started; the
        # watcher read 'queued' and failed with 'Untrusted verification workflow'.
        run={'id':123,'run_attempt':1,'repository':{'full_name':s.REPOSITORY},'head_repository':{'full_name':s.REPOSITORY},'head_sha':'b'*40,'head_branch':'main','path':p.WORKFLOW,'event':'schedule','workflow_id':55}
        with patch.object(p,'api',return_value={'id':55}):
            for status in ['queued','waiting','pending','requested','in_progress','completed']:
                p.validate_run_identity(dict(run,status=status),allow_running=True)
            for status in ['queued','in_progress']:
                with self.assertRaisesRegex(ValueError,'Untrusted'):p.validate_run_identity(dict(run,status=status))
            with self.assertRaisesRegex(ValueError,'Untrusted'):p.validate_run_identity(dict(run,status='queued',event='pull_request'),allow_running=True)

    def test_a_result_comment_is_posted_once_per_receipt(self):
        url='https://github.com/'+s.REPOSITORY+'/actions/runs/123/artifacts/456'
        body='Lean checkpoint recorded: Lean Verified.\n\n[Lean checkpoint receipt and logs]('+url+')'
        bot={'login':'github-actions[bot]','type':'Bot'}
        def call_with(comments):
            posts=[]
            def call(path,data=None,method=None):
                if data is None:return comments
                posts.append((path,data));return {}
            return call,posts
        # A second watcher finds the bot comment with the same receipt link and posts nothing.
        call,posts=call_with([{'user':bot,'body':body}])
        self.assertFalse(s.comment_once(42,body,call));self.assertEqual(posts,[])
        # Another receipt, or the same link quoted by a person, does not count.
        for comments in [[{'user':bot,'body':body.replace('/456','/457')}],[{'user':{'login':'someone','type':'User'},'body':body}]]:
            call,posts=call_with(comments)
            self.assertTrue(s.comment_once(42,body,call));self.assertEqual(posts,[('issues/42/comments',{'body':body})])
        # The scan is bounded: ten full pages without an answer need review.
        call,posts=call_with([{'user':{'login':'x','type':'User'},'body':'x'}]*100)
        with self.assertRaisesRegex(ValueError,'bounded scan'):s.comment_once(42,body,call)

    def test_the_review_ping_is_posted_once_per_run_attempt(self):
        bot={'login':'github-actions[bot]','type':'Bot'}
        comments,posts=[],[]
        def api(path,data=None,method=None):
            if path=='labels' or path.endswith('/labels'):return {}
            if data is None:return list(comments)
            posts.append(data['body']);comments.append({'user':bot,'body':data['body']});return {}
        with patch.object(p,'api',side_effect=api):
            # Three publisher watchers of one run (PR #29, 2026-10-21) post one ping.
            for _ in range(3):p.label_review(29,'39515983587 1')
            self.assertEqual(len(posts),1)
            self.assertIn('@nmamano',posts[0]);self.assertTrue(posts[0].startswith('<!-- bos-review-ping 29 39515983587 1 -->'))
            # A ping can reach a merged PR (a nanoda block after a Lean merge): it never says the PR stays open.
            self.assertNotIn('stays open',posts[0])
            # Another run attempt pings again.
            p.label_review(29,'39515983587 2')
            self.assertEqual(len(posts),2)


class ControllerTrustTests(unittest.TestCase):
    """validate_controller over a fake Git API: a commit must hold exactly the protected files
    of one trusted verifier revision (the site's direct-trust.json list, or this checkout)."""
    def setUp(self):
        for f in [p.commit_tree,p.git_tree,p.recursive_tree,p.protected_entries,p.trusted_controllers]:f.cache_clear()
        self.addCleanup(lambda:[f.cache_clear() for f in [p.commit_tree,p.git_tree,p.recursive_tree,p.protected_entries,p.trusted_controllers]])
        old={'scripts/verifier.py':('100644','1'*40),'.github/workflows/verify.yml':('100644','2'*40),'challenges/dft/A.lean':('100644','3'*40)}
        self.current=dict(old,**{'scripts/verifier.py':('100644','4'*40)})
        self.commits={'old':dict(old,**{'README.md':('100644','5'*40),'submissions/dft/x/Submission.lean':('100644','6'*40)}),
                      'current':dict(self.current)}
        blobs=lambda files:{k:{'sha':v[1],'mode':v[0]} for k,v in files.items() if not k.startswith('submissions/')}
        self.trust={'controller_blobs':blobs(self.commits['old']),'previous_controller_blobs':{'c'*40:blobs({**self.commits['old'],'scripts/verifier.py':('100644','7'*40)})}}
        self.trust_raw=json.dumps(self.trust).encode()
        self.read_error=None

    def api(self,path,*args,**kwargs):
        if path.startswith('git/commits/'):return {'tree':{'sha':'T|'+path.rsplit('/',1)[1]+'|'}}
        if path.startswith('git/trees/T|'):
            ref,recursive=path[len('git/trees/'):].split('?')[0],path.endswith('?recursive=1')
            _,commit,folder=ref.split('|')
            prefix=folder+'/' if folder else ''
            entries,seen=[],set()
            for name,(mode,sha) in self.commits[commit].items():
                if not name.startswith(prefix):continue
                rest=name[len(prefix):].split('/')
                if recursive:
                    for i in range(1,len(rest)):
                        sub='/'.join(rest[:i])
                        if sub not in seen:seen.add(sub);entries.append({'path':sub,'type':'tree','mode':'040000','sha':'T|'+commit+'|'+prefix+sub})
                    entries.append({'path':'/'.join(rest),'type':'blob','mode':mode,'sha':sha})
                elif len(rest)==1:entries.append({'path':rest[0],'type':'blob','mode':mode,'sha':sha})
                elif rest[0] not in seen:seen.add(rest[0]);entries.append({'path':rest[0],'type':'tree','mode':'040000','sha':'T|'+commit+'|'+prefix+rest[0]})
            return {'tree':entries,'truncated':False}
        if path.startswith('issues/') and path.endswith('/comments') or 'comments?' in path:return self.comments(path,*args)
        raise AssertionError(path)

    def read(self,req,opener,parse,path):
        # The trust read uses the opener that drops the token on a redirect off api.github.com.
        assert any(isinstance(h,p.PublicRedirect) for h in opener.__self__.handlers)
        if self.read_error:raise self.read_error
        blob=p.blob_sha(self.trust_raw)
        return {'commits/main':{'sha':'9'*40},'contents/data/direct-trust.json?ref='+'9'*40:{'sha':blob},
                'git/blobs/'+blob:{'content':__import__('base64').b64encode(self.trust_raw).decode()}}[path]

    def check(self,*commits):
        with patch.object(p,'api',side_effect=self.api),patch.object(s,'github_read_retry',side_effect=self.read),\
             patch.object(p,'local_entries',return_value=frozenset((k,)+v for k,v in self.current.items())),patch.dict(os.environ,GH_TOKEN='x'):
            p.validate_controller(*commits)

    def test_an_older_trusted_revision_passes_and_an_untrusted_one_does_not(self):
        # A PR branched from an older trusted revision needs no update after a verifier push.
        self.check('old','current')
        for i,change in enumerate([{'scripts/verifier.py':('100644','8'*40)},{'scripts/evil.py':('100644','8'*40)},
                       {'scripts/verifier.py':('100755','1'*40)},{'patches/x.patch':('100644','8'*40)}]):
            with self.subTest(change=change):
                self.commits[f'pr{i}']=dict(self.commits['old'],**change)
                with self.assertRaisesRegex(p.LayoutError,'every trusted'):self.check(f'pr{i}')
                # The run controller is checked the same way.
                with self.assertRaisesRegex(p.LayoutError,'every trusted'):self.check('old',f'pr{i}')
        # A removed protected file is a different revision too.
        self.commits['removed']={k:v for k,v in self.commits['old'].items() if k!='challenges/dft/A.lean'}
        with self.assertRaises(p.LayoutError):self.check('removed')
        # A protected directory that is a symlink or a file is no trusted revision.
        for mode in ['120000','100644']:
            with self.subTest(mode=mode):
                self.commits['flat'+mode]={k:v for k,v in self.commits['old'].items() if not k.startswith('scripts/')}
                self.commits['flat'+mode]['scripts']=(mode,'8'*40)
                with self.assertRaisesRegex(p.LayoutError,'every trusted'):self.check('flat'+mode)
        # Files outside the protected directories do not matter.
        self.commits['readme']=dict(self.commits['old'],**{'README.md':('100644','8'*40)})
        self.check('readme')

    def test_an_unreadable_trust_list_keeps_the_pr_open(self):
        import urllib.error
        import http.client
        for error in [urllib.error.URLError('down'),ValueError('bad'),ConnectionResetError('reset'),TimeoutError('slow'),http.client.IncompleteRead(b'x')]:
            with self.subTest(error=error):
                self.read_error=error;p.trusted_controllers.cache_clear()
                with self.assertRaises(p.TrustUnavailable) as ctx:self.check('old')
                self.assertNotIsInstance(ctx.exception,p.LayoutError)
        # A trust blob that does not match its hash is refused.
        self.read_error=None;self.trust_raw=b'{}';p.trusted_controllers.cache_clear()
        real=self.read
        self.read=lambda req,o,r,path:dict(real(req,o,r,path),sha='0'*40) if path.startswith('contents/') else real(req,o,r,path)
        with self.assertRaises(p.TrustUnavailable):self.check('old')

    def test_selection_spends_no_run_on_an_untrusted_branch_and_asks_once(self):
        self.commits['pr']=dict(self.commits['old'],**{'scripts/verifier.py':('100644','8'*40)})
        posted,comments=[],[]
        def comment_api(path,data=None,*args):
            if data is None:return list(comments)
            posted.append(data['body']);comments.append({'user':{'login':'github-actions[bot]','type':'Bot'},'body':data['body']});return {}
        self.comments=comment_api
        pr={'number':7,'head':{'sha':'pr'},'base':{'sha':'b'*40},'user':{'login':'alice'}}
        class Lease:
            def admitted(self,key):return False
        api=lambda path,*a,**k:pr if path=='pulls/7' else self.api(path,*a,**k)
        with patch.object(p,'api',side_effect=api),patch.object(s,'github_read_retry',side_effect=self.read),\
             patch.object(p,'local_entries',return_value=frozenset((k,)+v for k,v in self.current.items())),\
             patch.object(p,'proof_candidate',return_value=True),patch.object(p,'inspect_pr',return_value={'head_sha':'pr'}),\
             patch.object(s,'current_record') as record,patch.dict(os.environ,GH_TOKEN='x',GITHUB_SHA='b'*40):
            for _ in range(2):self.assertIsNone(p.select_candidate({'number':7},Lease()))
            record.assert_not_called()
            self.assertEqual(len(posted),1);self.assertIn('Update branch',posted[0])
            self.assertTrue(posted[0].startswith('<!-- bos-stale-controller-v1 7 pr -->'))
            # A branch from an older trusted revision is selected.
            pr['head']['sha']='old'
            with patch.object(p,'inspect_pr',return_value={'head_sha':'old','submission':{'problem':'dft'},'pr_url':'u'}),patch.object(s,'qualifies_for_run',return_value=True):
                self.assertEqual(p.select_candidate({'number':7},Lease())['gate'],'ready')

if __name__=='__main__':unittest.main()

class FinalCommentTests(unittest.TestCase):
    def test_repeated_publication_reuses_final_comment(self):
        marker='<!-- bos-pr-final-v2 7 head 123 1 -->'
        body=marker+'\nFinal verification result.'
        existing={'id':9,'body':body,'user':{'login':'github-actions[bot]','type':'Bot'}}
        with patch.object(p,'api',return_value=[existing]) as api:
            p.publish_final_comment(7,marker,body)
            self.assertEqual(api.call_count,1)
        with patch.object(p,'api',side_effect=[[existing],{}]) as api:
            p.publish_final_comment(7,marker,body+' updated')
            self.assertEqual(api.call_args.args[0],'issues/comments/9')
            self.assertEqual(api.call_args.kwargs['method'],'PATCH')

    def test_final_comment_after_page_one_and_untrusted_marker(self):
        marker='<!-- bos-pr-final-v2 7 head 123 1 -->';body=marker+'\nFinal'
        user={'id':8,'body':body,'user':{'login':'submitter','type':'User'}}
        bot={'id':9,'body':body,'user':{'login':'github-actions[bot]','type':'Bot'}}
        with patch.object(p,'api',side_effect=[[user]*100,[bot]]) as api:
            p.publish_final_comment(7,marker,body)
            self.assertEqual(api.call_count,2)
        with patch.object(p,'api',side_effect=[[user],{}]) as api:
            p.publish_final_comment(7,marker,body)
            self.assertEqual(api.call_args.args,('issues/7/comments',{'body':body}))

