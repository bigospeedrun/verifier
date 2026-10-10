import copy
import hashlib
import io
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
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

    def test_auto_outcomes(self):
        req=self.request();receipt=self.receipt()
        self.assertEqual(p.outcome(receipt,req,'success')[0],'merge')
        for kernel in ['lean','nanoda']:
            bad=copy.deepcopy(receipt);bad['kernels'][kernel]['status']='rejected';bad['theorems']['Race.bound'][kernel+'_kernel']='rejected'
            self.assertEqual(p.outcome(bad,req,'failure')[0],'close')
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

    def publish_fixture(self, mutate_pr=None, unsafe=False, conclusion='success', omit_receipt=False, publisher_attempt='2', change_before_close=False, run_event='schedule', artifact_size=None, stage='final', rejection=False):
        request=self.request();receipt=self.receipt();buf=io.BytesIO()
        suffix='-lean' if stage=='lean' else ''
        if stage=='lean':
            receipt['verification_stage']='lean'
            receipt['kernels']['nanoda']={'status':'pending','reason':'advisory_queued'}
            receipt['theorems']['Race.bound']['nanoda_kernel']='pending'
        if rejection:
            receipt['kernels']['nanoda']={'status':'rejected','reason':'nanoda_type_equality_rejection'}
            receipt['theorems']['Race.bound']['nanoda_kernel']='rejected'
        with zipfile.ZipFile(buf,'w') as z:
            z.writestr('pr-request.json',json.dumps(request))
            if not omit_receipt:z.writestr('receipt.json',json.dumps(receipt))
        raw=buf.getvalue();calls=[]
        pr=copy.deepcopy(self.pr)
        if mutate_pr:mutate_pr(pr)
        run={'id':123,'run_attempt':1,'repository':{'full_name':s.REPOSITORY},'head_repository':{'full_name':s.REPOSITORY},'head_sha':'b'*40,'head_branch':'main','path':p.WORKFLOW,'event':'schedule','status':'completed','workflow_id':55,'conclusion':conclusion}
        run['event']=run_event
        pr_reads=0
        def api(path,data=None,method=None,raw=False):
            nonlocal pr_reads
            if data is not None:
                calls.append((path,data,method))
                return {'merged':True,'sha':'d'*40} if path.endswith('/merge') else {}
            if path=='actions/runs/123':return run
            if path=='actions/runs/123/artifacts?per_page=100':return {'artifacts':[{'id':99,'name':'pr-verification-123-1-7'+suffix,'size_in_bytes':len(buf.getvalue()) if artifact_size is None else artifact_size,'expired':False,'digest':'sha256:'+p.digest(buf.getvalue())}]}
            if path=='actions/artifacts/99/zip':return buf.getvalue()
            if path=='pulls/7':
                pr_reads+=1
                if change_before_close and pr_reads>1:
                    pr['head']['sha']='e'*40
                return pr
            if path=='actions/workflows/submissions.yml':return {'id':55}
            raise AssertionError(path)
        with tempfile.TemporaryDirectory() as tmp:
            old=Path.cwd();os.chdir(tmp)
            try:
                event=Path('event.json');event.write_text(json.dumps({'workflow_run':{'id':123,'run_attempt':1}}))
                with patch.dict(os.environ,GITHUB_EVENT_PATH=str(event),GITHUB_SHA='b'*40,GITHUB_RUN_ID='456',GITHUB_RUN_ATTEMPT=publisher_attempt),patch.object(p,'api',side_effect=api),patch.object(p,'inspect_pr',return_value=dict(request,head_sha=pr['head']['sha'])),patch.object(p,'validate_controller',side_effect=p.LayoutError('protected workflow changed') if unsafe else None):
                    artifact=api('actions/runs/123/artifacts?per_page=100')['artifacts'][0]
                    p.publish_pr(artifact,stage=stage)
                result=json.loads(Path('published/pr-submission-7'+suffix+'.json').read_text())
                return result,calls
            finally:os.chdir(old)

    def test_publisher_merge_uses_atomic_sha(self):
        result,calls=self.publish_fixture()
        self.assertEqual(result['disposition'],'merge');self.assertEqual(result['merge_commit'],'d'*40)
        merge=[c for c in calls if c[0].endswith('/merge')][0]
        self.assertEqual(merge[1]['sha'],'a'*40);self.assertEqual(merge[2],'PUT')

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
        self.assertEqual(calls,[])

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



if __name__=='__main__':unittest.main()
