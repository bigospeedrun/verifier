import base64
import hashlib
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
import urllib.error
from unittest.mock import Mock, patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import submissions as s
import smoke

CHALLENGE = ROOT / 'challenges/average-sensitivity'
REPO, PIN = 'https://github.com/Anchen-AI4Math/average-sensitivity-lean', 'cb8c10538e613329be16f9a949d0d75a4c7c67f0'


def body(bound='1881/500', repo=REPO, commit=PIN):
    return (f'### Problem\n\naverage-sensitivity\n\n### Repository URL\n\n{repo}\n\n### Commit SHA\n\n{commit}\n\n'
            f'### Bound\n\n{bound}\n')


def issue(number=60, **kwargs):
    return {'number': number, 'state': 'open', 'title': '[Lean submission] test', 'body': body(**kwargs),
            'user': {'login': 'submitter'}, 'created_at': '2026-10-23T12:00:00Z', 'updated_at': '2026-10-23T12:00:00Z'}


class StatementTests(unittest.TestCase):
    def test_the_verifier_statement_is_the_reviewed_files_joined(self):
        # One self-contained challenge: staging Statement.lean's import would take Model.lean from the submitter.
        model = (CHALLENGE / 'OAI/Combinatorics/GotsmanLinial/Model.lean').read_text()
        first, rest = (CHALLENGE / 'Statement.lean').read_text().split('\n', 1)
        self.assertEqual(first, 'import OAI.Combinatorics.GotsmanLinial.Model')
        joined = (CHALLENGE / 'VerifierStatement.lean').read_text()
        self.assertEqual(joined, model + rest)
        self.assertTrue(all(line.startswith('import Mathlib.') for line in joined.splitlines() if line.startswith('import')))
        profile = json.loads((ROOT / 'profiles/direct.json').read_text())['average-sensitivity']
        self.assertEqual(profile['challenge_sha256'], hashlib.sha256((ROOT / profile['challenge_file']).read_bytes()).hexdigest())
        # The frozen OpenAI model: openai/math@1581d4c lean/OAI/Combinatorics/GotsmanLinial/Model.lean.
        self.assertEqual(hashlib.sha256(model.encode()).hexdigest(), 'babc05672496b5525c163c87b9945597754a46f3fb89c98ab43e06fa52ba7f0d')

    def test_target_and_bound_range(self):
        sub = s.parse_body(body())
        source = s.challenge_source(sub)
        self.assertTrue(source.startswith((CHALLENGE / 'VerifierStatement.lean').read_text()))
        self.assertTrue(source.endswith('theorem Race.bound : BigOSpeedrun.AverageSensitivity.Bound ((1881 : ℚ) / 500) := by\n  sorry\n'))
        self.assertEqual(s.parse_body(body('8'))['bound'], '8')
        for bad in ['17/2', '3.762']:
            with self.assertRaises(ValueError):
                s.parse_body(body(bad))
        self.assertTrue(s.qualifies_for_run(sub, {'score': '8', 'score_relation': 'attained', 'any_lean_verified_at_bound': False}))
        self.assertFalse(s.qualifies_for_run(sub, {'score': '1881/500', 'score_relation': 'attained', 'any_lean_verified_at_bound': True}))


class OtherRecordTests(unittest.TestCase):
    def gate(self, claims=(), direct=None, prove2me=None, issue_url='https://github.com/bigospeedrun/verifier/issues/60'):
        rows = {'families': [{'slug': 'average-sensitivity', 'direction': 'lower', 'baseline': {'exactValue': '8'}, 'claims': list(claims)}]}
        files = {'src/lib/other-bounds.json': json.dumps(rows).encode(),
                 'data/direct-other.json': None if direct is None else json.dumps({'boards': {'other-average-sensitivity': {'claims': direct}}}).encode(),
                 'data/prove2me.json': None if prove2me is None else json.dumps({'boards': {'other-average-sensitivity': {'claims': prove2me}}}).encode()}
        with patch.object(s, 'site_files', return_value=('c' * 40, files)):
            return s.current_record('average-sensitivity', issue_url)

    def test_the_profile_range_gates_until_a_lean_verified_claim_exists(self):
        claimed = {'handle': 'canghaimeng', 'value': '399/125', 'evidence': 'claimed', 'url': 'x'}
        record = self.gate([claimed])
        self.assertEqual((record['score'], record['leader_ids'], record['any_lean_verified_at_bound']), ('8', ['profile-range'], False))
        self.assertEqual(record['problem_id'], 'other/average-sensitivity')

    def test_the_best_lean_verified_claim_of_any_source_gates(self):
        direct = [{'handle': 'direct-issue-61', 'value': '1881/500', 'evidence': 'lean-verified', 'url': 'https://github.com/bigospeedrun/verifier/issues/61'}]
        hand = {'handle': 'someone', 'value': '3.9', 'evidence': 'lean-verified', 'url': 'y'}
        record = self.gate([hand], direct=direct)
        self.assertEqual((record['score'], record['leader_ids'], record['any_lean_verified_at_bound']), ('1881/500', ['direct-issue-61'], True))
        # The candidate's own issue never gates itself; a value that is not exact is skipped.
        record = self.gate([hand, {'handle': 'z', 'value': '\\approx 3', 'evidence': 'lean-verified', 'url': 'z'}], direct=direct,
                           issue_url='https://github.com/bigospeedrun/verifier/issues/61')
        self.assertEqual(record['score'], '39/10')
        record = self.gate(prove2me=[{'handle': 'prove2me-3-5', 'value': '3.5', 'evidence': 'lean-verified', 'url': 'p'}])
        self.assertEqual(record['score'], '7/2')

    def test_site_files_reads_one_commit_and_tolerates_a_missing_file(self):
        def read(req, open_request, read_response, path):
            if path == 'commits/main':
                return {'sha': 'c' * 40}
            if 'direct-other' in path:
                raise urllib.error.HTTPError(path, 404, 'Not Found', None, None)
            self.assertIn('?ref=' + 'c' * 40, path)
            return {'content': base64.b64encode(b'{}').decode()}
        with patch.dict(os.environ, GH_TOKEN='t'), patch.object(s, 'github_read_retry', side_effect=read):
            sha, files = s.site_files(['src/lib/other-bounds.json', 'data/direct-other.json'])
        self.assertEqual((sha, files), ('c' * 40, {'src/lib/other-bounds.json': b'{}', 'data/direct-other.json': None}))

    def test_site_files_reads_a_large_file_from_its_blob(self):
        def read(req, open_request, read_response, path):
            if path == 'commits/main':
                return {'sha': 'c' * 40}
            if path.startswith('contents/'):
                return {'sha': 'b' * 40, 'content': ''}
            self.assertEqual(path, 'git/blobs/' + 'b' * 40)
            return {'content': base64.b64encode(b'{"big": 1}').decode()}
        with patch.dict(os.environ, GH_TOKEN='t'), patch.object(s, 'github_read_retry', side_effect=read):
            self.assertEqual(s.site_files(['src/lib/other-bounds.json'])[1], {'src/lib/other-bounds.json': b'{"big": 1}'})


class ClosedTests(unittest.TestCase):
    # Average sensitivity opened on 2026-10-23; CLOSED keeps working for the next problem.
    def setUp(self):
        closed = patch.object(s, 'CLOSED', {'average-sensitivity'})
        closed.start(); self.addCleanup(closed.stop)

    def test_a_closed_problem_is_not_selected(self):
        import queue_lease
        import derivation
        lease = Mock(state={'page': 1, 'offset': 0}, admitted=Mock(return_value=False))
        with tempfile.TemporaryDirectory() as tmp:
            old = Path.cwd(); os.chdir(tmp)
            try:
                with patch.dict(os.environ, GITHUB_OUTPUT=str(Path(tmp) / 'output')), patch.object(queue_lease, 'acquire', return_value=lease), \
                     patch.object(s, 'api', side_effect=lambda p, data=None: [issue()] if p.startswith('issues?') else []), \
                     patch.object(s, 'acknowledge'), patch.object(s, 'release'), \
                     patch.object(s, 'current_record', side_effect=AssertionError('no gate read for a closed problem')), \
                     patch.object(derivation.Reader, 'get', side_effect=derivation.NotComputed('offline')):
                    s.select()
                self.assertEqual(list(Path('requests').glob('*.json')), [])
                lease.reserve.assert_not_called()
            finally:
                os.chdir(old)

    def test_the_acknowledgement_says_the_problem_is_not_open(self):
        posts = []
        def api(path, data=None, method=None):
            if data is not None:
                posts.append(data); return {'id': 1}
            if path.startswith('issues?'):
                return [issue()]
            return []
        with patch.object(s, 'api', side_effect=api):
            s.acknowledge()
        self.assertEqual(len(posts), 1)
        self.assertIn('not open yet', posts[0]['body'])


class OpenTests(unittest.TestCase):
    def test_an_open_problem_is_selected_against_the_row_gate(self):
        import queue_lease
        import derivation
        lease = Mock(state={'page': 1, 'offset': 0}, admitted=Mock(return_value=False))
        gate = {'schema_version': 1, 'score': '8', 'score_relation': 'attained', 'leader_ids': ['baseline'],
                'any_lean_verified_at_bound': False, 'problem_id': 'other/average-sensitivity'}
        with tempfile.TemporaryDirectory() as tmp:
            old = Path.cwd(); os.chdir(tmp)
            try:
                with patch.dict(os.environ, GITHUB_OUTPUT=str(Path(tmp) / 'output')), patch.object(queue_lease, 'acquire', return_value=lease), \
                     patch.object(s, 'api', side_effect=lambda p, data=None: [issue()] if p.startswith('issues?') else []), \
                     patch.object(s, 'acknowledge'), patch.object(s, 'release'), patch.object(s, 'current_record', return_value=gate), \
                     patch.object(derivation.Reader, 'get', side_effect=derivation.NotComputed('offline')):
                    s.select()
                request = json.loads(Path('requests/60.json').read_text())
                self.assertEqual((request['submission']['problem'], request['record_gate']['score']), ('average-sensitivity', '8'))
                self.assertEqual(request['inputs']['challenge_file'], 'challenges/average-sensitivity/VerifierStatement.lean')
            finally:
                os.chdir(old)


class SmokeTests(unittest.TestCase):
    def selected(self, **change):
        item = issue()
        selected = s.issue_request(item, smoke.issue_submission(s.issue_input(item)))
        selected.update(test_only=True, live_smoke=smoke.AS_TAG)
        selected.update(change)
        return selected

    def test_the_average_sensitivity_smoke_is_the_fixed_pin_only(self):
        self.assertTrue(smoke.active(self.selected()))
        self.assertFalse(smoke.active(self.selected(test_only=False)))
        self.assertFalse(smoke.active(self.selected(route='pull_request')))
        self.assertFalse(smoke.active(self.selected(live_smoke=smoke.TAG)))
        other = self.selected()
        other['submission'] = dict(other['submission'], bound='3')
        self.assertFalse(smoke.active(other))
        with self.assertRaises(ValueError):
            smoke.issue_submission(s.issue_input(issue(commit='a' * 40)))

    def test_dispatch_tags_the_fixture(self):
        import queue_lease
        lease = Mock(state={})
        event = {'inputs': {'smoke_route': 'issue', 'smoke_number': '60'}}
        with tempfile.TemporaryDirectory() as tmp:
            old = Path.cwd(); os.chdir(tmp)
            try:
                Path('event.json').write_text(json.dumps(event))
                with patch.dict(os.environ, GITHUB_OUTPUT=str(Path(tmp) / 'output'), BOS_SMOKE_DISPATCH='1', GITHUB_EVENT_NAME='workflow_dispatch',
                                GITHUB_EVENT_PATH=str(Path(tmp) / 'event.json')), patch.object(s, 'api', return_value=issue()):
                    self.assertTrue(smoke.dispatch(lease))
                selected = json.loads(Path('requests/60.json').read_text())
                self.assertEqual((selected['live_smoke'], selected['test_only'], selected['submission']['problem']),
                                 (smoke.AS_TAG, True, 'average-sensitivity'))
            finally:
                os.chdir(old)


if __name__ == '__main__':
    unittest.main()
