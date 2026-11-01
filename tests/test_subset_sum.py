import hashlib
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import Mock, patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import submissions as s
from fractions import Fraction

CHALLENGE = ROOT / 'challenges/subset-sum'


def body(bound='4877/10000'):
    return ('### Problem\n\nsubset-sum\n\n### Repository URL\n\nhttps://github.com/someone/subset-sum-lean\n\n'
            f'### Commit SHA\n\n{"a" * 40}\n\n### Bound\n\n{bound}\n')


class StatementTests(unittest.TestCase):
    def test_the_profile_pins_the_reviewed_statement(self):
        # Reviewed on 2026-10-26 (BOS Reviewer, verifier #67): Statement.lean sha256 80bc6d28. Pinned to
        # Lean v4.34.1 + Mathlib d13f23b at the merge (Lead, 2026-10-27): the paper's OAI library is native there.
        profile = json.loads((ROOT / 'profiles/direct.json').read_text())['subset-sum']
        self.assertEqual(profile['challenge_file'], 'challenges/subset-sum/Statement.lean')
        self.assertEqual(profile['challenge_sha256'], hashlib.sha256((ROOT / profile['challenge_file']).read_bytes()).hexdigest())
        self.assertEqual(profile['challenge_sha256'], '80bc6d282676fc056a220968a727ab983b8c5a280cb0d9f24561bb3c90867517')
        self.assertEqual((profile['lean_toolchain'], profile['manifest_file'], profile['tools_file']),
                         ('leanprover/lean4:v4.34.1', 'profiles/lake-manifest.json', 'profiles/tools.json'))
        text = (CHALLENGE / 'Statement.lean').read_text()
        self.assertFalse([line for line in text.splitlines() if line.startswith('import')])
        self.assertNotIn('sorry', text)

    def test_target_and_bound_range(self):
        sub = dict(s.parse_body(body()), problem='subset-sum')
        source = s.challenge_source(sub)
        self.assertTrue(source.startswith((CHALLENGE / 'Statement.lean').read_text()))
        self.assertTrue(source.endswith('theorem Race.bound : BigOSpeedrun.SubsetSum.SolvedInTime ((4877 : Rat) / 10000) := by\n  sorry\n'))
        self.assertEqual(s.validate_submission(dict(sub, bound='1'))['bound'], '1')
        for bad in ['3/2', '0.49']:
            with self.assertRaises(ValueError):
                s.validate_submission(dict(sub, bound=bad))


class GateTests(unittest.TestCase):
    def gate(self, rows, metadata):
        data = {'problem_id': 'subset-sum/randomized-word-ram', 'records': rows, 'record_metadata': metadata}
        with patch.object(s, 'site_snapshot', return_value=('c' * 40, json.dumps(data).encode())):
            return s.current_record('subset-sum', 'https://github.com/bigospeedrun/verifier/issues/90')

    def test_the_baseline_gates_until_a_lean_verified_row_exists(self):
        rows = [{'id': 'classical-baseline', 'score': '1/2'}, {'id': 'a-kapila', 'score': '4877/10000', 'score_relation': 'attained'}]
        record = self.gate(rows, {'a-kapila': {'site_tier': 'claimed'}})
        self.assertEqual((record['score'], record['leader_ids'], record['any_lean_verified_at_bound']), ('1/2', ['classical-baseline'], False))
        self.assertTrue(s.qualifies_for_run({'problem': 'subset-sum', 'bound': '4877/10000'}, record))
        self.assertFalse(s.qualifies_for_run({'problem': 'subset-sum', 'bound': '3/5'}, record))


BOARD = {'problem_id': 'subset-sum/randomized-word-ram', 'record_metadata': {},
         'records': [{'id': 'classical-baseline', 'score': '1/2'}, {'id': 'a-kapila', 'score': '4877/10000'}]}


class ClassicGateTests(unittest.TestCase):
    """A bound worse than the classic bound of its board gets no run and no row (Lead, 2026-11-01, issue #94)."""
    def classic(self, bound, problem='subset-sum', board=BOARD):
        with patch.object(s, 'site_snapshot', return_value=('c' * 40, json.dumps(board).encode())):
            return s.worse_than_classic({'problem': problem, 'bound': bound})

    def test_only_a_bound_worse_than_the_classical_baseline_row(self):
        self.assertEqual(self.classic('3/4'), Fraction(1, 2))
        self.assertEqual(self.classic('1'), Fraction(1, 2))
        # A tie with the classic bound is not worse: it can still run while no Lean Verified row exists.
        for bound in ['1/2', '4877/10000', '0']:
            with self.subTest(bound=bound):
                self.assertIsNone(self.classic(bound))
        # DFT: a higher saving is better, and the classic bound is 0.
        dft = dict(BOARD, records=[{'id': 'classical-baseline', 'score': '0'}])
        self.assertIsNone(self.classic('0', 'dft', dft))
        self.assertIsNone(self.classic('1/2', 'dft', dft))
        with self.assertRaises(ValueError):
            self.classic('3/4', board=dict(BOARD, records=BOARD['records'][1:]))

    def test_other_bounds_rows_read_the_exact_baseline(self):
        def rows(baseline):
            other = {'families': [{'slug': 'average-sensitivity', 'baseline': {'exactValue': baseline}},
                                  {'slug': 'catalan', 'baseline': {'exactValue': '+\\infty'}}]}
            return patch.object(s, 'site_files', return_value=('c' * 40, {'src/lib/other-bounds.json': json.dumps(other).encode()}))
        with rows('8'):
            self.assertIsNone(s.worse_than_classic({'problem': 'average-sensitivity', 'bound': '8'}))
            self.assertIsNone(s.worse_than_classic({'problem': 'catalan', 'bound': '100000000'}))
        with rows('7'):
            self.assertEqual(s.worse_than_classic({'problem': 'average-sensitivity', 'bound': '15/2'}), 7)

    def select(self, bound):
        """One scan over an open issue, with Subset Sum open (as after its opening commit)."""
        import queue_lease
        import derivation
        from test_submissions import issue
        item = issue(60, problem='subset-sum', bound=bound)
        lease = Mock(state={'page': 1, 'offset': 0}, admitted=Mock(return_value=False))
        calls = []
        def api(path, data=None, method=None):
            calls.append((path, data, method))
            return [item] if path.startswith('issues?') else []
        gate = {'schema_version': 1, 'score': '1/2', 'score_relation': 'attained', 'leader_ids': ['classical-baseline'],
                'any_lean_verified_at_bound': False, 'problem_id': 'subset-sum/randomized-word-ram'}
        with tempfile.TemporaryDirectory() as tmp:
            old = Path.cwd(); os.chdir(tmp)
            try:
                with patch.dict(os.environ, GITHUB_OUTPUT=str(Path(tmp) / 'output')), patch.object(queue_lease, 'acquire', return_value=lease), \
                     patch.object(s, 'CLOSED', set()), patch.object(s, 'api', side_effect=api), \
                     patch.object(s, 'site_snapshot', return_value=('c' * 40, json.dumps(BOARD).encode())), \
                     patch.object(s, 'acknowledge'), patch.object(s, 'release'), \
                     patch.object(s, 'current_record', return_value=gate) as record, \
                     patch.object(derivation.Reader, 'get', side_effect=derivation.NotComputed('offline')):
                    s.select()
                request = Path('requests/60.json')
                return (json.loads(request.read_text()) if request.exists() else None), calls, record
            finally:
                os.chdir(old)

    def test_the_scan_closes_a_bound_worse_than_classic_without_a_run_or_a_claimed_marker(self):
        request, calls, record = self.select('3/4')
        self.assertIsNone(request)
        record.assert_not_called()
        posts = [data['body'] for path, data, method in calls if path == 'issues/60/comments' and data]
        self.assertEqual(len(posts), 1)
        self.assertTrue(posts[0].startswith('<!-- bos-classic-v1 60 '))
        self.assertNotIn('bos-claimed-v1', posts[0])
        self.assertIn('The bound 3/4 is above the classic bound 1/2 of this board, so it is not a race result. '
                      'No proof run starts, and it is not listed. This issue now closes.', posts[0])
        self.assertIn('Subset Sum board: https://bigospeedrun.com/subset-sum', posts[0])
        self.assertIn(('issues/60', {'state': 'closed', 'state_reason': 'not_planned'}, 'PATCH'), calls)

    def test_the_scan_selects_a_bound_that_ties_the_classic_bound(self):
        request, calls, record = self.select('1/2')
        self.assertEqual(request['submission']['bound'], '1/2')
        record.assert_called_once()
        self.assertFalse([c for c in calls if c[0] == 'issues/60/comments' and c[1] and 'bos-classic-v1' in c[1]['body']])


class ClosedTests(unittest.TestCase):
    def test_subset_sum_is_closed_until_its_smoke(self):
        self.assertIn('subset-sum', s.CLOSED)
        self.assertEqual(s.board_line('subset-sum'), 'Subset Sum board: https://bigospeedrun.com/subset-sum')


if __name__ == '__main__':
    unittest.main()
