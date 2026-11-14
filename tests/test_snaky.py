import hashlib
import json
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import submissions as s

CHALLENGE = ROOT / 'challenges/other-snaky'


def body(bound='20'):
    return ('### Problem\n\nsnaky\n\n### Repository URL\n\nhttps://github.com/someone/snaky-lean\n\n'
            f'### Commit SHA\n\n{"a" * 40}\n\n### Bound\n\n{bound}\n')


class SnakyStatementTests(unittest.TestCase):
    def test_the_verifier_statement_is_the_reviewed_files_joined(self):
        # One self-contained challenge: staging Statement.lean's import would take Model.lean from the submitter.
        model = (CHALLENGE / 'Model.lean').read_text()
        first, rest = (CHALLENGE / 'Statement.lean').read_text().split('\n', 1)
        self.assertEqual(first, 'import challenges.«other-snaky».Model')
        joined = (CHALLENGE / 'VerifierStatement.lean').read_text()
        self.assertEqual(joined, model + rest)
        imports = [line for line in joined.splitlines() if line.startswith('import')]
        self.assertEqual(imports, ['import Mathlib.Data.Finset.Card', 'import Mathlib.Data.Int.Basic',
                                   'import Mathlib.Data.Fintype.Prod', 'import Mathlib.Algebra.Group.Prod'])
        self.assertNotIn('sorry', joined)

    def test_the_openai_block_is_unchanged(self):
        # openai/math@1581d4c lean/ComparatorChallenges/SnakyTwentyOne.lean, lines 3-40 (the definitions).
        provenance = json.loads((CHALLENGE / 'provenance.json').read_text())
        self.assertEqual(provenance['source_commit'], '1581d4cbdd69a0faf34b2089614fe2a814316a6a')
        self.assertEqual(provenance['extracted_lines'], '3-40')
        lines = (CHALLENGE / 'Model.lean').read_text().splitlines(keepends=True)
        start, end = map(int, provenance['local_lines'].split('-'))
        block = ''.join(lines[start - 1:end])
        self.assertEqual(hashlib.sha256(block.encode()).hexdigest(), provenance['extracted_sha256'])
        self.assertEqual(provenance['extracted_sha256'], '0d999f2d9ea7a88ee3a28067de5ac85566e4541c0763b006b30c4b6a30abf638')
        self.assertTrue(block.startswith('namespace OAI\n') and block.endswith('end SnakyPrototype.OrdinaryStrategy\n'))
        self.assertEqual(''.join(lines[end:]), '\nend OAI\n')

    def test_the_target_keeps_openai_conclusion_with_n(self):
        statement = (CHALLENGE / 'Statement.lean').read_text()
        for part in ['∀ r M B, σ r M B ∉ M ∧ σ r M B ∉ B', 'LegalRepliesBeforeFinal σ n β ∅ ∅',
                     'HasSnaky (playState σ n β ∅ ∅ n).1', '(playState σ n β ∅ ∅ n).1.card = n',
                     'Disjoint (playState σ n β ∅ ∅ n).1 (playState σ n β ∅ ∅ (n - 1)).2',
                     '(playState σ n β ∅ ∅ k).2.card = k']:
            self.assertIn(part, statement)
        self.assertIn('def Bound (n : ℕ) : Prop :=', statement)


class ProfileTests(unittest.TestCase):
    def test_the_profile_pins_the_reviewed_statement(self):
        # Lead, 2026-11-02 (verifier #106): Lean v4.34.1 + Mathlib d13f23b, a single job, whole numbers up to 100.
        profile = json.loads((ROOT / 'profiles/direct.json').read_text())['snaky']
        self.assertEqual(profile['challenge_file'], 'challenges/other-snaky/VerifierStatement.lean')
        self.assertEqual(profile['challenge_sha256'], hashlib.sha256((ROOT / profile['challenge_file']).read_bytes()).hexdigest())
        self.assertEqual(profile['challenge_sha256'], '49e630b3bab9a3d1006b373edd85cf196eba0f45bdb878e0126db16776ed780b')
        self.assertEqual((profile['lean_toolchain'], profile['manifest_file'], profile['tools_file']),
                         ('leanprover/lean4:v4.34.1', 'profiles/lake-manifest.json', 'profiles/tools.json'))
        self.assertEqual((profile['theorem_names'], profile['maximum'], profile['upstream_commit']),
                         (['Race.bound'], '100', '1581d4cbdd69a0faf34b2089614fe2a814316a6a'))
        self.assertNotIn('runner', profile)
        self.assertEqual(s.matrix_entry(5, 'x', 'issue', s.parse_body(body())), {'issue_number': 5, 'login': 'x', 'route': 'issue'})

    def test_target_and_whole_number_bounds(self):
        sub = s.parse_body(body())
        source = s.challenge_source(sub)
        self.assertTrue(source.startswith((CHALLENGE / 'VerifierStatement.lean').read_text()))
        self.assertTrue(source.endswith('theorem Race.bound : BigOSpeedrun.Snaky.Bound 20 := by\n  sorry\n'))
        # Reviewer's checklist: 20, 19 and 0 pass the form (0 is in the range; Validation.lean shows that Bound 0 is
        # false), 19/2 and 101 do not.
        for good in ['20', '19', '0', '100']:
            self.assertEqual(s.validate_submission(dict(sub, bound=good))['bound'], good)
        self.assertEqual(s.validate_submission(dict(sub, bound='38/2'))['bound'], '19')
        for bad in ['19/2', '39/2', '19.5', '101', '-1']:
            with self.subTest(bound=bad), self.assertRaises(ValueError):
                s.validate_submission(dict(sub, bound=bad))
        with self.assertRaisesRegex(ValueError, 'whole number of Maker moves'):
            s.validate_submission(dict(sub, bound='39/2'))
        # The target generator refuses a fraction even if a caller skips the form check.
        with patch.object(s, 'validate_submission', side_effect=lambda v: v), self.assertRaises(ValueError):
            s.challenge_source(dict(sub, bound='39/2'))


class GateTests(unittest.TestCase):
    def gate(self, claims=(), direct=None):
        rows = {'families': [{'slug': 'snaky', 'direction': 'lower', 'baseline': {'exactValue': '21'}, 'claims': list(claims)}]}
        files = {'src/lib/other-bounds.json': json.dumps(rows).encode(),
                 'data/direct-other.json': None if direct is None else json.dumps({'boards': {'other-snaky': {'claims': direct}}}).encode(),
                 'data/prove2me.json': None}
        with patch.object(s, 'site_files', return_value=('c' * 40, files)):
            return s.current_record('snaky', 'https://github.com/bigospeedrun/verifier/issues/110')

    def test_the_profile_range_gates_until_a_lean_verified_claim_exists(self):
        # The Claimed 19 and 20 rows never gate; a first Lean proof of 20 runs (Nil ruling 2026-11-02: stepping stone).
        claimed = [{'handle': 'gotrevor', 'value': '20', 'evidence': 'claimed', 'url': 'x'},
                   {'handle': 'shjvandekamp', 'value': '19', 'evidence': 'claimed', 'url': 'y'}]
        record = self.gate(claimed)
        self.assertEqual((record['score'], record['leader_ids'], record['any_lean_verified_at_bound'], record['problem_id']),
                         ('100', ['profile-range'], False, 'other/snaky'))
        self.assertTrue(s.qualifies_for_run({'problem': 'snaky', 'bound': '20'}, record))
        self.assertTrue(s.qualifies_for_run({'problem': 'snaky', 'bound': '100'}, record))
        # A Lean Verified 20 gates: 20 again does not run, 19 does.
        record = self.gate(claimed, direct=[{'handle': 'direct-issue-107', 'value': '20', 'evidence': 'lean-verified', 'url': 'z'}])
        self.assertEqual((record['score'], record['any_lean_verified_at_bound']), ('20', True))
        self.assertFalse(s.qualifies_for_run({'problem': 'snaky', 'bound': '20'}, record))
        self.assertTrue(s.qualifies_for_run({'problem': 'snaky', 'bound': '19'}, record))


class OpenTests(unittest.TestCase):
    # Snaky opened on 2026-11-03 after its smoke (run 41548037272, issue #113) and the refused mutation runs.
    def test_snaky_is_open(self):
        self.assertNotIn('snaky', s.CLOSED)
        self.assertEqual(s.board_line('snaky'), 'Snaky board: https://bigospeedrun.com/other/snaky')
        with self.assertRaises(ValueError) as error:
            s.validate_submission({'schema_version': 1, 'problem': 'nope', 'bound': '1', 'repo_url': 'https://github.com/a/b',
                                   'commit': 'a' * 40, 'authors': []})
        self.assertIn('snaky', str(error.exception))
        form = (ROOT / '.github/ISSUE_TEMPLATE/lean-submission.yml').read_text()
        self.assertIn('options: [dft, 3sum, apsp, average-sensitivity, catalan, subset-sum, snaky, heilbronn-triangle, directed-sssp, prime-gaps, 3sat]', form)
        sub = {'schema_version': 1, 'problem': 'snaky', 'bound': '20', 'repo_url': 'https://github.com/a/b', 'commit': 'a' * 40, 'authors': []}
        self.assertEqual(s.validate_submission(sub)['bound'], '20')
        for bound in ['19/2', '101']:
            with self.subTest(bound=bound), self.assertRaises(ValueError):
                s.validate_submission(dict(sub, bound=bound))


if __name__ == '__main__':
    unittest.main()
