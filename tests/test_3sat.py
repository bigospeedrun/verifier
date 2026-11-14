"""The 3-SAT board (task 07840cc3, verifier #192): the trusted statement, the closed chain profile and the target."""
import hashlib
import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import chain
import submissions as s
import verifier as v

CHALLENGE = ROOT / 'challenges/3sat'
PROFILE = json.loads((ROOT / 'profiles/direct.json').read_text())['3sat']
OAI_COMMIT = '7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a'


def submission(bound='1/2'):
    return {'schema_version': 1, 'problem': '3sat', 'bound': bound, 'repo_url': 'https://github.com/someone/sat',
            'commit': 'a' * 40, 'authors': []}


class StatementTests(unittest.TestCase):
    def test_the_definitions_are_openai_lines_1_to_128(self):
        provenance = json.loads((CHALLENGE / 'provenance.json').read_text())
        self.assertEqual((provenance['source_repository'], provenance['commit'], provenance['modified']),
                         ('https://github.com/openai/math', OAI_COMMIT, False))
        [entry] = provenance['files']
        definitions = (CHALLENGE / 'SubexponentialSATDefinitions.lean').read_bytes()
        self.assertEqual((entry['lines'], entry['bytes'], entry['sha256']),
                         ('1-128', len(definitions), hashlib.sha256(definitions).hexdigest()))

    def test_the_verifier_statement_is_the_definitions_then_the_statement(self):
        definitions = (CHALLENGE / 'SubexponentialSATDefinitions.lean').read_text()
        statement = (CHALLENGE / 'Statement.lean').read_text()
        self.assertTrue(statement.startswith('import SubexponentialSATDefinitions\n'))
        self.assertEqual((CHALLENGE / 'VerifierStatement.lean').read_text(),
                         definitions + statement.removeprefix('import SubexponentialSATDefinitions\n'))
        for text in [definitions, statement]:
            self.assertNotIn('sorry', text)
            self.assertNotIn('axiom ', text)
        # No hypothesis: in particular not the Exponential Time Hypothesis.
        self.assertIn('def SolvedInTime (α : ℚ) : Prop :=\n  ∃ (machine : Computation.PrimitiveMachine) (d : ℕ),\n', statement)

    def test_the_reviewed_statement_bytes(self):
        self.assertEqual(PROFILE['challenge_sha256'], hashlib.sha256((ROOT / PROFILE['challenge_file']).read_bytes()).hexdigest())
        self.assertEqual(PROFILE['challenge_sha256'], '33c481812f1ce3245a2d3207e1f0d9cd3e5d16c456976b346036dfbd0479c886')


class ProfileTests(unittest.TestCase):
    def test_the_profile_runs_on_the_check_chain(self):
        self.assertEqual((PROFILE['lean_toolchain'], PROFILE['manifest_file'], PROFILE['tools_file'], PROFILE['runner']),
                         (v.CHAIN_TOOLCHAIN, 'profiles/lake-manifest.json', 'profiles/tools-chain.json', 'github-chain'))
        self.assertEqual((PROFILE['source_roots'], PROFILE['theorem_names'], PROFILE['maximum'], PROFILE['upstream_commit']),
                         (['OAI', 'Submission'], ['Race.bound'], '100', OAI_COMMIT))
        self.assertEqual(chain.caps(PROFILE), {'max_build_jobs': 4, 'max_check_jobs': 4, 'max_hours': 30, 'segment_parts': 5})
        self.assertEqual(PROFILE['lake_workers_start'], 2)
        self.assertIn(PROFILE['lake_workers_start'], v.LAKE_WORKERS)
        v.check_chain_profile(PROFILE, {'lean_toolchain': PROFILE['lean_toolchain']})
        self.assertEqual(v.build_roots(PROFILE), ['OAI', 'Submission'])

    def test_closed_until_the_smoke_passes(self):
        self.assertIn('3sat', s.CLOSED)
        self.assertEqual(s.MODEL_IDS['3sat'], '3sat/randomized-bit-model')
        self.assertIn('3sat', s.HIGHER)
        self.assertNotIn('3sat', s.OTHER)
        self.assertEqual(s.board_line('3sat'), '3-SAT board: https://bigospeedrun.com/3sat')
        form = (ROOT / '.github/ISSUE_TEMPLATE/lean-submission.yml').read_text()
        self.assertIn('directed-sssp, prime-gaps, 3sat]', form)

    def test_a_larger_alpha_is_better(self):
        self.assertEqual((s.open_rank('3sat'), s.range_end('3sat')), (-1, 0))


class TargetTests(unittest.TestCase):
    def test_target(self):
        source = s.challenge_source(submission())
        self.assertTrue(source.startswith((CHALLENGE / 'VerifierStatement.lean').read_text()))
        self.assertTrue(source.endswith('theorem Race.bound : BigOSpeedrun.ThreeSat.SolvedInTime ((1 : ℚ) / 2) := by\n  sorry\n'))
        for good, reduced in [('1/2', '1/2'), ('2/4', '1/2'), ('0', '0'), ('100', '100'), ('3/5', '3/5')]:
            self.assertEqual(s.validate_submission(submission(good))['bound'], reduced)
        for bad in ['101', '-1/2', '0.5', '1/0']:
            with self.assertRaises(ValueError):
                s.validate_submission(submission(bad))


if __name__ == '__main__':
    unittest.main()
