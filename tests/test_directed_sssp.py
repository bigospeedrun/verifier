import hashlib
import json
from fractions import Fraction as F
from pathlib import Path
import sys
import os
import tempfile
import unittest
from unittest.mock import Mock, patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import submissions as s

CHALLENGE = ROOT / 'challenges/directed-sssp'
FORK = 'https://github.com/bigospeedrun/c-hd-proof'
PIN = '98c53accb47a505482a1781597ae14bf67e81cec'


def body(bound='n log^3/4 ; n log^11/12'):
    return ('### Problem\n\ndirected-sssp\n\n### Repository URL\n\nhttps://github.com/someone/sssp-lean\n\n'
            f'### Commit SHA\n\n{"a" * 40}\n\n### Bound\n\n{bound}\n')


class StatementTests(unittest.TestCase):
    def test_the_statement_imports_the_model_and_no_proof(self):
        # Nil's GO, 2026-11-03: the model comes from our fork at a pinned commit; this file has the race statement only.
        statement = (CHALLENGE / 'VerifierStatement.lean').read_text()
        self.assertEqual([line for line in statement.splitlines() if line.startswith('import')],
                         ['import Frontier.CostModel', 'import Mathlib.Analysis.SpecialFunctions.Pow.Real'])
        for word in ['sorry', 'axiom', 'admit', 'theorem', 'lemma']:
            self.assertNotIn(word, statement)
        for part in ['(n : ℝ) ^ (a : ℝ) * (⌊((Nat.log 2 n : ℕ) : ℝ) ^ (b : ℝ)⌋₊ : ℝ)',
                     '(n : ℝ) ^ (a : ℝ) * Real.log n ^ (b : ℝ) * Real.log (Real.log n) ^ (c : ℝ)',
                     '∃ fuel r, P.run fuel G s = some r ∧ r.Solves G s ∧ (r.cost : ℝ) ≤ budget',
                     '∃ P : Program, P.Exact ∧ ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 16 ≤ N ∧',
                     '(∀ (G : Graph) (s : Fin G.n), N ≤ G.n → Sparse a b G.n G.m →\n      CorrectWithin P G s (C * Time a\' b\' c\' G.n)) ∧',
                     '(∀ (G : Graph) (s : Fin G.n),\n      CorrectWithin P G s (C * ((G.n : ℝ) + 1) * ((G.m : ℝ) + 1)))']:
            self.assertIn(part, statement)

    def test_validation_imports_the_verifier_statement(self):
        validation = (CHALLENGE / 'Validation.lean').read_text()
        self.assertTrue(validation.startswith('import VerifierStatement\n'))
        self.assertNotIn('sorry', validation)
        for name in ['weaker_time', 'cover_sparser', 'cap_ge_self', 'time_pos']:
            self.assertIn(f'theorem {name}' if name != 'time_pos' else f'lemma {name}', validation)

    def test_the_profile_pins_the_statement_and_the_fork(self):
        profile = json.loads((ROOT / 'profiles/direct.json').read_text())['directed-sssp']
        self.assertEqual(profile['challenge_file'], 'challenges/directed-sssp/VerifierStatement.lean')
        self.assertEqual(profile['challenge_sha256'], hashlib.sha256((ROOT / profile['challenge_file']).read_bytes()).hexdigest())
        self.assertEqual((profile['lean_toolchain'], profile['manifest_file'], profile['tools_file']),
                         ('leanprover/lean4:v4.34.1', 'profiles/lake-manifest.json', 'profiles/tools.json'))
        self.assertEqual((profile['theorem_names'], profile['source_roots'], profile['upstream_commit']),
                         (['Race.bound'], ['Submission'], PIN))
        # The fork is cloned at its pin and staged as the Frontier root; no file of it is in this repository, and no
        # patch changes it (Lead, 2026-11-03). Its own build keeps Lean's default autoImplicit = true (formal/lean has
        # no leanOptions), and Frontier/CHD/MergeSort.lean uses an auto-bound name (smoke run 41631927522 failed with
        # autoImplicit = false), so only the Frontier root gets that option; Submission and the challenge keep false.
        self.assertEqual(profile['solution_dependencies'],
                         [{'repo_url': FORK, 'commit': PIN, 'source_subdir': 'formal/lean', 'source_roots': ['Frontier'],
                           'lean_options': {'autoImplicit': True}}])
        sys.path.insert(0, str(ROOT / 'scripts'))
        import verifier
        lake = verifier.lakefile(['Submission', 'Frontier', 'VerifierChallenge', 'VerifierAudit'], root_options=
                                 verifier.dependency_root_options(profile['solution_dependencies'], profile['source_roots']))
        self.assertIn('[leanOptions]\nautoImplicit = false\n', lake)
        self.assertIn('\n[[lean_lib]]\nname = "Frontier"\n[lean_lib.leanOptions]\nautoImplicit = true\n', lake)
        self.assertEqual(lake.count('autoImplicit = true'), 1)
        self.assertFalse((CHALLENGE / 'Frontier').exists())
        self.assertNotIn('runner', profile)

    def test_the_problem_is_open(self):
        self.assertNotIn('directed-sssp', s.CLOSED)
        form = (ROOT / '.github/ISSUE_TEMPLATE/lean-submission.yml').read_text()
        self.assertIn('snaky, heilbronn-triangle, directed-sssp, prime-gaps, 3sat]', form)
        self.assertIn('(directed-sssp: D ; T, such as n log^3/4 ; n log^11/12)', form)
        self.assertEqual((s.MODEL_IDS['directed-sssp'], s.board_line('directed-sssp')),
                         ('directed-sssp/comparison-addition-sparse',
                          'Directed shortest paths board: https://bigospeedrun.com/directed-sssp'))


class CHDRowTests(unittest.TestCase):
    """The maintainer profile for the Vals AI row (Lead, 2026-11-03: a maintainer binding, as for matrix-nine-fourths).
    verify.yml checks one fixed target, the C-HD row; the public issue route never reads this profile."""
    def test_the_fixed_target_is_the_generated_c_hd_row(self):
        profile = json.loads((ROOT / 'profiles/sssp-chd.json').read_text())
        direct = json.loads((ROOT / 'profiles/direct.json').read_text())['directed-sssp']
        target = (ROOT / profile['challenge_file']).read_text()
        sub = dict(s.parse_body(body()), bound='n log^3/4 ; n log^11/12')
        self.assertEqual(target, s.challenge_source(sub))
        self.assertEqual(profile['challenge_sha256'], hashlib.sha256(target.encode()).hexdigest())
        self.assertEqual(profile['challenge_sha256'], 'b9569daeed41b0394a8a0ec10bd40fa15d005fef8afb1abfa2f77a52f7d27ab0')
        for key in ['lean_toolchain', 'manifest_file', 'tools_file', 'solution_module', 'theorem_names', 'source_roots',
                    'upstream_commit', 'solution_dependencies']:
            self.assertEqual(profile[key], direct[key], key)
        self.assertEqual((profile['bound'], profile['score_relation'], profile['model']),
                         ('n log^3/4 ; n log^11/12', 'attained', s.MODEL_IDS['directed-sssp']))
        self.assertEqual(set(profile['permitted_axioms']), {'propext', 'Quot.sound', 'Classical.choice'})

    def test_verify_resolves_only_this_profile_for_the_row(self):
        sys.path.insert(0, str(ROOT / 'scripts'))
        import verifier
        request = {'repo_url': 'https://github.com/bigospeedrun/sssp-lean-scratch',
                   'commit': '98919233966fa6196cf67639c1eee2b2496d26b6',
                   'challenge_file': 'challenges/directed-sssp/CHDRow.lean', 'theorem_names': 'Race.bound',
                   'lean_toolchain': 'leanprover/lean4:v4.34.1'}
        profile, names = verifier.validate_request(request)
        self.assertEqual((profile['challenge_file'], names), ('challenges/directed-sssp/CHDRow.lean', ['Race.bound']))
        for field, value in [('theorem_names', 'BigOSpeedrun.DirectedSSSP.Bound'), ('lean_toolchain', 'leanprover/lean4:v4.34.0'),
                             ('challenge_file', 'challenges/directed-sssp/VerifierStatement.lean')]:
            with self.subTest(field=field), self.assertRaises(ValueError):
                verifier.validate_request(dict(request, **{field: value}))


class GrammarTests(unittest.TestCase):
    def test_normal_forms_parse_to_exponent_tuples(self):
        cases = {
            'n log^3/4 ; n log^11/12': (1, F(3, 4), 1, F(11, 12), 0),
            'n ; n log^1/2 loglog^1/2': (1, 0, 1, F(1, 2), F(1, 2)),
            'n ; n log': (1, 0, 1, 1, 0),
            'n^2 ; n^2': (2, 0, 2, 0, 0),
            'n ; n^2 loglog^-1': (1, 0, 2, 0, -1),
            'n^2 ; n^3 loglog^-1': (2, 0, 3, 0, -1),
            'n log^3/4 ; n log^11/12 loglog^-1/3': (1, F(3, 4), 1, F(11, 12), F(-1, 3)),
            'n^3/2 log^2 ; n^3/2 log^2 loglog': (F(3, 2), 2, F(3, 2), 2, 1),
            'n log ; n log^2 loglog^-7': (1, 1, 1, 2, -7),
        }
        for text, tup in cases.items():
            with self.subTest(text=text):
                self.assertEqual(s.parse_sssp(text), tuple(F(x) for x in tup))
                self.assertEqual(s.validate_submission(dict(s.parse_body(body()), bound=text))['bound'], text)

    def test_other_texts_are_refused_with_the_example(self):
        for text in ['n log^3/4; n log^11/12', 'n log^3/4 ;n log^11/12', 'n log^6/8 ; n log', 'n^1 ; n', 'log n ; n',
                     'n log^0 ; n', 'n loglog ; n', 'n ; n log  loglog', ' n ; n', 'n ; n ', 'n ; n ; n', 'n ; n^01',
                     'n ; n^+2', 'n ; n^2.5', 'n ; loglog log n', 'n ; n n', 'n ; n log^1/1', 'n ; n log^-0',
                     'n ; n log^2/-3', 'n^2 ;', '; n', 'n', '', 'n ; n log^' + '1' * 41, 'n ; N', 'n ; n lg',
                     'n ; n\tlog', 'n ; n log^3/4\n']:
            with self.subTest(text=text), self.assertRaisesRegex(ValueError, 'for example "n log\\^3/4 ; n log\\^11/12"'):
                s.parse_sssp(text)

    def test_ranges(self):
        for text in ['n log^-1 ; n', 'n^1/2 ; n', 'n^2 log ; n^3', 'n^3 ; n^3']:
            with self.subTest(text=text), self.assertRaisesRegex(ValueError, 'between n and n\\^2'):
                s.parse_sssp(text)
        for text in ['n log ; n', 'n ; n^4', 'n ; n^3 loglog', 'n log ; n log^-1 loglog^9', 'n^2 ; n^2 loglog^-5',
                     'n ; n loglog^-1']:
            with self.subTest(text=text), self.assertRaisesRegex(ValueError, 'at least the edge bound D and at most n\\^3'):
                s.parse_sssp(text)

    def test_the_statement_bound_is_refused(self):
        # Lead, 2026-11-03 (verifier #134): the second clause of Bound gives every program C(n+1)(m+1), so a row with
        # T >= n·D adds nothing and the form refuses it.
        for text in ['n^2 ; n^3', 'n ; n^3', 'n ; n^2', 'n log^3/4 ; n^2 log^3/4', 'n log ; n^2 log loglog']:
            with self.subTest(text=text), self.assertRaisesRegex(ValueError, 'below n·D: the statement already gives'):
                s.parse_sssp(text)
            with self.subTest(text=text), self.assertRaisesRegex(ValueError, 'below n·D'):
                s.parse_body(body(text))

    def test_up_to_40_digits_per_integer(self):
        self.assertEqual(s.parse_sssp('n ; n log^1/' + '9' * 40)[3], F(1, int('9' * 40)))
        with self.assertRaises(ValueError):
            s.parse_sssp('n ; n log^1/1' + '0' * 40)

    def test_the_issue_form_value_must_be_the_normal_form(self):
        self.assertEqual(s.parse_body(body())['bound'], 'n log^3/4 ; n log^11/12')
        with self.assertRaisesRegex(ValueError, 'for example'):
            s.parse_body(body('n log^0.75 ; n log^11/12'))

    def test_the_target_has_the_five_exact_rationals(self):
        sub = s.parse_body(body())
        source = s.challenge_source(sub)
        self.assertTrue(source.startswith((CHALLENGE / 'VerifierStatement.lean').read_text()))
        self.assertTrue(source.endswith(
            '\n-- Big O Speedrun exact-bound target; generated from validated integers.\n'
            'theorem Race.bound : BigOSpeedrun.DirectedSSSP.Bound ((1 : ℚ) / 1) ((3 : ℚ) / 4) ((1 : ℚ) / 1) '
            '((11 : ℚ) / 12) ((0 : ℚ) / 1) := by\n  sorry\n'))
        self.assertTrue(s.challenge_source(dict(sub, bound='n log ; n log^2 loglog^-7')).endswith(
            'Bound ((1 : ℚ) / 1) ((1 : ℚ) / 1) ((1 : ℚ) / 1) ((2 : ℚ) / 1) ((-7 : ℚ) / 1) := by\n  sorry\n'))

    def test_other_problems_keep_one_rational(self):
        self.assertEqual(s.parse_body(body('1/2').replace('directed-sssp', 'catalan'))['bound'], '1/2')
        with self.assertRaises(ValueError):
            s.parse_body(body('n ; n').replace('directed-sssp', 'catalan'))


CASES = json.loads((ROOT / 'tests/fixtures/sssp-cases.json').read_text())


class SharedCaseTests(unittest.TestCase):
    """tests/fixtures/sssp-cases.json is a byte copy of the site's data/direct-fixtures/sssp-cases.json: the site's
    data/sssp.py and src/lib/sssp.ts check the same cases, and the site's trust file pins its sha256."""
    def test_parse_and_refuse(self):
        for case in CASES['parse']:
            with self.subTest(text=case['text']):
                self.assertEqual([str(x) for x in s.parse_sssp(case['text'])], case['exponents'])
        for text in CASES['refuse']:
            with self.subTest(text=text), self.assertRaises(ValueError):
                s.parse_sssp(text)

    def test_function_lines(self):
        for row in CASES['functions']:
            terms = s.sssp_function(row['text'])
            for d, t in row['at'].items():
                with self.subTest(row=row['name'], d=d):
                    self.assertEqual(s.sssp_text(s.sssp_time_at(terms, s.sssp_density(d)), ('n', 'log', 'loglog')), t)
        for bad in ['m^1 + n', 'm  + n', 'm log log', 'm^2/4', '', 'n + log m']:
            with self.subTest(bad=bad), self.assertRaises(ValueError):
                s.sssp_function(bad)

    def test_gate(self):
        for case in CASES['gate']:
            record = {'lean_verified': [{'id': f'r{i}', 'score': p} for i, p in enumerate(case['lean_verified'])],
                      'lean_lines': [dict(l, id='chd-lean-cost', row='r0') for l in case['lean_lines']]}
            with self.subTest(candidate=case['candidate'], lines=len(case['lean_lines'])):
                candidate = s.parse_sssp(case['candidate'])
                lines = [(s.sssp_function(l['function']), s.sssp_density(l['up_to'])) for l in case['lean_lines']]
                best = s.sssp_best(candidate[:2], [s.parse_sssp(p) for p in case['lean_verified']], lines)
                self.assertEqual(None if best is None else s.sssp_text(best, ('n', 'log', 'loglog')), case['best'])
                self.assertEqual(s.qualifies_for_run({'problem': s.SSSP, 'bound': case['candidate']}, record), case['runs'])


def board(tier='verified'):
    """A directed-sssp board in the site's shape: the classic, a Claimed paper row, the Vals AI row and its line."""
    vals = {'id': 'directed-sssp-2026', 'score': 'n log^3/4 ; n log^11/12',
            'rerun_status': {'state': 'passed', 'receipt_path': 'sources/x.json'} if tier == 'verified' else None}
    return {'problem_id': 'directed-sssp/comparison-addition-sparse',
            'records': [{'id': 'classical-baseline', 'score': 'm + n log'},
                        {'id': 'directed-sssp-stoc-2025', 'score': 'm log^2/3 + n'}, vals],
            'record_metadata': {'classical-baseline': {'site_tier': 'verified'}, 'directed-sssp-stoc-2025': {'site_tier': 'claimed'},
                                'directed-sssp-2026': {'site_tier': tier}},
            'chart': {'lines': [{'id': 'chd-lean-cost', 'function': 'n + m + m logratio + m^1/3 n^2/3 log^2/3',
                                 'up_to': 'n log^3/4', 'row': 'directed-sssp-2026'}]}}


class RecordGateTests(unittest.TestCase):
    def record(self, data, issue='https://github.com/bigospeedrun/verifier/issues/200'):
        with patch.object(s, 'site_snapshot', return_value=('c' * 40, json.dumps(data).encode())):
            return s.current_record(s.SSSP, issue)

    def runs(self, bound, record):
        return s.qualifies_for_run({'problem': s.SSSP, 'bound': bound}, record)

    def test_the_lean_verified_row_and_its_line_gate(self):
        record = self.record(board())
        self.assertEqual((record['lean_verified'], [l['id'] for l in record['lean_lines']], record['site_commit']),
                         ([{'id': 'directed-sssp-2026', 'score': 'n log^3/4 ; n log^11/12'}], ['chd-lean-cost'], 'c' * 40))
        # The Lead's cases (2026-11-03): Tchd(n) = n log^2/3 ties, a better time runs; above the cap the line is silent.
        for bound, runs in [('n ; n log^2/3', False), ('n ; n log^1/2', True), ('n log^3/4 ; n log^11/12', False),
                            ('n log^1/2 ; n log^5/6', False), ('n log^1/2 ; n log^4/5', True), ('n log ; n log^2', True)]:
            with self.subTest(bound=bound):
                self.assertEqual(self.runs(bound, record), runs)

    def test_claimed_rows_the_papers_and_the_classic_never_gate(self):
        record = self.record(board('claimed'))
        self.assertEqual((record['lean_verified'], record['lean_lines']), ([], []))
        for bound in ['n ; n log^2/3', 'n log^3/4 ; n log^11/12', 'n^2 ; n^3 loglog^-1']:
            with self.subTest(bound=bound):
                self.assertTrue(self.runs(bound, record))

    def test_the_own_row_does_not_gate_its_rerun(self):
        data = board()
        data['records'][2]['submission_url'] = 'https://github.com/bigospeedrun/verifier/issues/200'
        self.assertEqual((self.record(data)['lean_verified'], self.record(data)['lean_lines']), ([], []))

    def test_an_sssp_issue_goes_through_the_selection_pass(self):
        # verifier #134: Fraction('n^2 ; n^3') stopped the pass; now the gate reads the (D, T) tuples.
        import queue_lease
        import derivation
        for data in [board('claimed'), board()]:
            lease = Mock(state={'page': 1, 'offset': 0}, admitted=Mock(return_value=False))
            item = {'number': 200, 'state': 'open', 'title': '[Lean submission] test', 'body': body('n ; n log^1/2'),
                    'user': {'login': 'submitter'}, 'created_at': '2026-11-03T12:00:00Z', 'updated_at': '2026-11-03T12:00:00Z'}
            with tempfile.TemporaryDirectory() as tmp:
                old = Path.cwd(); os.chdir(tmp)
                try:
                    with patch.dict(os.environ, GITHUB_OUTPUT=str(Path(tmp) / 'output')), \
                         patch.object(queue_lease, 'acquire', return_value=lease), \
                         patch.object(s, 'api', side_effect=lambda p, data=None: [item] if p.startswith('issues?') else []), \
                         patch.object(s, 'acknowledge'), patch.object(s, 'release'), \
                         patch.object(s, 'site_snapshot', return_value=('c' * 40, json.dumps(data).encode())), \
                         patch.object(derivation.Reader, 'get', side_effect=derivation.NotComputed('offline')):
                        s.select()
                    request = json.loads(Path('requests/200.json').read_text())
                    self.assertEqual((request['submission']['bound'], request['inputs']['challenge_file']),
                                     ('n ; n log^1/2', 'challenges/directed-sssp/VerifierStatement.lean'))
                    self.assertEqual(len(request['record_gate']['lean_lines']), 0 if data == board('claimed') else 1)
                finally:
                    os.chdir(old)


if __name__ == '__main__':
    unittest.main()
