import importlib.util
import json
from pathlib import Path
import tempfile
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
# verifier.py imports verdicts from scripts/, as when it runs there; the test then also runs alone.
sys.path.insert(0, str(ROOT / 'scripts'))
spec = importlib.util.spec_from_file_location('verifier', ROOT / 'scripts/verifier.py')
v = importlib.util.module_from_spec(spec); spec.loader.exec_module(v)


class RequestTests(unittest.TestCase):
    def request(self):
        return {'repo_url': 'https://github.com/chafreaky/wht-power-saving-lean',
                'commit': '837dc3130adc79f7b7ab4ddd56c15576bbd766b0',
                'challenge_file': 'challenges/dft/UniformFourier233.lean',
                'theorem_names': 'OAI.PowerSaving.transform_mainY,OAI.PowerSaving.convolution_mainY',
                'lean_toolchain': 'leanprover/lean4:v4.34.1'}

    def test_reviewed_request(self):
        profile, names = v.validate_request(self.request())
        self.assertEqual(len(names), 2)
        self.assertEqual(profile['saving'], '7547360/10000000000')

    def test_untrusted_inputs_rejected(self):
        for key, value in [('repo_url', 'file:///etc/passwd'),
                           ('repo_url', 'https://user:secret@github.com/a/b'),
                           ('repo_url', 'https://github.com/a/b?x=y'),
                           ('commit', 'main'), ('commit', '-oops'),
                           ('challenge_file', '../submission/Challenge.lean'),
                           ('challenge_file', 'Work/Fourier233/UniformFourierChallenge.lean'),
                           ('theorem_names', 'True'),
                           ('theorem_names', 'OAI.PowerSaving.transform_mainY\n#eval IO.println "x"'),
                           ('lean_toolchain', 'nightly')]:
            with self.subTest(key=key, value=value):
                req = self.request(); req[key] = value
                with self.assertRaises(ValueError): v.validate_request(req)

    def test_trusted_challenge_is_independent(self):
        s = (ROOT / self.request()['challenge_file']).read_text()
        self.assertIn('import Mathlib', s)
        self.assertNotIn('import Work.', s)
        self.assertIn('def DFTProgram', s)
        self.assertIn('7547360/(10^(10:ℕ))', s)


class ChainTests(unittest.TestCase):
    def stage(self, files):
        tmp = tempfile.TemporaryDirectory(); self.addCleanup(tmp.cleanup)
        root = Path(tmp.name)
        for name, text in files.items():
            p = root / (name.replace('.', '/') + '.lean'); p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(text)
        return root

    def test_branches_stay_separate(self):
        root = self.stage({'X.A': 'import Mathlib\n', 'X.B': 'import X.A\n',
                           'X.C': 'import X.A\n', 'X.D': 'import X.B X.C\n'})
        self.assertEqual(v.plan_sources(root, 'X.D'), [['X.A', 'X.B'], ['X.C', 'X.D']])

    def test_nested_comments(self):
        root = self.stage({'X.A': '/- import Fake /- nested -/ -/\nimport Mathlib -- comment\n',
                           'X.B': 'import X.A\ntheorem b : True := by trivial\n'})
        self.assertEqual(v.plan_sources(root, 'X.B'), [['X.A', 'X.B']])

    def test_cycle_and_reserved_import(self):
        for files, target in [({'A': 'import B\n', 'B': 'import A\n'}, 'A'),
                              ({'A': 'import VerifierChallenge\n'}, 'A')]:
            with self.assertRaises(ValueError): v.plan_sources(self.stage(files), target)


class ReceiptStatusTests(unittest.TestCase):
    """verifier#194 (darkhipo): the receipt's status is the verdict's own rule, with each check's outcome apart."""
    NAME = 'BigOSpeedrun.Catalan.bound'

    def receipt(self, status='not_verified', lean='passed', nanoda=None, axioms=('propext',), stage='final'):
        nanoda = nanoda or {'status': 'incomplete', 'reason': 'out_of_memory'}
        data = {'status': status, 'theorem_names': [self.NAME], 'verification_stage': stage,
                'kernels': {'lean': {'status': lean, 'reason': 'comparator_acceptance'}, 'nanoda': nanoda},
                'axiom_audit': {'status': 'passed', 'reported_axioms': {self.NAME: list(axioms)}}}
        data['theorems'] = {self.NAME: {'lean_kernel': lean, 'nanoda_kernel': nanoda['status'], 'reported_axioms': list(axioms)}}
        return data

    def test_nanoda_out_of_memory_matches_the_verdict(self):
        # Run 43148643813 (#187): Lean and the audit passed, nanoda was OOM-killed; the receipt said not_verified.
        data = self.receipt(); v.receipt_status(data)
        self.assertEqual((data['status'], data['status_reason']), ('passed', 'lean_and_axiom_passed_nanoda_incomplete'))
        self.assertEqual(data['check_summary'], {'lean': 'passed (comparator_acceptance)', 'axiom_audit': 'passed',
                                                 'nanoda': 'incomplete (out_of_memory)'})

    def test_lean_checkpoint_passes_with_nanoda_queued(self):
        data = self.receipt(nanoda={'status': 'pending', 'reason': 'advisory_queued'}, stage='lean'); v.receipt_status(data)
        self.assertEqual((data['status'], data['status_reason']), ('passed', 'lean_and_axiom_passed_nanoda_pending'))

    def test_blocked_is_not_not_verified(self):
        data = self.receipt(axioms=('sorryAx',)); v.receipt_status(data)
        self.assertEqual((data['status'], data['status_reason']), ('blocked', 'unpermitted_axiom'))
        data = self.receipt(nanoda={'status': 'rejected'}); v.receipt_status(data)
        self.assertEqual(data['status'], 'blocked')

    def test_failed_lean_check_stays_not_verified(self):
        data = self.receipt(status='passed', lean='rejected'); v.receipt_status(data)
        self.assertEqual((data['status'], data['status_reason']), ('not_verified', 'lean_not_passed'))

    def test_setup_failure_and_timeout_keep_their_status(self):
        data = self.receipt(status='setup_failed'); v.receipt_status(data)
        self.assertEqual(data['status'], 'setup_failed'); self.assertNotIn('status_reason', data)
        data = self.receipt(status='timeout', lean='incomplete'); v.receipt_status(data)
        self.assertEqual(data['status'], 'timeout'); self.assertNotIn('status_reason', data)
        # A total deadline that only stopped the advisory nanoda check is the verdict's pass.
        data = self.receipt(status='timeout', nanoda={'status': 'incomplete', 'reason': 'total_deadline'}); v.receipt_status(data)
        self.assertEqual(data['status'], 'passed')


if __name__ == '__main__': unittest.main()
