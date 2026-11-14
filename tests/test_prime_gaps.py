import hashlib
import json
from pathlib import Path
import os
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import submissions as s
import verifier as v

CHALLENGE = ROOT / 'challenges/prime-gaps'
PROFILE = json.loads((ROOT / 'profiles/direct.json').read_text())['prime-gaps']


def submission(bound='246'):
    return {'schema_version': 1, 'problem': 'prime-gaps', 'bound': bound, 'repo_url': 'https://github.com/someone/gaps',
            'commit': 'a' * 40, 'authors': []}


class PrimeGapsStatementTests(unittest.TestCase):
    def test_the_statement_imports_only_mathlib_and_has_no_proof(self):
        text = (CHALLENGE / 'Statement.lean').read_text()
        imports = [line for line in text.splitlines() if line.startswith('import')]
        self.assertEqual(imports, ['import Mathlib.Data.Nat.Nth', 'import Mathlib.Data.Nat.Prime.Defs',
                                   'import Mathlib.Order.Filter.AtTopBot.Basic'])
        self.assertNotIn('sorry', text)
        self.assertNotIn('axiom', text.replace('Axiom Math', ''))

    def test_the_target_is_axiom_math_conclusion_with_b(self):
        # AxiomMath/PrimeGapsLib@1faa7b1 PrimeGaps/Bounded246.lean, with 246 replaced by B.
        provenance = json.loads((CHALLENGE / 'provenance.json').read_text())
        self.assertEqual(provenance['source_commit'], '1faa7b14e82ddebc2772dfb9153922f01b106477')
        original = provenance['original_statement']
        self.assertTrue(original.endswith('≤ 246'))
        text = (CHALLENGE / 'Statement.lean').read_text()
        self.assertIn('def Bound (B : ℕ) : Prop :=\n  ' + original.removesuffix('246') + 'B\n', text)
        self.assertIn('namespace BigOSpeedrun.PrimeGaps', text)

    def test_the_reviewed_statement_bytes(self):
        digest = hashlib.sha256((CHALLENGE / 'Statement.lean').read_bytes()).hexdigest()
        self.assertEqual(digest, 'c6b81e94927315c805bd34a30796d8d757156790dff243287811f3c53494f969')



class ProfileTests(unittest.TestCase):
    def test_the_profile_pins_the_statement_and_the_proof_libraries(self):
        # Task cbea6e9e: Lean v4.33.1 + Mathlib 0df444a (the anthropic pins), whole gaps up to 100000, a split run.
        self.assertEqual(PROFILE['challenge_sha256'], hashlib.sha256((ROOT / PROFILE['challenge_file']).read_bytes()).hexdigest())
        self.assertEqual((PROFILE['lean_toolchain'], PROFILE['manifest_file'], PROFILE['tools_file']),
                         ('leanprover/lean4:v4.33.1', 'profiles/anthropic-lake-manifest.json', 'profiles/anthropic-tools.json'))
        self.assertEqual((PROFILE['source_roots'], PROFILE['theorem_names'], PROFILE['maximum'], PROFILE['runner']),
                         (['Submission'], ['Race.bound'], '100000', 'github-split'))
        # PNT+ (kimihiro64 fork) imports LeanArchitect (module Architect); both at the commits of
        # kimihiro64/bombieri-vinogradov@7a17483's lake-manifest.json.
        self.assertEqual([(d['repo_url'], d['commit'], d['source_roots']) for d in PROFILE['solution_dependencies']], [
            ('https://github.com/hanwenzhu/LeanArchitect', 'd9013cc08bd2b5483e837368dfa4cc7ead92a5c2', ['Architect']),
            ('https://github.com/kimihiro64/PrimeNumberTheoremAnd', '0f15a38c619298b5cd786d39a84dd4bb8997324c', ['PrimeNumberTheoremAnd'])])
        # Opened on 2026-11-07 after its smoke (run 42305726764, issue #172) and the refused control and mutations.
        self.assertNotIn('prime-gaps', s.CLOSED)
        form = (ROOT / '.github/ISSUE_TEMPLATE/lean-submission.yml').read_text()
        self.assertIn('heilbronn-triangle, directed-sssp, prime-gaps, 3sat]', form)
        self.assertEqual(s.board_line('prime-gaps'), 'Bounded prime gaps board: https://bigospeedrun.com/other/prime-gaps')
        self.assertIn('prime-gaps', s.OTHER)

    def test_target_and_whole_number_bounds(self):
        source = s.challenge_source(submission())
        self.assertTrue(source.startswith((CHALLENGE / 'Statement.lean').read_text()))
        self.assertTrue(source.endswith('theorem Race.bound : BigOSpeedrun.PrimeGaps.Bound 246 := by\n  sorry\n'))
        for good in ['246', '2', '0', '100000']:
            self.assertEqual(s.validate_submission(submission(good))['bound'], good)
        self.assertEqual(s.validate_submission(submission('492/2'))['bound'], '246')
        for bad in ['491/2', '246.5', '100001', '-1']:
            with self.assertRaises(ValueError):
                s.validate_submission(submission(bad))

    def test_the_submission_root_builds_with_axiom_math_options(self):
        # Axiom Math's PrimeGapsLib builds with maxSynthPendingDepth = 3 (its lakefile.toml at 1faa7b1).
        text = v.lakefile(PROFILE['source_roots'] + ['Architect', 'PrimeNumberTheoremAnd', 'VerifierChallenge', 'VerifierAudit'],
                          PROFILE['manifest_file'], False, v.source_root_options(PROFILE))
        self.assertIn('[[lean_lib]]\nname = "Submission"\n[lean_lib.leanOptions]\nautoImplicit = false\nmaxSynthPendingDepth = 3\n', text)
        # LeanArchitect's lakefile at d9013cc sets no options, so it keeps Lean's default autoImplicit = true
        # (Architect/CollectUsed.lean binds m implicitly; smoke run 42301733703 failed there with false).
        # PNT+ sets autoImplicit = false itself, as the package does.
        self.assertIn('[[lean_lib]]\nname = "Architect"\n[lean_lib.leanOptions]\nautoImplicit = true\n', text)
        self.assertIn('[[lean_lib]]\nname = "PrimeNumberTheoremAnd"\n\n', text)
        self.assertNotIn('maxSynthPendingDepth', text.split('name = "VerifierChallenge"')[1])
        with self.assertRaises(ValueError):
            v.source_root_options(dict(PROFILE, source_lean_options={'maxHeartbeats': 0}))

    def test_no_other_profile_has_root_options_or_data_files(self):
        # Lead, 2026-11-06: both are for prime-gaps only.
        profiles = json.loads((ROOT / 'profiles/direct.json').read_text())
        profiles.update({p.name: json.loads(p.read_text()) for p in (ROOT / 'profiles').glob('*.json') if p.name != 'direct.json'})
        holders = {name for name, p in profiles.items() if isinstance(p, dict) and ({'source_lean_options', 'source_data_suffixes'} & set(p))}
        self.assertEqual(holders, {'prime-gaps'})

    def test_only_reviewed_data_suffixes(self):
        self.assertEqual(v.data_suffixes(PROFILE), {'.json'})
        self.assertEqual(v.data_suffixes({}), set())
        for bad in [['.olean'], ['.so'], '.json', ['.lean']]:
            with self.assertRaises(ValueError):
                v.data_suffixes({'source_data_suffixes': bad})
        self.assertTrue(v.DATA_PART.fullmatch('k50e25d25n1295.json'))
        for bad in ['..', '.hidden', 'a b.json', '']:
            self.assertFalse(v.DATA_PART.fullmatch(bad))


    def test_prepare_stages_the_certificate_json_but_no_other_file(self):
        request = s.make_request(s.validate_submission(submission()))
        def clone(url, sha, dest, label, **kwargs):
            files = ({'Submission.lean': 'import Submission.Cert\n', 'Submission/Cert.lean': 'import Mathlib\n',
                      'Submission/Cert/k50e25d25n1295.json': '{}', 'Submission/Cert/build.sh': 'echo', 'Other/x.json': '{}',
                      'lakefile.toml': 'untrusted'} if label == 'submission' else
                     {'Architect.lean': 'import Lean\n', 'Architect/x.json': '{}'} if label == 'solution-dependency-0' else
                     {'PrimeNumberTheoremAnd/A.lean': 'import Architect\n'})
            for name, data in files.items():
                path = dest / name; path.parent.mkdir(parents=True, exist_ok=True); path.write_text(data)
        def tree(args, **kwargs):
            root = Path(args[2])
            return b''.join(f'100644 blob {"a"*40}\t{p.relative_to(root)}\0'.encode() for p in root.rglob('*') if p.is_file())
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp); event = root / 'event.json'; event.write_text(json.dumps({'inputs': request}))
            with patch.object(v, 'ART', root / 'artifacts'), patch.object(v, 'WORK', root / 'work'), \
                 patch.object(v, 'command'), patch.object(v, 'clone', side_effect=clone), \
                 patch.object(v.subprocess, 'check_output', side_effect=tree), \
                 patch.dict(os.environ, GITHUB_EVENT_PATH=str(event), BOS_REQUEST_PATH=str(event), BOS_SPLIT=''):
                v.prepare()
                hashes = json.loads((root / 'artifacts/source-sha256.json').read_text())
                # The JSON inside the submission root is staged and hashed; a data file of a dependency, a script, a
                # file outside the roots and the build file are not.
                self.assertEqual(set(hashes), {'Submission.lean', 'Submission/Cert.lean', 'Submission/Cert/k50e25d25n1295.json',
                                               'Architect.lean', 'PrimeNumberTheoremAnd/A.lean'})
                lake = (root / 'work/stage/lakefile.toml').read_text()
                self.assertIn('maxSynthPendingDepth = 3', lake)
                self.assertIn('rev = "0df444a360eaa60ab8c11dca51a86af692955474"', lake)

    def test_a_large_or_oddly_named_data_file_is_refused(self):
        request = s.make_request(s.validate_submission(submission()))
        for name, data in [('Submission/big.json', 'x' * (v.DATA_MAX_BYTES + 1)), ('Submission/a b.json', '{}'), ('Submission.json', '{}')]:
            def clone(url, sha, dest, label, **kwargs):
                files = {'Submission.lean': 'import Mathlib\n', name: data} if label == 'submission' else {}
                for n, d in files.items():
                    path = dest / n; path.parent.mkdir(parents=True, exist_ok=True); path.write_text(d)
            def tree(args, **kwargs):
                root = Path(args[2])
                return b''.join(f'100644 blob {"a"*40}\t{p.relative_to(root)}\0'.encode() for p in root.rglob('*') if p.is_file())
            with self.subTest(name=name), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp); event = root / 'event.json'; event.write_text(json.dumps({'inputs': request}))
                with patch.object(v, 'ART', root / 'artifacts'), patch.object(v, 'WORK', root / 'work'), \
                     patch.object(v, 'command'), patch.object(v, 'clone', side_effect=clone), \
                     patch.object(v.subprocess, 'check_output', side_effect=tree), \
                     patch.dict(os.environ, GITHUB_EVENT_PATH=str(event), BOS_REQUEST_PATH=str(event), BOS_SPLIT=''):
                    if name == 'Submission.json':
                        v.prepare()  # not inside a root folder: not staged
                        self.assertNotIn(name, json.loads((root / 'artifacts/source-sha256.json').read_text()))
                    else:
                        with self.assertRaises(ValueError):
                            v.prepare()


if __name__ == '__main__':
    unittest.main()
