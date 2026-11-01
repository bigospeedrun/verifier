"""Integer factoring: the upstream rerun profile (Lead, 2026-10-30, option A). Rudich and Rousseau's Challenge.lean,
byte for byte, with their one theorem Factoring.subexponentialRate (score 0), on Lean v4.35.0 tools. Closed: only a
maintainer dispatch of verify.yml runs it; the issue and PR routes do not list the problem."""
import hashlib
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import verifier as v

PROFILE = json.loads((v.ROOT / 'profiles/integer-factoring.json').read_text())
PROVENANCE = json.loads((v.ROOT / 'challenges/integer-factoring/provenance.json').read_text())
MATHLIB = '56a005855ea17e0b0958f73ec801ae140b0a1679'
REQUEST = {'repo_url': 'https://github.com/IsaacRudich/SubexponentialDeterministicFactoring',
           'commit': 'c91cc3f4947caca8977e81a5d14244f73b5ae2b1',
           'challenge_file': 'challenges/integer-factoring/Challenge.lean',
           'theorem_names': 'Factoring.subexponentialRate',
           'lean_toolchain': 'leanprover/lean4:v4.35.0'}


def git_blob(path):
    data = path.read_bytes()
    return hashlib.sha1(b'blob %d\0' % len(data) + data).hexdigest()


class FrozenFilesTests(unittest.TestCase):
    def test_challenge_license_and_manifest_are_the_upstream_bytes(self):
        challenge = v.ROOT / PROFILE['challenge_file']
        self.assertEqual(v.digest(challenge), PROFILE['challenge_sha256'])
        self.assertEqual(v.digest(challenge), PROVENANCE['sha256'])
        self.assertEqual(git_blob(challenge), PROVENANCE['git_blob'])
        self.assertEqual(git_blob(v.ROOT / 'challenges/integer-factoring/LICENSE'), PROVENANCE['license_git_blob'])
        self.assertEqual(git_blob(v.ROOT / PROFILE['manifest_file']), PROVENANCE['manifest_git_blob'])
        self.assertEqual(PROVENANCE['source_commit'], PROFILE['upstream_commit'])

    def test_the_target_is_their_score_zero_theorem_and_the_conjecture_is_only_a_definition(self):
        text = (v.ROOT / PROFILE['challenge_file']).read_text()
        self.assertIn('theorem subexponentialRate :\n    ∃ M : FactoringMachine, ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ,\n'
                      '      FactorsWithin M (fun n => C * 2 ^ (n / k)) := by\n  sorry', text)
        self.assertIn('abbrev FactoringMachine := TM2ComputableInTime encodeNat encodeNat factor', text)
        self.assertIn('def SqrtLogLogConjecture : Prop', text)
        self.assertEqual(PROFILE['theorem_names'], ['Factoring.subexponentialRate'])
        self.assertEqual(PROFILE['bound'], '0')
        self.assertEqual(set(PROFILE['permitted_axioms']), set(v.AXIOMS))

    def test_manifest_pins_mathlib_v4_35_0_and_full_revisions(self):
        manifest = json.loads((v.ROOT / PROFILE['manifest_file']).read_text())
        revs = {p['name']: p['rev'] for p in manifest['packages']}
        self.assertEqual(revs['mathlib'], MATHLIB)
        self.assertTrue(all(v.SHA.fullmatch(r) for r in revs.values()))
        self.assertIn(f'rev = "{MATHLIB}"', v.lakefile(PROFILE['source_roots'], PROFILE['manifest_file']))

    def test_v4_35_tools_change_only_comparator_and_lean4export(self):
        new = json.loads((v.ROOT / PROFILE['tools_file']).read_text())
        old = json.loads((v.ROOT / 'profiles/tools.json').read_text())
        self.assertEqual({k for k in new if new[k] != old[k]}, {'comparator', 'lean4export'})
        self.assertEqual(new['comparator'], 'e3dcf3083fc53d44b27a4431fabf7d43181583f5')
        self.assertEqual(new['lean4export'], '5a9a355dc6c5fd82b69058d433e2ae2e8dfbf8fe')


class AutoImplicitTests(unittest.TestCase):
    # Their lakefile sets no Lean options, so their sources use Lean's default autoImplicit=true.
    def test_only_the_factoring_profiles_keep_lean_default_auto_implicit(self):
        self.assertIs(PROFILE['auto_implicit'], True)
        self.assertIn('autoImplicit = true', v.lakefile([], PROFILE['manifest_file'], True))
        self.assertIn('autoImplicit = false', v.lakefile([]))
        with self.assertRaisesRegex(ValueError, 'boolean'):
            v.lakefile([], auto_implicit='true')
        profiles = [json.loads(p.read_text()) for p in (v.ROOT / 'profiles').glob('*.json')]
        profiles += list(json.loads((v.ROOT / 'profiles/direct.json').read_text()).values())
        # integer-factoring-sqrtlog builds the same upstream sources (and its submission's), which also use the default.
        self.assertEqual(sorted(p.get('challenge_file') for p in profiles if isinstance(p, dict) and 'auto_implicit' in p),
                         sorted([PROFILE['challenge_file'], 'challenges/integer-factoring-sqrtlog/Challenge.lean']))


class RequestTests(unittest.TestCase):
    def test_the_maintainer_request_selects_this_profile(self):
        profile, names = v.validate_request(dict(REQUEST))
        self.assertEqual(profile, PROFILE)
        self.assertEqual(names, ['Factoring.subexponentialRate'])

    def test_other_toolchains_and_names_are_refused(self):
        with self.assertRaisesRegex(ValueError, 'toolchain'):
            v.validate_request(dict(REQUEST, lean_toolchain='leanprover/lean4:v4.34.1'))
        for name in ['Factoring.SqrtLogLogConjecture', 'Race.bound']:
            with self.assertRaisesRegex(ValueError, 'theorem_names'):
                v.validate_request(dict(REQUEST, theorem_names=name))

    def test_closed_to_issues_and_prs(self):
        self.assertNotIn('integer-factoring', json.loads((v.ROOT / 'profiles/direct.json').read_text()))


class PrepareTests(unittest.TestCase):
    def test_their_layout_stages_without_their_challenge_or_build_files(self):
        files = {'Challenge.lean': 'module\ntheorem untrusted : False := sorry\n',
                 'Solution.lean': 'module\n\npublic import Factoring_aux\npublic import Mathlib.Data.Nat.Log\n',
                 'Factoring_aux.lean': 'module\npublic import FactoringAux.Definitions\n',
                 'FactoringAux/Definitions.lean': 'module\npublic import Mathlib.Data.Nat.Prime.Defs\n',
                 'lakefile.toml': 'untrusted build file', 'lake-manifest.json': '{}', 'comparator.json': '{}',
                 # darkhipo, #68: a submission-side copy of the statement never becomes the target.
                 'VerifierChallenge.lean': 'theorem Factoring.subexponentialRate : True := trivial\n',
                 'VerifierAudit.lean': 'theorem untrusted : False := sorry\n'}
        def clone(url, sha, dest, label, **kwargs):
            self.assertEqual((url, sha, label), (REQUEST['repo_url'], REQUEST['commit'], 'submission'))
            for name, data in files.items():
                p = dest / name; p.parent.mkdir(parents=True, exist_ok=True); p.write_text(data)
        def tree(args, **kwargs):
            root = Path(args[2])
            return b''.join(f'100644 blob {"a"*40}\t{p.relative_to(root)}\0'.encode()
                            for p in root.rglob('*') if p.is_file())
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp); event = root / 'event.json'; event.write_text(json.dumps({'inputs': REQUEST}))
            with patch.object(v, 'ART', root / 'artifacts'), patch.object(v, 'WORK', root / 'work'), \
                 patch.object(v, 'command'), patch.object(v, 'clone', side_effect=clone), \
                 patch.object(v.subprocess, 'check_output', side_effect=tree), \
                 patch.dict(os.environ, GITHUB_EVENT_PATH=str(event), BOS_REQUEST_PATH=str(event)):
                v.prepare()
                hashes = json.loads((root / 'artifacts/source-sha256.json').read_text())
                self.assertEqual(set(hashes), {'Solution.lean', 'Factoring_aux.lean', 'FactoringAux/Definitions.lean'})
                stage = root / 'work/stage'
                self.assertEqual(v.digest(stage / 'VerifierChallenge.lean'), PROFILE['challenge_sha256'])
                self.assertEqual((stage / 'lean-toolchain').read_text(), 'leanprover/lean4:v4.35.0\n')
                self.assertEqual(v.digest(stage / 'lake-manifest.json'), v.digest(v.ROOT / PROFILE['manifest_file']))
                lakefile = (stage / 'lakefile.toml').read_text()
                for name in ['Solution', 'Factoring_aux', 'FactoringAux', 'VerifierChallenge', 'VerifierAudit']:
                    self.assertIn(f'name = "{name}"', lakefile)
                self.assertNotIn('name = "Challenge"', lakefile)
                self.assertIn('autoImplicit = true', lakefile)
                self.assertEqual(json.loads((root / 'work/control/chains.json').read_text()),
                                 [['FactoringAux.Definitions', 'Factoring_aux', 'Solution']])
                control = json.loads((root / 'work/control/lean.json').read_text())
                self.assertEqual(control['theorem_names'], ['Factoring.subexponentialRate'])
                self.assertEqual(control['solution_module'], 'Solution')
                self.assertEqual(v.receipt()['profile']['tools_file'], 'profiles/tools-v4.35.0.json')


if __name__ == '__main__':
    unittest.main()
