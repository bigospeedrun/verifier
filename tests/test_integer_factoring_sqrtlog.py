"""Integer factoring at score 1/2: the upstream rerun profile of 1337isnot1337's claimed proof (Lead, 2026-10-30, option A).
The challenge is Rudich and Rousseau's Challenge.lean, byte for byte, with one appended theorem that states their
Factoring.SqrtLogLogConjecture under the claimed proof's name. Lean v4.33.1, the pins of anthropics/formal-math eth.
The proof's sources come from three pinned repositories; the eth sources keep the Lean options of their lakefile.
Closed: only a maintainer dispatch of verify.yml runs it."""
import hashlib
import json
import os
from pathlib import Path
import sys
import tempfile
import tomllib
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import verifier as v

PROFILE = json.loads((v.ROOT / 'profiles/integer-factoring-sqrtlog.json').read_text())
PROVENANCE = json.loads((v.ROOT / 'challenges/integer-factoring-sqrtlog/provenance.json').read_text())
FROZEN = v.ROOT / 'challenges/integer-factoring/Challenge.lean'
SUBMISSION = 'https://github.com/1337isnot1337/integer-factoring'
SUBMISSION_COMMIT = 'e91442d3162cae7f775e008efb2ea998c4478344'
RUDICH = 'https://github.com/IsaacRudich/SubexponentialDeterministicFactoring'
RUDICH_COMMIT = 'c91cc3f4947caca8977e81a5d14244f73b5ae2b1'
ETH = 'https://github.com/anthropics/formal-math'
ETH_COMMIT = '16a5ce41304fcdaea4e0be7c132e1c361dc26da5'
# The [leanOptions] of anthropics/formal-math eth/lakefile.toml at ETH_COMMIT.
ETH_OPTIONS = {'autoImplicit': False, 'relaxedAutoImplicit': False, 'pp.unicode.fun': True, 'exponentiation.threshold': 2048}
TARGET = 'IntegerFactoring.HalfAppendix.sqrtLogLog_factoring'
APPENDED = ('\n/- Big O Speedrun, profile integer-factoring-sqrtlog. Everything above this comment is Rudich and\n'
            "Rousseau's Challenge.lean at c91cc3f4, byte for byte. Only this theorem is added: their conjecture,\n"
            'stated as proved, under the name of the claimed proof (1337isnot1337/integer-factoring,\n'
            'formal-appendix/HalfTheorem.lean). -/\n'
            'theorem IntegerFactoring.HalfAppendix.sqrtLogLog_factoring : Factoring.SqrtLogLogConjecture := by\n'
            '  sorry\n')
REQUEST = {'repo_url': SUBMISSION, 'commit': SUBMISSION_COMMIT,
           'challenge_file': 'challenges/integer-factoring-sqrtlog/Challenge.lean',
           'theorem_names': TARGET, 'lean_toolchain': 'leanprover/lean4:v4.33.1'}


def git_blob(path):
    data = path.read_bytes()
    return hashlib.sha1(b'blob %d\0' % len(data) + data).hexdigest()


class FrozenFilesTests(unittest.TestCase):
    def test_the_challenge_is_the_frozen_upstream_file_plus_one_theorem(self):
        challenge = v.ROOT / PROFILE['challenge_file']
        self.assertEqual(challenge.read_bytes(), FROZEN.read_bytes() + APPENDED.encode())
        self.assertEqual(v.digest(FROZEN), PROVENANCE['prefix_sha256'])
        self.assertEqual(git_blob(FROZEN), PROVENANCE['prefix_git_blob'])
        self.assertEqual(v.digest(challenge), PROFILE['challenge_sha256'])
        self.assertEqual(v.digest(challenge), PROVENANCE['sha256'])
        self.assertEqual(git_blob(v.ROOT / 'challenges/integer-factoring-sqrtlog/LICENSE'), PROVENANCE['license_git_blob'])
        self.assertEqual((PROVENANCE['source_commit'], PROVENANCE['claim_commit']), (RUDICH_COMMIT, SUBMISSION_COMMIT))

    def test_the_target_is_the_conjecture_under_the_claimed_name(self):
        self.assertEqual(PROFILE['theorem_names'], [TARGET])
        self.assertEqual(PROVENANCE['appended_theorem'], TARGET)
        self.assertIn('def SqrtLogLogConjecture : Prop :=\n'
                      '  ∃ C : ℕ, FactoringInTime (fun n => C * 2 ^ (C * n / (Nat.sqrt (Nat.log 2 n) + 1)))',
                      FROZEN.read_text())
        self.assertEqual((PROFILE['bound'], PROFILE['score_relation']), ('1/2', 'attained'))
        self.assertEqual(set(PROFILE['permitted_axioms']), set(v.AXIOMS))

    def test_pins_are_the_eth_toolchain(self):
        self.assertEqual(PROFILE['lean_toolchain'], 'leanprover/lean4:v4.33.1')
        self.assertEqual(PROFILE['manifest_file'], 'profiles/anthropic-lake-manifest.json')
        self.assertEqual(PROFILE['tools_file'], 'profiles/anthropic-tools.json')
        revs = {p['name']: p['rev'] for p in json.loads((v.ROOT / PROFILE['manifest_file']).read_text())['packages']}
        self.assertEqual(revs['mathlib'], PROVENANCE['mathlib'])
        self.assertIs(PROFILE['auto_implicit'], True)

    def test_sources_come_from_the_three_pinned_repositories(self):
        self.assertEqual((PROFILE['upstream_repo'], PROFILE['upstream_commit'], PROFILE['source_subdir']),
                         (SUBMISSION, SUBMISSION_COMMIT, 'formal-appendix'))
        self.assertEqual(PROFILE['solution_module'], 'HalfTheorem')
        self.assertIn('HalfTheorem', PROFILE['source_roots'])
        deps = PROFILE['solution_dependencies']
        self.assertEqual([(d['repo_url'], d['commit'], d.get('source_subdir', '')) for d in deps],
                         [(SUBMISSION, SUBMISSION_COMMIT, 'formal'), (RUDICH, RUDICH_COMMIT, '')] +
                         [(ETH, ETH_COMMIT, f'eth/proof/{s}') for s in
                          ['statements', 'machines', 'networks', 'rates', 'consequences', 'sparsification']])
        self.assertEqual(deps[0]['source_roots'], ['HalfPad', 'HalfPrefix'])
        self.assertEqual(deps[1]['source_roots'], ['Challenge', 'FactoringAux'])
        self.assertTrue(all(d['license'] == 'Apache-2.0' for d in deps))
        self.assertTrue(all(d['lean_options'] == ETH_OPTIONS for d in deps[2:]))
        self.assertTrue(all('lean_options' not in d for d in deps[:2]))
        roots = v.build_roots(PROFILE)
        self.assertEqual(len(roots), len(set(roots)))


class RequestTests(unittest.TestCase):
    def test_the_maintainer_request_selects_this_profile(self):
        profile, names = v.validate_request(dict(REQUEST))
        self.assertEqual(profile, PROFILE)
        self.assertEqual(names, [TARGET])

    def test_other_toolchains_and_names_are_refused(self):
        with self.assertRaisesRegex(ValueError, 'toolchain'):
            v.validate_request(dict(REQUEST, lean_toolchain='leanprover/lean4:v4.35.0'))
        for name in ['Factoring.subexponentialRate', 'Factoring.SqrtLogLogConjecture']:
            with self.assertRaisesRegex(ValueError, 'theorem_names'):
                v.validate_request(dict(REQUEST, theorem_names=name))

    def test_closed_to_issues_and_prs(self):
        direct = json.loads((v.ROOT / 'profiles/direct.json').read_text())
        self.assertFalse([k for k, p in direct.items() if 'integer-factoring' in p.get('challenge_file', '')] +
                         [k for k in direct if 'factoring' in k])


class LeanOptionsTests(unittest.TestCase):
    def test_a_dependency_gives_its_roots_its_options(self):
        text = v.lakefile(['A', 'B'], auto_implicit=True, root_options={'B': ETH_OPTIONS})
        libs = {lib['name']: lib for lib in tomllib.loads(text)['lean_lib']}
        self.assertEqual(tomllib.loads(text)['leanOptions'], {'autoImplicit': True})
        self.assertNotIn('leanOptions', libs['A'])
        # Lake reads a nested table as a dotted option name (Lake.Load.Toml decodeLeanOptionsAux), as in eth's lakefile.
        self.assertEqual(libs['B']['leanOptions'], {'autoImplicit': False, 'relaxedAutoImplicit': False,
                                                   'pp': {'unicode': {'fun': True}}, 'exponentiation': {'threshold': 2048}})
        self.assertIn('[lean_lib.leanOptions]\nautoImplicit = false\nexponentiation.threshold = 2048\n', text)

    def test_bad_options_are_refused(self):
        for options in [{}, {'autoImplicit': 'text'}, {'exponentiation.threshold': -1}, {'exponentiation.threshold': 1.5},
                        {'bad name': True}, {'x;y': 1}, [],
                        # A valid name that is not reviewed: refused by the allowlist.
                        {'debug.skipKernelTC': True}, {'maxHeartbeats': 0}]:
            with self.assertRaises(ValueError):
                v.lakefile(['A'], root_options={'A': options})
        with self.assertRaisesRegex(ValueError, 'not built'):
            v.lakefile(['A'], root_options={'B': {'autoImplicit': True}})
        clash = [{'source_roots': ['A'], 'lean_options': {'autoImplicit': True}},
                 {'source_roots': ['A'], 'lean_options': {'autoImplicit': False}}]
        with self.assertRaisesRegex(ValueError, 'different Lean options'):
            v.dependency_root_options(clash, ['Submission'])
        self.assertEqual(v.dependency_root_options([{'source_roots': ['A']}], ['Submission']), {})

    def test_a_dependency_root_must_not_be_a_submission_verifier_or_reserved_root(self):
        # It fails at prepare, before any build, with or without lean_options.
        for root in ['Submission', 'VerifierChallenge', 'VerifierX', 'Lean', 'Init']:
            for dep in [{'source_roots': ['A', root]}, {'source_roots': [root], 'lean_options': {'autoImplicit': False}}]:
                with self.assertRaisesRegex(ValueError, 'dependency root'):
                    v.dependency_root_options([dep], ['Submission'])
        self.assertEqual(v.dependency_root_options(PROFILE['solution_dependencies'], PROFILE['source_roots'])['StepMachines'],
                         ETH_OPTIONS)

    def test_other_profiles_get_no_option_blocks(self):
        profiles = [json.loads(p.read_text()) for p in (v.ROOT / 'profiles').glob('*.json')]
        profiles += list(json.loads((v.ROOT / 'profiles/direct.json').read_text()).values())
        for p in profiles:
            if not isinstance(p, dict) or 'challenge_file' not in p or p is PROFILE or p == PROFILE:
                continue
            deps = p.get('solution_dependencies', [])
            self.assertFalse(any('lean_options' in d for d in deps), p['challenge_file'])
            roots = p.get('source_roots', ['Submission']) + [r for d in deps for r in d['source_roots']]
            text = v.lakefile(roots, p.get('manifest_file', 'profiles/lake-manifest.json'), p.get('auto_implicit', False),
                              v.dependency_root_options(deps, p.get('source_roots', ['Submission'])))
            self.assertNotIn('[lean_lib.leanOptions]', text)
            self.assertEqual(text, v.lakefile(roots, p.get('manifest_file', 'profiles/lake-manifest.json'),
                                              p.get('auto_implicit', False)))


class PrepareTests(unittest.TestCase):
    def test_the_claimed_layout_stages_from_the_three_repositories(self):
        trees = {
            (SUBMISSION, 'submission'): {
                'formal-appendix/HalfTheorem.lean': 'import Bridge\nimport GeneralPieces.Main\n',
                'formal-appendix/Bridge.lean': 'import HalfPad\nimport Challenge\nimport FactoringAux.Defs\n',
                'formal-appendix/Unused.lean': 'theorem unused : True := trivial\n',
                'formal/HalfPad.lean': 'import Mathlib.Data.Nat.Log\n', 'formal/Other.lean': '',
                'Makefile': 'untrusted', 'lean-toolchain': 'untrusted'},
            (SUBMISSION, 'solution-dependency-0'): None,
            (RUDICH, 'solution-dependency-1'): {
                'Challenge.lean': 'module\npublic import Mathlib.Data.Nat.Log\n',
                'FactoringAux/Defs.lean': 'module\n', 'Solution.lean': 'untrusted', 'lakefile.toml': 'untrusted'},
            (ETH, 'eth'): {
                'eth/proof/rates/GeneralPieces/Main.lean': 'import ToTuring.Poly\n',
                'eth/proof/machines/ToTuring/Poly.lean': 'import Mathlib.Data.Nat.Log\n',
                'eth/Challenge.lean': 'theorem eth_untrusted : False := sorry\n', 'eth/lakefile.toml': 'untrusted'},
        }
        profile = dict(PROFILE, source_roots=['HalfTheorem', 'Bridge'], solution_dependencies=[
            dict(PROFILE['solution_dependencies'][0], source_roots=['HalfPad']),
            dict(PROFILE['solution_dependencies'][1], source_roots=['Challenge', 'FactoringAux']),
            dict(PROFILE['solution_dependencies'][3], source_roots=['ToTuring']),
            dict(PROFILE['solution_dependencies'][5], source_roots=['GeneralPieces'])])
        def clone(url, sha, dest, label, **kwargs):
            key = (url, 'eth' if url == ETH else label)
            files = trees[key] if trees.get(key) is not None else trees[(SUBMISSION, 'submission')]
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
                 patch.object(v, 'validate_request', return_value=(profile, [TARGET])), \
                 patch.object(v.subprocess, 'check_output', side_effect=tree), \
                 patch.dict(os.environ, GITHUB_EVENT_PATH=str(event), BOS_REQUEST_PATH=str(event)):
                v.prepare()
                hashes = json.loads((root / 'artifacts/source-sha256.json').read_text())
                self.assertEqual(set(hashes), {'HalfTheorem.lean', 'Bridge.lean', 'HalfPad.lean', 'Challenge.lean',
                                               'FactoringAux/Defs.lean', 'ToTuring/Poly.lean', 'GeneralPieces/Main.lean'})
                stage = root / 'work/stage'
                self.assertEqual(v.digest(stage / 'VerifierChallenge.lean'), PROFILE['challenge_sha256'])
                self.assertEqual((stage / 'lean-toolchain').read_text(), 'leanprover/lean4:v4.33.1\n')
                config = tomllib.loads((stage / 'lakefile.toml').read_text())
                self.assertEqual(config['leanOptions'], {'autoImplicit': True})
                with_options = {lib['name'] for lib in config['lean_lib'] if 'leanOptions' in lib}
                self.assertEqual(with_options, {'ToTuring', 'GeneralPieces'})
                planned = {m for chain in json.loads((root / 'work/control/chains.json').read_text()) for m in chain}
                self.assertEqual(planned, {'HalfTheorem', 'Bridge', 'HalfPad', 'Challenge', 'FactoringAux.Defs',
                                           'GeneralPieces.Main', 'ToTuring.Poly'})
                control = json.loads((root / 'work/control/lean.json').read_text())
                self.assertEqual((control['theorem_names'], control['solution_module']), ([TARGET], 'HalfTheorem'))


if __name__ == '__main__':
    unittest.main()
