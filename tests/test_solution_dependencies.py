import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import verifier as v


class SolutionDependencyTests(unittest.TestCase):
    def test_pinned_source_dependency_is_staged_hashed_and_audited(self):
        request = {'repo_url': 'https://github.com/openai/math',
                   'commit': 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',
                   'challenge_file': 'challenges/matrix-multiplication/MatrixMultiplication.lean',
                   'theorem_names': 'OAI.MatrixMultiplication.complex_omega_le_nine_quarters',
                   'lean_toolchain': 'leanprover/lean4:v4.34.1'}
        calls = []
        def clone(url, sha, dest, label, **kwargs):
            calls.append((url, sha, kwargs))
            files = ({'lean/OAI/LinearAlgebra/MatrixMultiplication/Main.lean': 'import FixedPointTheorems.brouwer\n',
                      'lean/OAI/Unrelated.lean': 'axiom bad : False\n'} if label == 'submission' else
                     {'FixedPointTheorems/brouwer.lean': 'import Mathlib\n',
                      'FixedPointTheorems/brouwer.olean': 'untrusted object',
                      'lakefile.lean': 'untrusted build code'})
            for name, data in files.items():
                p = dest / name; p.parent.mkdir(parents=True, exist_ok=True); p.write_text(data)
        def tree(args, **kwargs):
            root = Path(args[2])
            return b''.join(f'100644 blob {"a"*40}\t{p.relative_to(root)}\0'.encode()
                            for p in root.rglob('*') if p.is_file())
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp); event = root / 'event.json'; event.write_text(json.dumps({'inputs': request}))
            with patch.object(v, 'ART', root / 'artifacts'), patch.object(v, 'WORK', root / 'work'), \
                 patch.object(v, 'command') as commands, patch.object(v, 'clone', side_effect=clone), patch.object(v.subprocess, 'check_output', side_effect=tree), \
                 patch.dict(os.environ, GITHUB_EVENT_PATH=str(event), BOS_REQUEST_PATH=str(event), BOS_SPLIT=''):
                v.prepare()
                receipt = v.receipt()
                self.assertFalse(receipt['test_only'])
                self.assertEqual(receipt['solution_dependencies'][0]['commit'], '770940ddf9878cf61952ed53d910b92bca841838')
                hashes = json.loads((root / 'artifacts/source-sha256.json').read_text())
                self.assertEqual(set(hashes), {'OAI/LinearAlgebra/MatrixMultiplication/Main.lean', 'FixedPointTheorems/brouwer.lean'})
                self.assertIn('FixedPointTheorems', (root / 'work/stage/lakefile.toml').read_text())
                self.assertEqual(len(calls), 2)
                self.assertEqual(commands.call_count, 2)
                dep=receipt['solution_dependencies'][0]
                self.assertEqual(v.digest(v.ROOT / dep['patch_file']),dep['patch_sha256'])
                self.assertIn('--check',commands.call_args_list[0].args[0])
                self.assertIn('--index',commands.call_args_list[1].args[0])
                self.assertTrue(calls[0][2]['sparse_paths'])
                control = json.loads((root / 'work/control/lean.json').read_text())
                self.assertEqual(set(control['permitted_axioms']), {'propext', 'Classical.choice', 'Quot.sound'})

    def test_a_file_that_a_reviewed_patch_adds_is_listed(self):
        # OpenAI's PrimeNumberTheoremAnd and StrongPNT patches add whole folders (Erdos970). HEAD's tree does not list them;
        # after `git apply --index` the index does (integer multiplication rebuild, 2026-11-25).
        import subprocess
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp) / 'dep'; repo.mkdir()
            git = lambda *a: subprocess.run(['git', '-C', str(repo), '-c', 'user.name=t', '-c', 'user.email=t@t', *a], check=True, capture_output=True)
            git('init', '-q'); (repo / 'Pkg').mkdir(); (repo / 'Pkg/Old.lean').write_text('import Mathlib\n')
            git('add', '-A'); git('commit', '-q', '-m', 'base')
            (repo / 'Pkg/New').mkdir(); (repo / 'Pkg/New/Added.lean').write_text('import Pkg.Old\n')
            git('add', '-A'); patch_text = subprocess.check_output(['git', '-C', str(repo), 'diff', '--cached'])
            git('reset', '-q', '--hard')
            patch_file = Path(tmp) / 'p.patch'; patch_file.write_bytes(patch_text)
            git('apply', '--index', str(patch_file))
            names = lambda raw: sorted(e.split(b'\t', 1)[1].decode() for e in raw.split(b'\0') if e)
            self.assertEqual(names(v.source_files(repo, False)), ['Pkg/Old.lean'])
            self.assertEqual(names(v.source_files(repo, True)), ['Pkg/New/Added.lean', 'Pkg/Old.lean'])
            self.assertTrue(all(e.split()[0] == b'100644' for e in v.source_files(repo, True).split(b'\0') if e))

    def test_integer_multiplication_rebuild_profile(self):
        # OpenAI 92b516ef: three dependencies at OpenAI's pins with OpenAI's patches (byte copies, pinned sha256), and the
        # Lean options of each upstream lakefile: PrimeNumberTheoremAnd autoImplicit false (our default), StrongPNT Lean's
        # defaults, AbsorptionCutoff its [leanOptions] (its linter option is not a build option).
        profile = json.loads((v.ROOT / 'profiles/integer-multiplication-tapes.json').read_text())
        self.assertEqual(profile['theorem_names'], ['OAI.Computability.NearSquareRoot.uniformIntegerMultiplication'])
        self.assertEqual(v.digest(v.ROOT / profile['challenge_file']), profile['challenge_sha256'])
        self.assertEqual(profile['challenge_sha256'], '29701b0ccef385b102bc3193484d9e0a5ecde3ec0005233bd87806d570413607')
        deps = {d['source_roots'][0]: d for d in profile['solution_dependencies']}
        self.assertEqual(sorted(deps), ['AbsorptionCutoff', 'PrimeNumberTheoremAnd', 'StrongPNT'])
        for name, dep in deps.items():
            self.assertEqual(v.digest(v.ROOT / dep['patch_file']), dep['patch_sha256'], name)
            self.assertEqual(dep['patch_upstream_commit'], '92b516ef8e2abf66c3db7aa31438d3010bc7956f')
        self.assertNotIn('lean_options', deps['PrimeNumberTheoremAnd'])
        self.assertEqual(deps['StrongPNT']['lean_options'], {'autoImplicit': True})
        self.assertEqual(deps['AbsorptionCutoff']['lean_options'],
                         {'autoImplicit': True, 'relaxedAutoImplicit': False, 'maxSynthPendingDepth': 3, 'pp.unicode.fun': True})

    def test_matrix_profile_enables_only_nine_fourths(self):
        profile = json.loads((v.ROOT / 'profiles/matrix-nine-fourths.json').read_text())
        self.assertEqual(profile['theorem_names'], ['OAI.MatrixMultiplication.complex_omega_le_nine_quarters'])
        self.assertEqual(v.digest(v.ROOT / profile['challenge_file']), profile['challenge_sha256'])
