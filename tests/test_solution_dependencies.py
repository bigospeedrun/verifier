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
                 patch.dict(os.environ, GITHUB_EVENT_PATH=str(event), BOS_REQUEST_PATH=str(event)):
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
                self.assertTrue(calls[0][2]['sparse_paths'])
                control = json.loads((root / 'work/control/lean.json').read_text())
                self.assertEqual(set(control['permitted_axioms']), {'propext', 'Classical.choice', 'Quot.sound'})

    def test_matrix_profile_enables_only_nine_fourths(self):
        profile = json.loads((v.ROOT / 'profiles/matrix-nine-fourths.json').read_text())
        self.assertEqual(profile['theorem_names'], ['OAI.MatrixMultiplication.complex_omega_le_nine_quarters'])
        self.assertEqual(v.digest(v.ROOT / profile['challenge_file']), profile['challenge_sha256'])
