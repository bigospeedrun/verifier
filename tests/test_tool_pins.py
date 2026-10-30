"""Tool pins shared by every profile. nanoda 8de7e0c4 (2026-10-29) replaced 3a240721 in all tool files on 2026-10-30
(Lead): it adds the nested-inductive recursor, inductive-block parser and Quot hardening fixes."""
import json
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import verifier as v

NANODA = '8de7e0c4ed3052745a7f8725164efd9e76d84c56'


def profiles():
    found = []
    for path in sorted((v.ROOT / 'profiles').glob('*.json')):
        data = json.loads(path.read_text())
        if path.name == 'direct.json':
            found += list(data.values())
        elif isinstance(data, dict) and 'challenge_file' in data:
            found.append(data)
    return found


class ToolPinTests(unittest.TestCase):
    def test_every_profile_uses_a_tool_file_with_the_one_nanoda_pin(self):
        files = {p.get('tools_file', 'profiles/tools.json') for p in profiles()}
        self.assertEqual(files, {'profiles/tools.json', 'profiles/anthropic-tools.json', 'profiles/tools-v4.35.0.json'})
        for name in files:
            pins = json.loads((v.ROOT / name).read_text())
            self.assertEqual(pins['nanoda'], NANODA, name)
            self.assertTrue(all(v.SHA.fullmatch(pins[k]) for k in ['comparator', 'lean4export', 'landrun', 'nanoda']), name)


if __name__ == '__main__':
    unittest.main()
