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
        self.assertEqual(files, {'profiles/tools.json', 'profiles/anthropic-tools.json', 'profiles/tools-v4.35.0.json', 'profiles/tools-chain.json',
                                 'profiles/tools-v4.33.0-rc2.json'})
        for name in files:
            pins = json.loads((v.ROOT / name).read_text())
            self.assertEqual(pins['nanoda'], NANODA, name)
            self.assertTrue(all(v.SHA.fullmatch(pins[k]) for k in ['comparator', 'lean4export', 'landrun', 'nanoda']), name)


    def test_lean4export_patches_match_their_pins(self):
        """profiles/tools.json patches lean4export 076e8e5 with PR #52 (print) and PR #60 (parse); docs/execution.md,
        Patched lean4export. Drop them when upstream merges both and the pin moves past them."""
        pins = json.loads((v.ROOT / 'profiles/tools.json').read_text())
        self.assertEqual(pins['lean4export'], '076e8e57707e813375e8f9da8bf989799ace9680')
        self.assertEqual([x['file'] for x in pins['lean4export_patches']],
                         ['patches/lean4export-pr52-natlit-print.patch', 'patches/lean4export-natlit-parse.patch'])
        for item in pins['lean4export_patches']:
            self.assertEqual(v.digest(v.ROOT / item['file']), item['sha256'], item['file'])
        for name in ['profiles/anthropic-tools.json', 'profiles/tools-v4.35.0.json', 'profiles/tools-v4.33.0-rc2.json']:
            self.assertNotIn('lean4export_patches', json.loads((v.ROOT / name).read_text()), name)
        self.assertTrue((v.ROOT / 'tests/lean/NatTest.lean').is_file())

    def test_the_chain_tool_file_is_tools_json_plus_the_comparator_patch(self):
        """profiles/tools-chain.json (runner github-chain, docs/execution.md, Segmented check): the same pins as
        profiles/tools.json, and the reviewed Comparator patch. No other tool file patches Comparator."""
        chain = json.loads((v.ROOT / 'profiles/tools-chain.json').read_text())
        patches = chain.pop('comparator_patches')
        plain = json.loads((v.ROOT / 'profiles/tools.json').read_text())
        plain.pop('comparator_nanoda_patches')  # a chain runs no nanoda (docs/execution.md), so it needs no thread patch
        self.assertEqual(chain, plain)
        self.assertNotIn('comparator_nanoda_patches', chain)
        self.assertEqual([x['file'] for x in patches], ['patches/comparator-segmented-check.patch'])
        for item in patches:
            self.assertEqual(v.digest(v.ROOT / item['file']), item['sha256'], item['file'])
        for name in ['profiles/tools.json', 'profiles/anthropic-tools.json', 'profiles/tools-v4.35.0.json', 'profiles/tools-v4.33.0-rc2.json']:
            self.assertNotIn('comparator_patches', json.loads((v.ROOT / name).read_text()), name)

    def test_the_nanoda_thread_patch_is_pinned_for_the_two_comparators_that_hard_code_four_threads(self):
        """Task be5e47b3: Comparator d03acab and e3dcf30 (profiles/tools.json, tools-v4.35.0.json) write "num_threads": 4 for
        nanoda; the patch reads COMPARATOR_NANODA_THREADS. The older Comparator pins (anthropic-tools.json,
        tools-v4.33.0-rc2.json) write no num_threads, so nanoda runs one worker there already: no patch. It is its own key,
        because comparator_patches also starts the segmented-check self-test (verifier.setup)."""
        for name in ['profiles/tools.json', 'profiles/tools-v4.35.0.json']:
            items = json.loads((v.ROOT / name).read_text())['comparator_nanoda_patches']
            self.assertEqual([x['file'] for x in items], ['patches/comparator-nanoda-threads.patch'], name)
            self.assertEqual(v.digest(v.ROOT / items[0]['file']), items[0]['sha256'], name)
        for name in ['profiles/anthropic-tools.json', 'profiles/tools-v4.33.0-rc2.json', 'profiles/tools-chain.json']:
            self.assertNotIn('comparator_nanoda_patches', json.loads((v.ROOT / name).read_text()), name)
        text = (v.ROOT / 'patches/comparator-nanoda-threads.patch').read_text()
        self.assertEqual((text.count('+      | some "1" => 1'), text.count('-      ("num_threads", 4),')), (1, 1))
        # verifier#226: the same patch passes nanoda's worker stack size, from COMPARATOR_NANODA_STACK_MIB (verifier.py NANODA_STACK_MIB).
        self.assertEqual([text.count(f'+      | some "{n}" => {n}') for n in v.NANODA_STACK_MIB], [1, 1, 1])
        self.assertEqual(text.count('+      ("stack_size_bytes", nanodaStackBytes),'), 1)
        # The two pinned Main.lean files are the same, so one patch fits both (checked on the clones, 2026-11-23).
        self.assertEqual(json.loads((v.ROOT / 'profiles/tools.json').read_text())['comparator'], 'd03acab154d269c06e60e4de7e4cc85deebff94b')
        self.assertEqual(json.loads((v.ROOT / 'profiles/tools-v4.35.0.json').read_text())['comparator'], 'e3dcf3083fc53d44b27a4431fabf7d43181583f5')


if __name__ == '__main__':
    unittest.main()
