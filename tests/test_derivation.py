import base64
import json
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import derivation as d
import pr_submissions as p
import submissions as s

SITE_SHA, MAIN_SHA = 'c' * 40, 'e' * 40

EARLIER = {
    'Submission.lean': '-- Authors: Halit\nimport Submission.Main\ntheorem Race.bound : True := by\n  exact bound 30103 10000000\n',
    'Submission/Main.lean': '/- Copyright Halit. @halitziyakartal -/\ndef bound (a b : Nat) : True := trivial\n',
    'Submission/Big.lean': 'theorem big : 2 + 2 = 4 := rfl\n',
    'Submission/Data.lean': 'def table : List Nat := [1, 2, 3]\n',
    'Submission/Lemma.lean': 'theorem l : 1 = 1 := rfl\n',
}


def blob(text):
    return p.blob_sha(text.encode())


class FakeReader(d.Reader):
    """Serves one verified PR folder (earlier author) and one verified issue repository."""

    def __init__(self, folder_files, issue_files=None, issue_login='someone', limit=d.CALLS, fail=(), prs=None, withdrawn=None):
        super().__init__(limit)
        self.blobs, self.fail = {}, set(fail)
        tree = []
        for folder, files in folder_files.items():
            for rel, text in files.items():
                self.blobs[blob(text)] = text.encode()
                tree.append({'path': f'{folder}/{rel}', 'type': 'blob', 'sha': blob(text), 'size': len(text.encode())})
            tree.append({'path': f'{folder}/manifest.json', 'type': 'blob', 'sha': 'f' * 40, 'size': 30})
        self.verifier_tree = {'truncated': False, 'tree': tree}
        self.issue_tree = {'truncated': False, 'tree': [
            {'path': rel, 'type': 'blob', 'sha': blob(text), 'size': len(text)} for rel, text in (issue_files or {}).items()]}
        for text in (issue_files or {}).values():
            self.blobs[blob(text)] = text.encode()
        states = {f'direct-pr-41:{"1" * 64}': {'key': 'direct-pr-41', 'decision': 'lean-verified', 'submission': {
            'problem': 'dft', 'repo_url': 'https://github.com/bigospeedrun/verifier', 'commit': 'a' * 40,
            'source_subdir': 'submissions/dft/halitziyakartal-v4'}}}
        for key, folder in (prs or {}).items():  # More verified PR folders: {'direct-pr-43': 'ptweezy-copy'}.
            states[f'{key}:{"3" * 64}'] = {'key': key, 'decision': 'lean-verified', 'submission': {
                'problem': 'dft', 'repo_url': 'https://github.com/bigospeedrun/verifier', 'commit': 'a' * 40,
                'source_subdir': f'submissions/dft/{folder}'}}
        if issue_files:
            states[f'direct-issue-19:{"2" * 64}'] = {'key': 'direct-issue-19', 'decision': 'lean-verified', 'submission': {
                'problem': 'dft', 'repo_url': 'https://github.com/someone/proof', 'commit': 'b' * 40}}
        raw = json.dumps({'final_states': states}).encode()
        self.blobs[p.blob_sha(raw)] = raw
        self.site_blob = p.blob_sha(raw)
        notes = json.dumps({'withdrawn': withdrawn or {}}).encode()
        self.blobs[p.blob_sha(notes)] = notes
        self.notes_blob = p.blob_sha(notes)
        self.board = json.dumps({'records': [{'id': 'direct-issue-19', 'authors': [{'name': issue_login}]}] if issue_login else []}).encode()
        self.issue_login = None  # Set by a test to name the issue's submitter when no board row does.

    def get(self, repo, path):
        if path in self.fail:
            raise OSError('offline')
        if self.calls >= self.limit:
            raise d.NotComputed('API budget used')
        self.calls += 1
        return self.fetch(repo, path)

    def fetch(self, repo, path):
        if (repo, path) == (d.SITE, 'commits/main'):
            return {'sha': SITE_SHA}
        if (repo, path) == (d.SITE, f'contents/data/direct-submissions.json?ref={SITE_SHA}'):
            return {'sha': self.site_blob}
        if (repo, path) == (d.SITE, f'contents/data/direct-notes.json?ref={SITE_SHA}'):
            return {'sha': self.notes_blob}
        if path == 'git/refs/heads/main':
            return {'object': {'sha': MAIN_SHA}}
        if path == f'git/trees/{MAIN_SHA}:submissions/dft?recursive=1':
            return self.verifier_tree
        if (repo, path) == ('someone/proof', f'git/trees/{"b" * 40}?recursive=1'):
            return self.issue_tree
        if path == 'issues/19':
            return {'user': {'login': self.issue_login}} if self.issue_login else {}
        if path.startswith('git/blobs/'):
            return {'encoding': 'base64', 'content': base64.b64encode(self.blobs[path[10:]]).decode()}
        raise AssertionError((repo, path))


def run(reader, files, login='ptweezy', key='direct-pr-43'):
    cand = {rel: (blob(text), len(text.encode())) for rel, text in files.items()}
    for text in files.values():
        reader.blobs[blob(text)] = text.encode()
    with patch.object(s, 'site_snapshot', return_value=('x', reader.board)):
        return d.safe_report(reader, 'dft', login, key, lambda: (cand, s.REPOSITORY))


def earlier():
    return FakeReader({'halitziyakartal-v4': EARLIER})


def copy(**changes):
    files = dict(EARLIER)
    files.update(changes)
    return files


class DerivationTests(unittest.TestCase):
    def test_lean_scan_masks_numerals_and_moves_comments_out(self):
        code, comments = d.lean_scan('/- a /- nested -/ Author: X -/ theorem t : 2 = 0x2 := by -- by Y\n  norm_num [h3, "4"]\n')
        self.assertEqual(code, ['theorem', 't', ':', '#', '=', '#', ':', '=', 'by', 'norm_num', '[', 'h3', ',', '"4"', ']'])
        self.assertEqual([c.strip() for c in comments if c.strip()], ['a /- nested -/ Author: X -/', 'by Y'])
        self.assertEqual(d.lean_scan('x 1.5e-3')[0], d.lean_scan('x 7')[0])
        self.assertNotEqual(d.lean_scan('h1')[0], d.lean_scan('h2')[0])  # A digit inside a name is not a constant.

    def test_a_constants_only_copy_of_another_author_holds_even_with_credit_kept(self):
        # 2026-10-23: #43 and #44 kept every credit line of #41; only the constants changed.
        report = run(earlier(), copy(**{'Submission.lean': EARLIER['Submission.lean'].replace('30103', '30201')}))
        self.assertEqual((report['identical'], report['changed'], report['added'], report['removed']), (4, 1, 0, 0))
        self.assertEqual((report['constants_only'], report['credit'], report['hold']), (True, 'kept', True))
        self.assertEqual(report['closest'], {'key': 'direct-pr-41', 'url': 'https://github.com/bigospeedrun/verifier/pull/41',
                                             'files': 5, 'author_known': True})
        # Replaced credit is reported as such (#46).
        replaced = EARLIER['Submission.lean'].replace('30103', '30201').replace('Authors: Halit', 'Authors: ptweezy')
        report = run(earlier(), copy(**{'Submission.lean': replaced}))
        self.assertEqual((report['credit'], report['credit_lines'], report['hold']),
                         ('replaced', {'earlier': 1, 'kept': 0, 'missing': 1, 'new': 1}, True))

    def test_no_hold_without_positive_evidence(self):
        code_change = copy(**{'Submission/Big.lean': 'theorem big : 2 + 2 = 4 := by norm_num\n'})
        self.assertEqual(run(earlier(), code_change)['constants_only'], False)
        self.assertFalse(run(earlier(), code_change)['hold'])
        added = copy(**{'Submission/New.lean': 'theorem n : 3 = 3 := rfl\n'})
        self.assertEqual((run(earlier(), added)['added'], run(earlier(), added)['hold']), (1, False))
        # Below 80%: two of five files changed (constants only), three identical.
        low = copy(**{'Submission.lean': EARLIER['Submission.lean'].replace('30103', '1'),
                      'Submission/Data.lean': EARLIER['Submission/Data.lean'].replace('3]', '4]')})
        report = run(earlier(), low)
        self.assertEqual((report['identical'], report['constants_only'], report['hold']), (3, True, False))
        # The author's own earlier folder (login prefix) is never the match.
        own = run(earlier(), copy(**{'Submission.lean': EARLIER['Submission.lean'].replace('30103', '30201')}), login='HalitZiyaKARTAL', key='direct-pr-50')
        self.assertEqual((own['status'], own['hold']), ('no_match', False))

    def test_a_withdrawn_copy_of_the_authors_own_work_is_not_a_source(self):
        # 2026-11-01: #43 (ptweezy, withdrawn) is a copy of #41; a constants-only PR by #41's author must not
        # be held as derived from #43. The folder stays in main; the site's withdrawn list leaves it out.
        withdrawn_copy = copy(**{'Submission.lean': EARLIER['Submission.lean'].replace('30103', '30201')})
        folders = {'halitziyakartal-v4': EARLIER, 'ptweezy-copy': withdrawn_copy}
        mine = copy(**{'Submission.lean': EARLIER['Submission.lean'].replace('30103', '31278')})
        def report(withdrawn):
            reader = FakeReader(folders, prs={'direct-pr-43': 'ptweezy-copy'}, withdrawn=withdrawn)
            return run(reader, mine, login='HalitZiyaKARTAL', key='direct-pr-91')
        held = report({})  # Without the list, the copy is another author's closest source.
        self.assertEqual((held['closest']['key'], held['constants_only'], held['hold']), ('direct-pr-43', True, True))
        free = report({'direct-pr-43': 'Withdrawn by its submitter on 2026-10-23.'})
        self.assertEqual((free['status'], free['hold']), ('no_match', False))
        # Another author's constants-only copy of a withdrawn entry's base is still held through #41.
        other = run(FakeReader(folders, prs={'direct-pr-43': 'ptweezy-copy'}, withdrawn={'direct-pr-43': 'x'}), mine,
                    login='someone-else', key='direct-pr-92')
        self.assertEqual((other['closest']['key'], other['hold']), ('direct-pr-41', True))

    def test_an_issue_source_with_an_unknown_author_reports_but_never_holds(self):
        constants = copy(**{'Submission.lean': EARLIER['Submission.lean'].replace('30103', '30201')})
        for login, held in [(None, False), ('ptweezy', None), ('other', True)]:
            report = run(FakeReader({}, issue_files=EARLIER, issue_login=login), constants)
            if held is None:  # The candidate's own earlier source is skipped.
                self.assertEqual(report['status'], 'no_match')
                continue
            self.assertEqual(report['closest']['key'], 'direct-issue-19')
            self.assertEqual((report['closest']['author_known'], report['constants_only'], report['hold']), (held, True, held))

    def test_a_deleted_issue_repository_is_skipped(self):
        import urllib.error
        constants = copy(**{'Submission.lean': EARLIER['Submission.lean'].replace('30103', '30201')})
        reader = FakeReader({'halitziyakartal-v4': EARLIER}, issue_files={'Proof.lean': 'x\n'}, issue_login='other')
        fetch = reader.fetch
        def gone(repo, path):
            if repo == 'someone/proof':
                raise urllib.error.HTTPError(path, 404, 'Not Found', None, None)
            return fetch(repo, path)
        reader.fetch = gone
        self.assertEqual((run(reader, constants)['closest']['key'], run(reader, constants)['hold']), ('direct-pr-41', True))

    def test_an_issue_author_comes_from_the_issue_when_no_board_row_names_it_and_a_readme_is_not_code(self):
        # #54 (2026-10-24): its closest source #49 (Anchen0823) had no board row, and a changed README hid the
        # constants-only change.
        files = dict(EARLIER, **{'README.md': 'Authors: Halit\n'}, **{f'Submission/L{i}.lean': f'theorem l{i} : {i} = {i} := rfl\n' for i in range(5)})
        constants = dict(files, **{'Submission.lean': EARLIER['Submission.lean'].replace('30103', '30201'),
                                   'README.md': 'Authors: Halit\nThanks: a lowered constant\n'})
        for owner, held in [('other', True), ('ptweezy', None)]:
            reader = FakeReader({}, issue_files=files, issue_login=None)
            reader.issue_login = owner
            report = run(reader, constants)
            if held is None:
                self.assertEqual(report['status'], 'no_match')  # The candidate's own issue is skipped.
                continue
            self.assertEqual((report['closest']['author_known'], report['constants_only'], report['hold']), (True, True, True))
            self.assertEqual((report['credit_lines']['kept'] >= 1, report['credit_lines']['new']), (True, 1))

    def test_failures_and_caps_never_hold(self):
        constants = copy(**{'Submission.lean': EARLIER['Submission.lean'].replace('30103', '30201')})
        reader = earlier()
        reader.fail = {f'git/trees/{MAIN_SHA}:submissions/dft?recursive=1'}
        self.assertEqual(run(reader, constants), {'status': 'not_computed', 'reason': 'a read failed', 'hold': False})
        self.assertEqual(run(FakeReader({'halitziyakartal-v4': EARLIER}, limit=3), constants)['reason'], 'API budget used')
        with patch.object(d, 'MAX_BLOB', 10):
            report = run(earlier(), constants)
        self.assertEqual((report['status'], report['constants_only'], report['hold']), ('computed', None, False))
        reader = earlier()
        reader.verifier_tree['truncated'] = True
        self.assertEqual(run(reader, constants)['reason'], 'incomplete Git tree')

    def test_the_comment_quotes_no_file_content_and_is_posted_once_per_version(self):
        secret = EARLIER['Submission.lean'].replace('30103', '30201').replace('Authors: Halit', 'Authors: <script>x</script>')
        report = run(earlier(), copy(**{'Submission.lean': secret}))
        body = d.comment(43, 'a' * 40, report, 'pull_request')
        self.assertTrue(body.startswith(f'{d.MARKER}43 {"a" * 40} -->\n'))
        self.assertNotIn('script', body)
        self.assertNotIn('Submission', body)
        self.assertIn('Hold:', body)
        posts = []
        with patch.object(s, 'api', side_effect=lambda path, data=None: posts.append((path, data))):
            d.post(43, 'a' * 40, report, 'pull_request', [])
            bot = {'user': {'login': 'github-actions[bot]', 'type': 'Bot'}, 'body': posts[0][1]['body']}
            d.post(43, 'a' * 40, report, 'pull_request', [bot])
            d.post(43, 'b' * 40, report, 'pull_request', [bot])  # A new head is a new version.
        self.assertEqual([path for path, _ in posts], ['issues/43/comments', 'issues/43/comments'])
        for status in [{'status': 'no_match', 'hold': False}, {'status': 'not_computed', 'reason': 'API budget used', 'hold': False}]:
            self.assertNotIn('Hold:', d.comment(1, 'v', status, 'issue'))

    def test_source_files_skip_vendored_and_build_paths(self):
        self.assertTrue(d.source_file('A/B.lean') and d.source_file('README.md') and d.source_file('docs/NOTICE'))
        for path in ['.lake/packages/mathlib/X.lean', 'lake-packages/m/X.lean', 'build/X.lean', 'lakefile.toml', 'manifest.json']:
            self.assertFalse(d.source_file(path))


if __name__ == '__main__':
    unittest.main()
