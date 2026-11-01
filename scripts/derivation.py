"""Derivation report (marker bos-derivation-v1): how close a submission is to a verified
submission of another author.

After ptweezy's DFT PRs #43, #44 and #46 (2026-10-22) copied HalitZiyaKARTAL's #41 with
only constants changed, the selector reports on each submission version (closest match,
changed files, constants-only, credit lines kept or missing) and holds a pass for
maintainer review only on positive evidence: at least 80% of the files are byte-identical
to a verified submission that is certainly another author's, and the other files differ
only in numeric literals and comments. A check that cannot be computed never holds.

The report reads Git trees and blobs through the API only. It never checks out or runs
submitted files, and the comment quotes no file content: only counts and a link."""
import base64
from fractions import Fraction
import json
import os
from pathlib import PurePosixPath
import re
import urllib.error
import urllib.request

import submissions as s

MARKER = '<!-- bos-derivation-v1 '
CALLS = 60  # API reads for all reports of one selection scan (corpus reads are cached).
MAX_PAIRS = 12  # Changed files that one report reads and compares.
MAX_BLOB = 4_000_000  # Bytes per compared file (the DFT Merged2.lean is 1.8 MB, 2026-10-21).
MAX_FILES = 5000  # Source files of one submission.
HOLD_OVERLAP = Fraction(4, 5)
SITE = 'bigospeedrun/site'
SHA = re.compile('[0-9a-f]{40}')
CREDIT_FILES = ('README', 'NOTICE', 'AUTHORS', 'CREDITS', 'LICENSE', 'COPYING')
CREDIT = re.compile(r'(?i)\b(?:authors?|copyright|credits?|written\s+by|contributed\s+by|maintainers?|thanks?)\b'
                    r'|(?<![\w.@])@[A-Za-z0-9][A-Za-z0-9-]{0,38}\b')


class NotComputed(Exception):
    pass


class Defer(Exception):
    """The scan ran out of read budget before the report of a candidate that would run: select it at
    the next scan, so that a burst of copies (#43, #44 and #46 came within hours) cannot pass unreported."""


class Reader:
    """Cached GitHub API reads with one call budget for the whole scan."""

    def __init__(self, limit=CALLS):
        self.calls, self.limit, self.cache = 0, limit, {}

    def get(self, repo, path):
        key = (repo, path)
        if key not in self.cache:
            if self.calls >= self.limit:
                raise NotComputed('API budget used')
            self.calls += 1
            import pr_submissions as pr
            # The constant origin is the only destination of the token; the opener drops it on any
            # redirect to another host.
            req = urllib.request.Request('https://api.github.com/repos/' + repo + '/' + path,
                                         headers={'Authorization': 'Bearer ' + os.environ['GH_TOKEN'],
                                                  'Accept': 'application/vnd.github+json',
                                                  'X-GitHub-Api-Version': '2022-11-28'})
            self.cache[key] = s.github_read_retry(req, pr.github_opener().open, json.load, path)
        return self.cache[key]

    def blob(self, repo, sha):
        obj = self.get(repo, f'git/blobs/{sha}')
        if obj.get('encoding') != 'base64':
            raise NotComputed('unexpected blob encoding')
        import pr_submissions as pr
        raw = base64.b64decode(obj['content'], validate=False)
        if pr.blob_sha(raw) != sha:
            raise NotComputed('blob hash mismatch')
        return raw


def source_file(path):
    """Lean sources and credit files count; build output, vendored packages and dot folders do not."""
    parts = PurePosixPath(path).parts
    if not parts or any(p.startswith('.') or p in ('lake-packages', 'build') for p in parts):
        return False
    return path.endswith('.lean') or parts[-1].upper().startswith(CREDIT_FILES)


def tree_files(listing, limit=MAX_FILES):
    """{relative path: (blob sha, size)} of the source files in a recursive tree listing."""
    if not isinstance(listing, dict) or listing.get('truncated') or not isinstance(listing.get('tree'), list):
        raise NotComputed('incomplete Git tree')
    files = {}
    for e in listing['tree']:
        path = e.get('path')
        if e.get('type') == 'blob' and isinstance(path, str) and source_file(path) and SHA.fullmatch(str(e.get('sha'))) and type(e.get('size')) is int:
            files[path] = (e['sha'], e['size'])
    if len(files) > limit:
        raise NotComputed('too many files')
    return files


TOKEN = re.compile(r'0[xX][0-9a-fA-F_]+|0[bB][01_]+|0[oO][0-7_]+|[0-9][0-9_]*(?:\.[0-9]+)?(?:[eE][+-]?[0-9]+)?'
                   r"|[^\W\d][\w'!?]*|\S")
SPECIAL = re.compile(r'--|/-|"')
STRING = re.compile(r'"(?:[^"\\\n]|\\.)*"')
BLOCK = re.compile(r'/-|-/')


def lean_scan(text):
    """(code tokens with each numeric literal replaced by '#', comment lines).

    Line comments (--) and nested block comments (/- -/, also /-- and /-!) leave the code
    tokens and come back as lines, because author and credit lines live there."""
    code, comments, i, n = [], [], 0, len(text)

    def add(piece):
        code.extend('#' if tok[0].isdigit() else tok for tok in TOKEN.findall(piece))

    while i < n:
        m = SPECIAL.search(text, i)
        if not m:
            add(text[i:])
            break
        add(text[i:m.start()])
        if m.group() == '--':
            end = text.find('\n', m.end())
            end = n if end < 0 else end
            comments.append(text[m.end():end])
            i = end
        elif m.group() == '/-':
            depth, j = 1, m.end()
            while depth:
                b = BLOCK.search(text, j)
                if not b:
                    j = n
                    break
                depth += 1 if b.group() == '/-' else -1
                j = b.end()
            comments += text[m.end():j].split('\n')
            i = j
        else:
            string = STRING.match(text, m.start())
            code.append(string.group() if string else '"')
            i = string.end() if string else m.end()
    return code, comments


def credit_lines(rel, raw):
    text = raw.decode('utf-8', errors='replace')
    if rel.endswith('.lean'):
        tokens, lines = lean_scan(text)
    else:
        tokens, lines = None, text.split('\n')
    found = [' '.join(line.split()) for line in lines if CREDIT.search(line)]
    return tokens, [line for line in found if line]


def corpus(reader, problem):
    """Verified submissions of the problem: [(key, url, (kind, folder name or login or None), files, repo)].

    The site's data/direct-submissions.json at its main commit lists every final Lean Verified
    outcome. A PR folder is read from verifier main in one tree; an issue source from its pinned
    repository commit. An issue source that cannot be read any more (a deleted repository) is skipped."""
    site = reader.get(SITE, 'commits/main')['sha']
    if not SHA.fullmatch(site):
        raise NotComputed('invalid site commit')
    meta = reader.get(SITE, f'contents/data/direct-submissions.json?ref={site}')
    states = json.loads(reader.blob(SITE, meta['sha']))['final_states']
    # A withdrawn submission is not a source (site data/direct-notes.json, 'withdrawn'; its folder stays in
    # main). #43/#44/#46 were copies of #41, so #91 by #41's author read as closest to #43 (2026-11-01).
    notes = reader.get(SITE, f'contents/data/direct-notes.json?ref={site}')
    withdrawn = set(json.loads(reader.blob(SITE, notes['sha'])).get('withdrawn') or {})
    # An Other bounds row has no board file: its issue authors stay unknown (reported, never held).
    board = {'records': []} if problem in s.OTHER else json.loads(s.site_snapshot(problem)[1])
    authors = {}
    for row in board['records']:
        names = row.get('authors') or []
        if row['id'].startswith('direct-issue-') and len(names) == 1 and isinstance(names[0].get('name'), str):
            authors[row['id']] = names[0]['name'].lower()
    found, seen = [], set()
    folders = None
    for state in states.values():
        sub = state.get('submission') or {}
        key = state.get('key')
        if state.get('decision') != 'lean-verified' or sub.get('problem') != problem or not isinstance(key, str) or key in withdrawn:
            continue
        source = (sub.get('repo_url'), sub.get('commit'), sub.get('source_subdir'))
        if source in seen:
            continue
        seen.add(source)
        match = re.fullmatch(r'direct-(issue|pr)-([1-9][0-9]*)', key)
        if not match or not SHA.fullmatch(str(sub.get('commit'))):
            continue
        if match[1] == 'pr':
            folder = sub.get('source_subdir') or ''
            if not re.fullmatch(rf'submissions/{re.escape(problem)}/[a-z0-9][a-z0-9-]{{0,79}}', folder):
                continue
            if folders is None:
                head = reader.get(s.REPOSITORY, 'git/refs/heads/main')['object']['sha']
                if not SHA.fullmatch(head):
                    raise NotComputed('invalid verifier commit')
                folders = tree_files(reader.get(s.REPOSITORY, f'git/trees/{head}:submissions/{problem}?recursive=1'), 100_000)
            name = folder.rsplit('/', 1)[1]
            files = {rel[len(name) + 1:]: v for rel, v in folders.items() if rel.startswith(name + '/')}
            if not files:
                continue
            # A folder name is the PR author's lowercase login, a hyphen and a suffix.
            found.append((key, f'https://github.com/{s.REPOSITORY}/pull/{match[2]}', ('folder', name), files, s.REPOSITORY))
        else:
            repo = str(sub.get('repo_url', '')).removeprefix('https://github.com/')
            if not re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_.-]{0,99}/[A-Za-z0-9][A-Za-z0-9_.-]{0,99}', repo):
                continue
            try:
                files = tree_files(reader.get(repo, f"git/trees/{sub['commit']}?recursive=1"))
            except urllib.error.HTTPError as error:
                error.close()
                continue
            author = authors.get(key)
            if author is None:
                # No board row names the submitter (an Other bounds row has no board file): the issue does
                # (#54, 2026-10-24: its closest source #49 had an unknown author, so it could not hold).
                try:
                    login = (reader.get(s.REPOSITORY, f'issues/{match[2]}').get('user') or {}).get('login')
                except NotComputed:
                    raise
                except Exception:
                    login = None  # An unreadable issue leaves the author unknown: reported, never held.
                author = login.lower() if isinstance(login, str) and re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9-]{0,38}', login) else None
            found.append((key, f'https://github.com/{s.REPOSITORY}/issues/{match[2]}', ('login', author), files, repo))
    return found


def other_author(author, login):
    """True when the entry is certainly another author's work, False when it may be the candidate's own,
    None when its author is unknown (it can be reported, but it never holds)."""
    kind, value = author
    if kind == 'folder':
        return not value.startswith(login + '-')
    return None if value is None else value != login


def pair(cand, pred):
    """Match files: byte-identical blobs first (any path), then the same path, then a unique file name.
    Returns (identical count, changed [(candidate path, earlier path)], added paths, removed paths)."""
    by_sha = {}
    for rel in sorted(pred):
        by_sha.setdefault(pred[rel][0], []).append(rel)
    used, rest_c, identical = set(), [], 0
    for rel in sorted(cand):
        options = [p for p in by_sha.get(cand[rel][0], []) if p not in used]
        if options:
            used.add(rel if rel in options else options[0])
            identical += 1
        else:
            rest_c.append(rel)
    rest_p = [p for p in sorted(pred) if p not in used]
    changed = [(c, c) for c in rest_c if c in rest_p]
    done = {c for c, _ in changed}
    rest_c = [c for c in rest_c if c not in done]
    rest_p = [p for p in rest_p if p not in done]
    names_c, names_p = {}, {}
    for rel in rest_c:
        names_c.setdefault(PurePosixPath(rel).name, []).append(rel)
    for rel in rest_p:
        names_p.setdefault(PurePosixPath(rel).name, []).append(rel)
    for name, rels in sorted(names_c.items()):
        if len(rels) == 1 and len(names_p.get(name, [])) == 1:
            changed.append((rels[0], names_p[name][0]))
    added = [c for c in rest_c if c not in {x for x, _ in changed}]
    removed = [p for p in rest_p if p not in {y for _, y in changed}]
    return identical, changed, added, removed


def compute(reader, problem, login, self_key, cand, cand_repo):
    """The report object; any read failure or cap gives status not_computed and no hold."""
    login = login.lower()
    if not cand:
        return {'status': 'not_computed', 'reason': 'no source files found', 'hold': False}
    best = None
    for key, url, author, files, repo in corpus(reader, problem):
        other = other_author(author, login)
        if key == self_key or other is False:
            continue
        shas = {sha for sha, _ in files.values()}
        identical = sum(1 for sha, _ in cand.values() if sha in shas)
        rank = (identical, other is True, -len(files))
        if identical and (best is None or rank > best[0]):
            best = (rank, key, url, files, repo, other)
    if best is None:
        return {'status': 'no_match', 'candidate_files': len(cand), 'hold': False}
    _, key, url, pred, pred_repo, other = best
    identical, changed, added, removed = pair(cand, pred)
    report = {'status': 'computed', 'closest': {'key': key, 'url': url, 'files': len(pred), 'author_known': other is True},
              'candidate_files': len(cand), 'identical': identical, 'changed': len(changed),
              'added': len(added), 'removed': len(removed), 'constants_only': None, 'credit': None,
              'credit_lines': None, 'hold': False}
    if len(changed) > MAX_PAIRS or any(cand[c][1] > MAX_BLOB or pred[p][1] > MAX_BLOB for c, p in changed):
        report['reason'] = 'too many or too large changed files to compare'
        return report
    same_code, before, kept, new = True, 0, 0, 0
    for c, p in changed:
        tokens_c, credit_c = credit_lines(c, reader.blob(cand_repo, cand[c][0]))
        tokens_p, credit_p = credit_lines(p, reader.blob(pred_repo, pred[p][0]))
        # A README, NOTICE or other credit file counts for the credit lines only; only Lean code decides
        # constants-only (#54: a changed README made a constants-only change of #49 look like new code).
        if (tokens_c is None) != (tokens_p is None) or (tokens_c is not None and tokens_c != tokens_p):
            same_code = False
        remaining = list(credit_c)
        before += len(credit_p)
        for line in credit_p:
            if line in remaining:
                remaining.remove(line)
                kept += 1
        new += len(remaining)
    missing = before - kept
    report['constants_only'] = same_code and not added and not removed
    report['credit_lines'] = {'earlier': before, 'kept': kept, 'missing': missing, 'new': new}
    report['credit'] = 'kept' if not missing else 'replaced' if new else 'removed'
    # The credit result is reported only: #43 and #44 kept every credit line of #41 in the files, but their
    # rows named the new submitter (probe 2026-10-23).
    report['hold'] = bool(other is True and report['constants_only'] and Fraction(identical, len(cand)) >= HOLD_OVERLAP)
    return report


def issue_files(reader, submission):
    repo = submission['repo_url'].removeprefix('https://github.com/')
    return tree_files(reader.get(repo, f"git/trees/{submission['commit']}?recursive=1")), repo


def pr_files(records, folder):
    """Candidate files from the PR layout records (paths already validated by inspect_pr)."""
    return {r['path'][len(folder) + 1:]: (r['sha'], r['size']) for r in records
            if source_file(r['path'][len(folder) + 1:])}


def safe_report(reader, problem, login, self_key, files, defer=False):
    """compute() that never raises: a failure gives a not_computed report without a hold.

    With defer (a candidate that would start a run), a used-up budget raises Defer instead, unless
    the report had the whole budget of a fresh scan: then it is not_computed, so that one oversized
    submission cannot wait forever."""
    fresh = reader.calls == 0
    try:
        cand, repo = files()
        return compute(reader, problem, login, self_key, cand, repo)
    except NotComputed as error:
        if defer and not fresh and str(error) == 'API budget used':
            raise Defer() from None
        reason = str(error)  # A fixed message of this module.
    except s.ScanLimit:
        if defer:
            raise Defer() from None
        reason = 'API budget used'
    except Exception:  # Never block or hold a submission because the report failed.
        reason = 'a read failed'
    return {'status': 'not_computed', 'reason': reason, 'hold': False}


def percent(part, whole):
    return f'{(100 * part) // whole}%' if whole else '0%'


def comment(number, version, report, route):
    item = 'PR' if route == 'pull_request' else 'issue'
    body = f'{MARKER}{number} {version} -->\nDerivation report for this version. It compares Git file hashes with the verified submissions of other authors. It does not judge the proof.\n\n'
    if report['status'] == 'not_computed':
        return body + f"Not computed: {report.get('reason', 'unknown')}. This does not hold the submission."
    if report['status'] == 'no_match':
        return body + 'No verified submission of another author has a file identical to a file of this version.'
    closest = report['closest']
    who = 'of another author' if closest.get('author_known') else 'with an unknown author (it cannot hold this version)'
    body += (f"Closest verified submission {who}: [{closest['key']}]({closest['url']}). "
             f"{report['identical']} of {report['candidate_files']} source files of this version are identical to its files "
             f"({percent(report['identical'], report['candidate_files'])}).\n"
             f"Against it: {report['changed']} changed, {report['added']} added, {report['removed']} removed.\n")
    if report['constants_only'] is None:
        body += f"Constants-only and credit checks: not computed ({report.get('reason', 'unknown')}).\n"
    else:
        lines = report['credit_lines']
        body += ('Only numeric constants changed in the code: ' + ('yes' if report['constants_only'] else 'no') + '.\n'
                 f"Credit lines (author, copyright, @handle) in the changed files: {lines['earlier']} in the earlier submission, "
                 f"{lines['kept']} kept, {lines['missing']} missing, {lines['new']} new.\n")
    if report['hold']:
        body += (f'\nHold: this version changes only numeric constants of another author\'s verified submission. The proof check still runs, but a pass does not merge or close this {item} and does not '
                 f'list it as Lean Verified until a maintainer reviews the credit. If this work builds on the earlier submission, '
                 f'keep its credit lines and name it in this {item}; a new version gets a new report.')
    return body


def reported(number, version, comments):
    marker = f'{MARKER}{number} {version} -->'
    return any(s.is_bot(c) and (c.get('body') or '').startswith(marker) for c in comments)


def safe_post(number, version, report, route, comments):
    """post() that never raises: a failed comment must not stop the selection."""
    try:
        post(number, version, report, route, comments)
    except Exception as error:
        print(f'Derivation report comment on #{int(number)} failed: {type(error).__name__}', flush=True)


def post(number, version, report, route, comments):
    """One report comment per version. comments is the first page that the selector already read."""
    if reported(number, version, comments):
        return
    body = comment(number, version, report, route)
    if len(comments) < 100:
        s.api(f'issues/{number}/comments', {'body': body})
    else:
        s.comment_once(number, body, key=f'{MARKER}{number} {version} -->')
