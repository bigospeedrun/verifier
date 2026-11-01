#!/usr/bin/env python3
"""Trusted issue parser and report publisher. Issue text is data, never code."""
import argparse
from fractions import Fraction
from functools import lru_cache
import hashlib
import json
import os
from pathlib import Path
import re
import urllib.request
import urllib.error
from http.client import IncompleteRead
import time
from datetime import datetime, timezone
from verdicts import admission, compile_error_comment, deterministic_setup_failure, reason_line

ROOT = Path(__file__).resolve().parents[1]
REPOSITORY = 'bigospeedrun/verifier'
TITLE = '[Lean submission]'
MARKER = '<!-- bos-direct-v1 '
FIELDS = {'schema_version', 'problem', 'bound', 'repo_url', 'commit', 'authors'}


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=True)


def submission_hash(value):
    return hashlib.sha256(canonical(validate_submission(value)).encode()).hexdigest()


def validate_submission(value):
    if not isinstance(value, dict) or not FIELDS <= set(value) or set(value) - FIELDS - {'entrypoint', 'source_subdir'} or type(value['schema_version']) is not int or value['schema_version'] != 1:
        raise ValueError('Expected schema_version, problem, bound, repo_url, commit, authors only')
    profiles = json.loads((ROOT / 'profiles/direct.json').read_text())
    if not isinstance(value['problem'], str) or value['problem'] not in profiles:
        raise ValueError('Supported problems: ' + ', '.join(p for p in profiles if p not in CLOSED))
    # At most 40 digits per integer (Nil, 2026-10-21: a reduced 3SUM bound needed 19, issue #35).
    if not isinstance(value['bound'], str) or not re.fullmatch(r'(?:0|[1-9][0-9]{0,39})(?:/[1-9][0-9]{0,39})?', value['bound']):
        raise ValueError('bound must be an integer or a fraction p/q (no decimals), with at most 40 digits in each')
    bound = Fraction(value['bound'])
    if not 0 <= bound <= Fraction(profiles[value['problem']]['maximum']):
        raise ValueError('bound is outside the problem range')
    if not isinstance(value['repo_url'], str) or not re.fullmatch(r'https://github\.com/[A-Za-z0-9][A-Za-z0-9_.-]{0,99}/[A-Za-z0-9][A-Za-z0-9_.-]{0,99}', value['repo_url']):
        raise ValueError('repo_url must be a public GitHub repository URL without query or credentials')
    if not isinstance(value['commit'], str) or not re.fullmatch('[0-9a-f]{40}', value['commit']):
        raise ValueError('commit must be a full lowercase Git SHA')
    entrypoint = value.get('entrypoint', 'Race.bound')
    if entrypoint not in ['Race.bound', 'dft233']:
        raise ValueError('Unknown entrypoint')
    if entrypoint == 'dft233' and (value['problem'] != 'dft' or bound != Fraction('7547360/10000000000')):
        raise ValueError('dft233 supports only its fixed DFT saving')
    if 'source_subdir' in value and not re.fullmatch(r'submissions/(dft|3sum|apsp)/[a-z0-9][a-z0-9-]{0,79}', value['source_subdir']):
        raise ValueError('Invalid PR source folder')
    if 'source_subdir' in value and value['source_subdir'].split('/')[1] != value['problem']:
        raise ValueError('PR source folder problem mismatch')
    authors = value['authors']
    if not isinstance(authors, list) or not 0 <= len(authors) <= 30 or any(not isinstance(x, str) or not x.strip() or len(x) > 120 or any(ord(c) < 32 for c in x) for x in authors):
        raise ValueError('authors must contain 1 to 30 names, at most 120 characters each')
    result = dict(value, bound=str(bound))
    if entrypoint == 'Race.bound':
        result.pop('entrypoint', None)
    return result


FORM_FIELDS = ['Problem', 'Repository URL', 'Commit SHA', 'Bound']
MODEL_IDS = {'dft': 'exact-dft/uniform-exact-arithmetic', '3sum': '3sum/word-ram', 'apsp': 'apsp/word-ram',
             'average-sensitivity': 'other/average-sensitivity', 'catalan': 'other/catalan',
             'subset-sum': 'subset-sum/randomized-word-ram'}
# Other bounds rows with a trusted statement: the record gate reads the row, not a board file.
OTHER = {'average-sensitivity', 'catalan'}
# A profile whose proof route is not open yet: selection skips it, and only the maintainer smoke runs
# it (smoke.py). Opening is a reviewed change that removes the problem from this set. Average
# sensitivity opened on 2026-10-23 after its smoke (run 39943626205, issue #48) passed. Catalan opened on
# 2026-10-27 after its split-build smoke (run 40497685416, issue #68) passed. Subset Sum (2026-10-27) waits
# for a proof on its profile to smoke with.
CLOSED = {'subset-sum'}


def parse_body(body):
    """Exact GitHub issue form headings and one-line values; no prose or JSON."""
    if not isinstance(body, str) or len(body.encode('utf-8')) > 4096:
        raise ValueError('Expected the four structured issue form fields')
    pattern = r'\A### Problem\n\n([^\n]+)\n\n### Repository URL\n\n([^\n]+)\n\n### Commit SHA\n\n([^\n]+)\n\n### Bound\n\n([^\n]+)\n?\Z'
    match = re.fullmatch(pattern, body.replace('\r\n', '\n'))
    if not match:
        raise ValueError('Unexpected, duplicate, missing, or multiline issue field')
    problem, repo, commit, bound = match.groups()
    value = validate_submission({'schema_version': 1, 'problem': problem, 'repo_url': repo,
                                 'commit': commit, 'bound': bound, 'authors': []})
    if value['bound'] != bound:
        raise ValueError('Bound must be a reduced exact rational string')
    return value


def body_hash(body):
    return hashlib.sha256(body.encode('utf-8')).hexdigest()


# Where a profile's proof check runs. 'github-split': two hosted jobs, a build job and a check job
# (submission-check.yml, docs/execution.md). The selection gives its matrix entry split: true.
RUNNERS = {'github', 'github-split'}


def selected_profile(submission):
    if submission.get('entrypoint') == 'dft233':
        profile = json.loads((ROOT / 'profiles/dft233.json').read_text())
    else:
        profile = json.loads((ROOT / 'profiles/direct.json').read_text())[submission['problem']]
    if profile.get('runner', 'github') not in RUNNERS:
        raise ValueError('Unknown profile runner')
    return profile


def runner(submission):
    return selected_profile(submission).get('runner', 'github')


def matrix_entry(number, login, route, submission):
    entry = {'issue_number': number, 'login': login, 'route': route}
    if route == 'issue' and runner(submission) == 'github-split':
        entry['split'] = True
    return entry


def resolve_request(request):
    submission = validate_submission(request['direct_submission'])
    profile = selected_profile(submission)
    if request != make_request(submission):
        raise ValueError('Direct request fields must match the trusted problem profile')
    actual = hashlib.sha256((ROOT / profile['challenge_file']).read_bytes()).hexdigest()
    if actual != profile['challenge_sha256']:
        raise ValueError('Trusted statement bytes changed')
    return profile, profile['theorem_names']


def make_request(submission):
    submission = validate_submission(submission)
    profile = selected_profile(submission)
    request = {'direct_submission': submission, 'repo_url': submission['repo_url'], 'commit': submission['commit'],
            'challenge_file': profile['challenge_file'], 'theorem_names': ','.join(profile['theorem_names']), 'lean_toolchain': profile['lean_toolchain']}
    if 'source_subdir' in submission:
        request['source_subdir'] = submission['source_subdir']
    return request


def challenge_source(submission):
    submission = validate_submission(submission)
    request = make_request(submission)
    profile, _ = resolve_request(request)
    base = (ROOT / profile['challenge_file']).read_text()
    if submission.get('entrypoint') == 'dft233':
        return base
    n, d = Fraction(submission['bound']).as_integer_ratio()
    if submission['problem'] == 'dft':
        target = f'''open OAI.PowerSaving Filter Asymptotics

theorem Race.bound : ∃ order solve W, DFTProgram order solve W ∧
    (fun n : ℕ => (W n : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) * (Real.log (n : ℝ)) ^ (1 - ({n} : ℝ) / {d})) := by
  sorry
'''
    elif submission['problem'] == 'average-sensitivity':
        target = f'theorem Race.bound : BigOSpeedrun.AverageSensitivity.Bound (({n} : ℚ) / {d}) := by\n  sorry\n'
    elif submission['problem'] == 'catalan':
        target = f'theorem Race.bound : BigOSpeedrun.Catalan.Bound (({n} : ℚ) / {d}) := by\n  sorry\n'
    elif submission['problem'] == 'subset-sum':
        target = f'theorem Race.bound : BigOSpeedrun.SubsetSum.SolvedInTime (({n} : Rat) / {d}) := by\n  sorry\n'
    else:
        problem = 'ThreeSum' if submission['problem'] == '3sum' else 'APSP'
        target = f'theorem Race.bound : EndStatement.{problem}.SolvedInTime (({n} : Rat) / {d}) := by\n  sorry\n'
    return base + '\n-- Big O Speedrun exact-bound target; generated from validated integers.\n' + target


SCAN_BUDGET = None


class ScanLimit(RuntimeError):
    pass


def scan_check(path=''):
    if SCAN_BUDGET is None or path.startswith(('git/commits', 'git/refs')):
        return
    if SCAN_BUDGET['calls'] >= 400 or time.monotonic() >= SCAN_BUDGET['deadline']:
        raise ScanLimit('Selection API/time budget exhausted; saved cursor will resume')
    SCAN_BUDGET['calls'] += 1


def scan_timeout():
    return 15 if SCAN_BUDGET is not None else 60


def github_read_retry(req, open_request, read_response, path):
    """Retry GET transport failures only; never replay a possibly committed write."""
    for attempt in range(3):
        scan_check(path)
        try:
            with open_request(req, timeout=scan_timeout()) as response:
                return read_response(response)
        except urllib.error.HTTPError as exc:
            retryable = 500 <= exc.code < 600
            exc.close()
            if not retryable or req.get_method() != 'GET' or attempt == 2:
                raise
        except (urllib.error.URLError, ConnectionError, TimeoutError, IncompleteRead):
            if req.get_method() != 'GET' or attempt == 2:
                raise
        time.sleep(2 ** attempt)


def api(path, data=None, method=None):
    # This constant origin is the only destination for this scoped token.
    req = urllib.request.Request('https://api.github.com/repos/' + REPOSITORY + '/' + path,
          data=None if data is None else json.dumps(data).encode(), method=method,
          headers={'Authorization': 'Bearer ' + os.environ['GH_TOKEN'], 'Accept': 'application/vnd.github+json',
                   'X-GitHub-Api-Version': '2022-11-28', 'Content-Type': 'application/json'})
    return github_read_retry(req, urllib.request.urlopen, json.load, path)


def pages(path):
    page = 1
    while True:
        batch = api(path + ('&' if '?' in path else '?') + f'per_page=100&page={page}')
        yield from batch
        if len(batch) < 100:
            return
        page += 1


def marker_for(number, digest, raw_digest):
    return MARKER + str(number) + ' ' + digest + ' ' + raw_digest + ' -->'


def is_bot(comment):
    return comment.get('user', {}).get('login') == 'github-actions[bot]' and comment.get('user', {}).get('type') == 'Bot'


RECEIPT_LINK = re.compile(r'\]\((https://github\.com/[^)\s]+/actions/runs/[0-9]+/artifacts/[0-9]+)\)')


def comment_once(number, body, call=None, key=None):
    """Post a result comment unless a bot comment already links the same receipt artifact
    (or, with a key, already contains that key), and keep only the oldest copy after a race.
    GitHub can start two publisher watchers for one verify run (a run that goes queued and
    back to in_progress sends a second event); both see the same checkpoint (2026-10-20)."""
    call = call or api
    links = [key] if key else RECEIPT_LINK.findall(body)
    if links:
        for page in range(1, 11):
            comments = call(f'issues/{number}/comments?per_page=100&page={page}')
            if not isinstance(comments, list):
                raise ValueError('Unexpected comment list')
            if any(isinstance(c, dict) and is_bot(c) and links[0] in (c.get('body') or '') for c in comments):
                return False
            if len(comments) < 100:
                break
        else:
            raise ValueError('Comment lookup exceeds bounded scan; review required')
    posted = call(f'issues/{number}/comments', {'body': body})
    if links and isinstance(posted, dict) and posted.get('id'):
        try:
            drop_newer_copy(number, links[0], posted['id'], call)
        except Exception as error:  # Best effort: the comment is posted; a failed cleanup leaves two copies.
            print('Duplicate comment cleanup failed: ' + type(error).__name__, flush=True)
    return True


def drop_newer_copy(number, key, posted_id, call):
    """Two publisher watchers can both pass the check above before either posts (test issue #48,
    2026-10-23: the Lean checkpoint comment twice, one second apart). The oldest bot comment with
    the key stays; a watcher whose own copy is newer deletes it."""
    same = []
    for page in range(1, 11):
        comments = call(f'issues/{number}/comments?per_page=100&page={page}')
        same += [c for c in comments if isinstance(c, dict) and is_bot(c) and key in (c.get('body') or '')]
        if len(comments) < 100:
            break
    ids = sorted(c['id'] for c in same if isinstance(c.get('id'), int))
    if len(ids) > 1 and posted_id in ids and posted_id != ids[0]:
        try:
            call(f'issues/comments/{int(posted_id)}', method='DELETE')
        except ValueError:
            pass  # 204 No Content: the delete succeeded; there is no JSON body to read.


def issue_input(issue):
    if 'pull_request' in issue or issue.get('state') != 'open' or not issue.get('title', '').startswith(TITLE):
        return None
    return parse_body(issue.get('body'))


def issue_request(issue, submission):
    login = issue['user']['login']
    if not re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9-]{0,38}(?:\[bot\])?', login):
        raise ValueError('Invalid authenticated issue login')
    return {'inputs': make_request(submission), 'submission': submission,
            'submission_sha256': submission_hash(submission), 'issue_body_sha256': body_hash(issue['body']),
            'issue_submitter_login': login, 'issue_number': issue['number'],
            'issue_url': f"https://github.com/{REPOSITORY}/issues/{issue['number']}",
            'issue_created_at': issue['created_at'], 'issue_updated_at': issue['updated_at'],
            'source_published_at': None, 'test_only': False}


@lru_cache(maxsize=3)
def site_snapshot(problem):
    import base64
    def read(path):
        req = urllib.request.Request('https://api.github.com/repos/bigospeedrun/site/' + path,
                                     headers={'Accept': 'application/vnd.github+json',
                                              'Authorization': 'Bearer ' + os.environ['GH_TOKEN']})
        return github_read_retry(req, urllib.request.urlopen, json.load, path)
    sha = read('commits/main')['sha']
    if not re.fullmatch('[0-9a-f]{40}', sha):
        raise ValueError('Invalid site commit')
    slug = 'exact-dft' if problem == 'dft' else problem
    obj = read(f'contents/data/{slug}.json?ref={sha}')
    raw = base64.b64decode(obj['content'], validate=False)
    return sha, raw


def open_rank(problem):
    """Second key of an open endpoint: below an attained score on dft (max wins), above it
    on the exponent boards (min wins), so an attained tie always leads."""
    return -1 if problem == 'dft' else 1


def site_files(paths):
    """(site main commit, {path: bytes or None}) read at one resolved commit; None for a missing file."""
    import base64
    def read(path):
        req = urllib.request.Request('https://api.github.com/repos/bigospeedrun/site/' + path,
                                     headers={'Accept': 'application/vnd.github+json',
                                              'Authorization': 'Bearer ' + os.environ['GH_TOKEN']})
        return github_read_retry(req, urllib.request.urlopen, json.load, path)
    sha = read('commits/main')['sha']
    if not re.fullmatch('[0-9a-f]{40}', sha):
        raise ValueError('Invalid site commit')
    found = {}
    for path in paths:
        try:
            obj = read(f'contents/{path}?ref={sha}')
            if not obj.get('content'):
                # The contents API leaves out the content of a file over 1 MB; its Git blob has it.
                obj = read(f"git/blobs/{obj['sha']}")
            found[path] = base64.b64decode(obj['content'], validate=False)
        except urllib.error.HTTPError as error:
            if error.code != 404:
                raise
            found[path] = None
    return sha, found


def exact_value(text):
    if not isinstance(text, str) or not re.fullmatch(r'(?:0|[1-9][0-9]{0,39})(?:/[1-9][0-9]{0,39}|\.[0-9]{1,40})?', text):
        return None
    return Fraction(text)


def other_record(problem, issue_url):
    """The gate of an Other bounds row: its best Lean Verified claim (hand-listed, prove2.me or a direct
    submission), else the row's exact baseline. A lower coefficient is better on these rows."""
    rows, direct, prove2me = 'src/lib/other-bounds.json', 'data/direct-other.json', 'data/prove2me.json'
    sha, files = site_files([rows, direct, prove2me])
    family = next(f for f in json.loads(files[rows])['families'] if f['slug'] == problem)
    if family['direction'] != 'lower':
        raise ValueError('Other bounds direction mismatch')
    claims = list(family['claims'])
    for extra in [direct, prove2me]:
        if files[extra] is not None:
            claims += json.loads(files[extra]).get('boards', {}).get('other-' + problem, {}).get('claims', [])
    verified = [(exact_value(c.get('value')), c.get('handle')) for c in claims
                if c.get('evidence') == 'lean-verified' and c.get('url') != issue_url]
    verified = [(v, h) for v, h in verified if v is not None]
    if verified:
        best = min(v for v, _ in verified)
        leaders, any_lean = sorted(str(h) for v, h in verified if v == best), True
    else:
        baseline = family['baseline'].get('exactValue')
        best = exact_value(baseline)
        if best is None and baseline == '+\\infty':
            # No finite baseline (Catalan): every bound in the profile's range beats it, so the range's top gates.
            best = Fraction(json.loads((ROOT / 'profiles/direct.json').read_text())[problem]['maximum'])
        if best is None:
            raise ValueError('No Lean Verified claim or exact baseline; refuse to guess')
        leaders, any_lean = ['baseline'], False
    raw = b''.join(files[p] or b'' for p in [rows, direct, prove2me])
    return {'schema_version': 1, 'score': str(best), 'score_relation': 'attained', 'leader_ids': leaders,
            'any_lean_verified_at_bound': any_lean, 'problem_id': MODEL_IDS[problem], 'site_commit': sha,
            'data_sha256': hashlib.sha256(raw).hexdigest(),
            'checked_at': datetime.now(timezone.utc).isoformat().replace('+00:00', 'Z')}


def current_record(problem, issue_url):
    """Read the board from a resolved immutable site commit, never the issue repo.

    The gate is the best Lean Verified row of the board (Nil ruling 2026-10-20): a Claimed
    or Human Verified row never blocks a proof run. With no Lean Verified row, the classical
    baseline is the gate, so a bound must at least match it."""
    if problem in OTHER:
        return other_record(problem, issue_url)
    sha, raw = site_snapshot(problem)
    data = json.loads(raw)
    if data['problem_id'] != MODEL_IDS[problem]:
        raise ValueError('Current record model mismatch')
    def lean_verified(row):
        metadata = data['record_metadata'].get(row['id'], {})
        rerun = row.get('rerun_status') or {}
        return metadata.get('site_tier') == 'verified' and rerun.get('state') == 'passed' and bool(rerun.get('receipt_path'))
    records = [r for r in data['records'] if r.get('submission_url') != issue_url
               and r['id'] != 'classical-baseline'
               and not data['record_metadata'].get(r['id'], {}).get('reproduction_of')
               and lean_verified(r)]
    if not records:
        records = [r for r in data['records'] if r['id'] == 'classical-baseline']
    if not records:
        raise ValueError('No Lean Verified record or baseline; refuse to guess')
    # Mirrors the site comparison (site data/direct_import.py open_rank): exact score
    # first, and an open endpoint is weaker than an attained value at the same score.
    key = lambda r: (Fraction(r['score']), open_rank(problem) if r.get('score_relation') == 'strict-upper-bound' else 0)
    best = (max if problem == 'dft' else min)(records, key=key)
    leaders = [r for r in records if key(r) == key(best)]
    return {'schema_version': 1, 'score': str(Fraction(best['score'])),
            'score_relation': best.get('score_relation', 'attained'),
            'leader_ids': sorted(r['id'] for r in leaders),
            'any_lean_verified_at_bound': any(lean_verified(r) for r in leaders),
            'problem_id': data['problem_id'], 'site_commit': sha,
            'data_sha256': hashlib.sha256(raw).hexdigest(),
            'checked_at': datetime.now(timezone.utc).isoformat().replace('+00:00', 'Z')}


def qualifies_for_run(submission, record):
    candidate = (Fraction(submission['bound']), 0)
    current = (Fraction(record['score']), open_rank(submission['problem']) if record['score_relation'] == 'strict-upper-bound' else 0)
    if candidate == current:
        # A tie with a Lean Verified leader starts no run; a tie with the baseline (no Lean
        # Verified row yet) does. Missing evidence metadata cannot authorize a costly run.
        # Never relabel another author's record.
        return record.get('any_lean_verified_at_bound') is False
    return candidate > current if submission['problem'] == 'dft' else candidate < current


# The race page of each problem on bigospeedrun.com (Lead, 2026-10-25, BOS Growth: GitHub visitors rarely reach the
# site). A final result names it in one line; the site routes are /<slug> for Big O boards, /other/<slug> otherwise.
BOARDS = {'dft': ('Exact discrete Fourier transform', 'exact-dft'), '3sum': ('3SUM', '3sum'),
          'apsp': ('All-pairs shortest paths', 'apsp'), 'average-sensitivity': ('Average sensitivity', 'other/average-sensitivity'),
          'catalan': ("Catalan's constant", 'other/catalan'), 'subset-sum': ('Subset Sum', 'subset-sum')}


def board_line(problem):
    """One neutral line that links the race page of a problem, the same for every outcome (Lead, 2026-10-25: a
    listing claim would be false until the next site refresh); '' for an unknown problem."""
    if problem not in BOARDS:
        return ''
    name, path = BOARDS[problem]
    return f'{name} board: https://bigospeedrun.com/{path}'


CLAIMED_TEXT = ('This submission is listed as Claimed; the bound does not qualify for a proof run. A run starts only for a '
                'bound that matches or beats the best Lean Verified result on its board, and that bar only gets higher, so '
                'this {item} now closes. It stays listed as Claimed. To submit a better bound, open a new {item}.')


def close_claimed(number, digest, item, problem=None):
    """One claimed-only report for this submission version, then close it as not planned: it would never run
    later, and the site keeps it listed as Claimed by this report's marker (Lead, 2026-10-23, after PR #52)."""
    marker = f'<!-- bos-claimed-v1 {number} {digest} -->'
    line = board_line(problem)
    comment_once(number, marker + '\n' + CLAIMED_TEXT.format(item=item) + ('\n\n' + line if line else ''), key=marker)
    api(f'issues/{number}', {'state': 'closed', 'state_reason': 'not_planned'}, method='PATCH')


def selection_outputs(selected):
    with open(os.environ['GITHUB_OUTPUT'], 'a') as out:
        out.write('selected=' + str(bool(selected)).lower() + '\n')
        out.write('matrix=' + canonical({'include': selected}) + '\n')


def select():
    global SCAN_BUDGET
    SCAN_BUDGET = {'calls': 0, 'deadline': time.monotonic() + 240}
    try:
        select_bounded()
    except ScanLimit:
        pass  # Incremental outputs and the cursor already preserve completed work.
    finally:
        SCAN_BUDGET = None


ACK = '<!-- bos-ack-v1 '
TEST_LABEL = 'test'
ACK_LIMIT = 30  # Newest open issues and PRs acknowledged per scan.
ACK_CALLS = 120  # The pass's own API cap and time cap: the selection after it keeps the rest of the budget.
ACK_SECONDS = 60


class AckLimit(RuntimeError):
    pass


def acknowledge():
    """Reply once to each open submission issue (per body version) and each open PR (per head) that
    has no bot reply for that version yet. It runs before the queue lease, so a submission gets an
    answer at the next scan even while another proof run holds the queue (issue #35, 2026-10-21: a
    form error left the issue without any reply for 10 h)."""
    import pr_submissions as pr
    budget = {'calls': 0, 'deadline': time.monotonic() + ACK_SECONDS}

    def call(path, data=None, method=None):
        if budget['calls'] >= ACK_CALLS or time.monotonic() >= budget['deadline']:
            raise AckLimit('acknowledgement budget used')
        budget['calls'] += 1
        return api(path, data, method)

    def bot_comments(number):
        """Bot comments of an item, oldest first, from at most 10 pages; None when the thread is longer."""
        found = []
        for page in range(1, 11):
            batch = call(f'issues/{number}/comments?per_page=100&page={page}')
            found += [c for c in batch if is_bot(c)]
            if len(batch) < 100:
                return found
        return None

    def reply(item):
        number = item['number']
        if 'pull_request' not in item and TEST_LABEL in [label.get('name') for label in item.get('labels') or [] if isinstance(label, dict)]:
            return  # A maintainer test issue (a label needs triage rights): the silent smoke posts nothing.
        if 'pull_request' in item:
            budget['calls'] += 1
            pull = pr.api(f'pulls/{number}')
            version, known = pull['head']['sha'], [pull['head']['sha']]
        elif item.get('title', '').startswith(TITLE):
            version = body_hash(item.get('body') or '')
            try:
                submission = issue_input(item)
            except ValueError as error:
                submission, known = error, []
            else:
                if submission is None:
                    return
                known = [submission_hash(submission)]
        else:
            return
        marker = ACK + str(number) + ' ' + version + ' -->'
        replies = bot_comments(number)
        # A thread longer than 10 pages: do not post (a reply could be on a later page).
        # A version that already has its acknowledgement, or a result or claimed reply, needs none.
        if replies is None or any(k in (c.get('body') or '') for c in replies for k in [marker, *known]):
            return
        if 'pull_request' in item:
            budget['calls'] += 3
            text = ('Received. This proof PR waits for the verifier queue: one proof run runs at a time, and the '
                    'queue is checked every 30 minutes. The result is posted here.' if pr.proof_candidate(pull) else
                    'Received. This PR changes no submissions/ folder, so it starts no proof run. A maintainer '
                    'reviews it and answers here.')
        elif isinstance(submission, dict) and submission['problem'] in CLOSED:
            text = ('Received, but proof submissions for this problem are not open yet. The maintainers will '
                    'announce when they are; this issue is checked again then.')
        elif isinstance(submission, ValueError):
            text = ('Received, but this submission cannot start a proof run: ' + str(submission) + '. Edit this '
                    'issue to fix the form; the edit starts a new check.')
        else:
            text = ('Received. The verifier checks submissions every 30 minutes and runs one proof at a time, '
                    'so this run can wait for the current one. The result is posted here.')
        posted = call(f'issues/{number}/comments', {'body': marker + '\n' + text})
        # Two runs can overlap (an issue event and the schedule). Keep only the oldest reply with this
        # marker: delete ours when an older one exists.
        replies = bot_comments(number) or []
        same = sorted((c for c in replies if (c.get('body') or '').startswith(marker)), key=lambda c: c['id'])
        if len(same) > 1 and posted.get('id') != same[0]['id'] and any(c['id'] == posted.get('id') for c in same):
            try:
                call(f'issues/comments/{int(posted["id"])}', method='DELETE')
            except ValueError:
                pass  # 204 No Content: the delete succeeded; there is no JSON body to read.

    for item in call(f'issues?state=open&sort=created&direction=desc&per_page={ACK_LIMIT}'):
        try:
            reply(item)
        except (AckLimit, ScanLimit):
            raise
        except Exception as error:
            # One failed item (a 403 on a PR comment, 2026-10-21 18:47Z) must not stop the replies to the others.
            print(f"Acknowledgement of #{int(item.get('number') or 0)} failed: {type(error).__name__}", flush=True)


RELEASE_CALLS = 40
RELEASE_ENTRIES = 20
REVIEW_LABEL = 'verification-needs-review'  # pr_submissions.add_review_label sets it on a hold


def remove_review_label(number, call):
    """A released hold no longer waits for review (Lead, 2026-10-24): remove its label. Already gone is fine."""
    try:
        call(f'issues/{number}/labels/{REVIEW_LABEL}', method='DELETE')
    except urllib.error.HTTPError as error:
        if error.code != 404:
            raise


def release():
    """Act on the lead's approvals of derivation holds: an entry in the site's data/review-decisions.json
    under derivations ({id, submission_sha256, decision: approved}) merges a held PR at its held head,
    or closes a held issue as completed. Only the bot's hold ping binds that digest to the held version
    (PR head or issue body), and the ping is posted only after the proof checks passed; an approval
    without a matching ping, or for a changed head or body, does nothing. The site lists the result at
    its next refresh (Lead, 2026-10-23: one entry releases the merge and the listing)."""
    import pr_submissions as pr
    budget = {'calls': 0, 'deadline': time.monotonic() + 30}

    def call(path, data=None, method=None):
        if budget['calls'] >= RELEASE_CALLS or time.monotonic() >= budget['deadline']:
            raise AckLimit('release budget used')
        budget['calls'] += 1
        return api(path, data, method)

    decisions = json.loads(pr.site_file('data/review-decisions.json'))
    approved = [d for d in decisions.get('derivations', []) if isinstance(d, dict) and d.get('decision') == 'approved']
    for entry in approved[-RELEASE_ENTRIES:]:
        match = re.fullmatch(r'direct-(issue|pr)-([1-9][0-9]{0,8})', str(entry.get('id')))
        digest = str(entry.get('submission_sha256'))
        if not match or not re.fullmatch('[0-9a-f]{64}', digest):
            continue
        number = int(match[2])
        try:
            item = call(f'issues/{number}')
            if ('pull_request' in item) != (match[1] == 'pr'):
                continue
            if item.get('state') != 'open':
                # A released item that still has the review label (a failed removal, or #56 before 2026-10-24).
                done = (item.get('pull_request') or {}).get('merged_at') if match[1] == 'pr' else item.get('state_reason') == 'completed'
                if done and REVIEW_LABEL in [label.get('name') for label in item.get('labels') or []]:
                    remove_review_label(number, call)
                continue
            prefix = f'{pr.HOLD_MARKER}{number} {digest} '
            # Every held version of this digest (an issue body edit that keeps the submission posts a second ping).
            versions = set()
            for page in range(1, 4):
                batch = call(f'issues/{number}/comments?per_page=100&page={page}')
                for c in batch:
                    found = re.match(r'([0-9a-f]{40}|[0-9a-f]{64}) -->', (c.get('body') or '')[len(prefix):]) if is_bot(c) and (c.get('body') or '').startswith(prefix) else None
                    if found:
                        versions.add(found[1])
                if len(batch) < 100:
                    break
            if not versions:
                continue
            if match[1] == 'pr':
                version = call(f'pulls/{number}')['head']['sha']
                if version not in versions:
                    continue
                # GitHub compares the head atomically; a moved head declines the merge.
                call(f'pulls/{number}/merge', {'sha': version, 'merge_method': 'squash'}, 'PUT')
                remove_review_label(number, call)
            else:
                if body_hash(item.get('body') or '') not in versions:
                    continue
                marker = f'<!-- bos-derivation-release-v1 {number} {digest} -->'
                try:
                    line = board_line(parse_body(item.get('body') or '')['problem'])
                except ValueError:
                    line = ''
                comment_once(number, marker + '\nA maintainer reviewed the credit and released this result. This issue now closes.'
                             + ('\n\n' + line if line else ''), call, key=marker)
                call(f'issues/{number}', {'state': 'closed', 'state_reason': 'completed'}, 'PATCH')
                remove_review_label(number, call)
        except AckLimit:
            raise
        except Exception as error:
            print(f'Release of #{number} failed: {type(error).__name__}', flush=True)


def select_bounded():
    """One trusted batch; resumable 40-candidate/4-minute scan, ten accounts."""
    import queue_lease
    import pr_submissions as pr
    selected, authors = [], set()
    selection_outputs(selected)
    try:
        acknowledge()
    except Exception as error:  # A non-critical pass: any error stops only the pass, never the selection.
        print('Acknowledgement pass stopped: ' + type(error).__name__, flush=True)
    try:
        release()
    except Exception as error:  # A non-critical pass, like the acknowledgement pass.
        print('Release pass stopped: ' + type(error).__name__, flush=True)
    import smoke
    lease = queue_lease.acquire(queue_lease.SMOKE_REF) if smoke.requested() else queue_lease.acquire()
    if lease is None:
        return
    import smoke
    if smoke.dispatch(lease):
        return
    Path('requests').mkdir(exist_ok=True)
    import derivation
    reader = derivation.Reader()  # One derivation call budget and cache for the whole scan.
    deadline = time.monotonic() + 240
    scanned = 0
    while scanned < 40 and len(selected) < 9 and time.monotonic() < deadline:
        page, offset = lease.state['page'], lease.state['offset']
        batch = api(f'issues?state=open&sort=created&direction=asc&per_page=50&page={page}')
        if offset >= len(batch):
            lease.state.update(page=1, offset=0)
            lease.save()
            break
        for index in range(offset, len(batch)):
            if scanned >= 40 or len(selected) >= 9 or time.monotonic() >= deadline:
                return
            issue = batch[index]
            # Persist after each bounded candidate, including invalid submissions.
            lease.state.update(page=page if index+1 < 50 else page+1, offset=(index+1) % 50)
            scanned += 1
            try:
                login = issue['user']['login'].lower()
                if login in authors:
                    continue
                # A maintainer test issue (a label needs triage rights) runs only by dispatch (smoke.py).
                if 'pull_request' not in issue and TEST_LABEL in [label.get('name') for label in issue.get('labels') or [] if isinstance(label, dict)]:
                    continue
                # One bounded comments page; do not walk attacker-sized threads.
                comments = api(f"issues/{issue['number']}/comments?per_page=100&page=1")
                if 'pull_request' in issue:
                    request = pr.select_candidate(issue, lease, reader, comments)
                    if request is None:
                        continue
                    route = 'pull_request'
                else:
                    try:
                        submission = issue_input(issue)
                    except ValueError:
                        continue
                    if submission is None or submission['problem'] in CLOSED:
                        continue
                    request = issue_request(issue, submission)
                    digest = request['submission_sha256']
                    if lease.admitted(queue_lease.admission_key(request)):
                        continue
                    record = current_record(submission['problem'], request['issue_url'])
                    qualifies = qualifies_for_run(submission, record)
                    if qualifies or not derivation.reported(issue['number'], digest, comments):
                        report = derivation.safe_report(reader, submission['problem'], login, f"direct-issue-{issue['number']}",
                                                        lambda: derivation.issue_files(reader, submission), defer=qualifies)
                        # A Claimed-only issue is re-checked at each scan: retry a report that ran out of budget.
                        if qualifies or report.get('reason') != 'API budget used':
                            derivation.safe_post(issue['number'], digest, report, 'issue', comments)
                        request['derivation'] = report
                    if not qualifies:
                        marker = f"<!-- bos-claimed-v1 {issue['number']} {digest} -->"
                        # The report and the close; also the close alone when an earlier close failed after
                        # its report (the issue is open here, so it is still not closed).
                        if not any(is_bot(c) and c.get('body', '').startswith(marker) for c in comments):
                            close_claimed(issue['number'], digest, 'issue', submission['problem'])
                        else:
                            api(f"issues/{issue['number']}", {'state': 'closed', 'state_reason': 'not_planned'}, method='PATCH')
                        continue
                    request['record_gate'] = record
                    route = 'issue'
                lease.reserve(queue_lease.admission_key(request))
                authors.add(login)
                Path(f"requests/{issue['number']}.json").write_text(canonical(request) + '\n')
                selected.append(matrix_entry(issue['number'], login, route, request.get('submission')))
                selection_outputs(selected)
            except derivation.Defer:
                # Not reserved: the next scan starts at this candidate with a fresh read budget.
                lease.state.update(page=page, offset=index)
                return
            finally:
                lease.save()
        if len(batch) < 50:
            lease.state.update(page=1, offset=0)
            lease.save()
            break


def materialize():
    number = os.environ['ISSUE_NUMBER']
    if not re.fullmatch('[1-9][0-9]*', number):
        raise ValueError('Invalid issue number')
    selected = json.loads(Path(f'requests/{number}.json').read_text())
    if selected['issue_number'] != int(number) or (selected.get('test_only') is not False and not __import__('smoke').active(selected)):
        raise ValueError('Issue identity mismatch or test fixture')
    Path('request').mkdir(exist_ok=True)
    Path('request/request.json').write_text(canonical(selected) + '\n')


def preflight():
    import queue_lease
    # Recheck just before setup/compilation in case a runner was queued or the
    # site's current record advanced after batch selection.
    selected = json.loads(Path('request/request.json').read_text())
    smoke_test = __import__('smoke').active(selected)
    queue_lease.assert_owner(queue_lease.SMOKE_REF if smoke_test and selected.get('lease_kind') == 'smoke' else queue_lease.REF)
    current = api(f"issues/{selected['issue_number']}")
    try:
        candidate = issue_input(current)
    except ValueError:
        candidate = None
    smoke_test = __import__('smoke').active(selected)
    if smoke_test and candidate is not None:
        candidate = __import__('smoke').issue_submission(candidate)
    proceed = candidate == selected['submission'] and body_hash(current['body']) == selected['issue_body_sha256']
    record = selected['record_gate'] if smoke_test else current_record(selected['submission']['problem'], selected['issue_url'])
    proceed = proceed and (smoke_test or qualifies_for_run(selected['submission'], record))
    # Split run: job 1's gate said claimed_only, so it uploaded no build. Only an explicit 'false' counts;
    # an empty value (job 1 failed before its gate) leaves the check to unpack, which refuses.
    if os.environ.get('BOS_SPLIT') == 'true' and os.environ.get('BOS_BUILD_PROCEED') == 'false':
        proceed = False
    selected['record_gate'] = record
    Path('artifacts').mkdir(exist_ok=True)
    Path('artifacts/selected-request.json').write_text(canonical(selected)+'\n')
    Path('request/request.json').write_text(canonical(selected) + '\n')
    with open(os.environ['GITHUB_OUTPUT'], 'a') as out:
        out.write('proceed=' + ('true' if proceed else 'false') + '\n')
    Path('artifacts').mkdir(exist_ok=True)
    Path('artifacts/gate.json').write_text(canonical({'status': 'proceed' if proceed else 'claimed_only', 'reason': 'matches_or_beats_current_record' if proceed else 'record_or_issue_changed', 'record_gate': record}) + '\n')


def verdict(receipt, selected):
    expected = make_request(selected['submission'])
    names = selected_profile(selected['submission'])['theorem_names']
    if (receipt.get('request') != expected or receipt.get('theorem_names') != names
            or receipt.get('generated_challenge_sha256') != hashlib.sha256(challenge_source(selected['submission']).encode()).hexdigest()):
        return 'not_verified', 'statement_or_request_mismatch'
    return admission(receipt, names)


def passes(receipt, selected):
    return verdict(receipt, selected)[0] == 'passed'


def envelope(receipt, selected, run_id, run_attempt, verifier_commit, receipt_url):
    if submission_hash(selected['submission']) != selected['submission_sha256']:
        raise ValueError('Request hash mismatch')
    if selected['inputs'] != make_request(selected['submission']):
        raise ValueError('Request mismatch')
    run_url = f'https://github.com/{REPOSITORY}/actions/runs/{run_id}'
    if receipt.get('run_url') != run_url or receipt.get('verifier_commit') != verifier_commit:
        raise ValueError('Receipt run provenance mismatch')
    status, reason = verdict(receipt, selected)
    profile = selected_profile(selected['submission'])
    return {'schema_version': 1, 'submission': selected['submission'],
            'test_only': selected['test_only'],
            'issue_body_sha256': selected['issue_body_sha256'],
            'issue_submitter_login': selected['issue_submitter_login'],
            'problem_id': MODEL_IDS[selected['submission']['problem']], 'score_relation': 'attained',
            'model_revision': profile['upstream_commit'], 'model_sha256': profile['challenge_sha256'],
            'source_published_at': selected.get('source_published_at'),
            'checked_at': receipt.get('checked_at'), 'workflow_conclusion': None,
            'challenge': {'file': profile['challenge_file'], 'sha256': profile['challenge_sha256'],
                          'upstream_commit': profile['upstream_commit'], 'generated_sha256': receipt.get('generated_challenge_sha256')},
            'theorem_names': profile['theorem_names'], 'record_gate': selected.get('record_gate'),
            'submission_sha256': selected['submission_sha256'], 'issue_number': selected['issue_number'],
            'issue_url': selected['issue_url'], 'issue_created_at': selected['issue_created_at'],
            'issue_updated_at': selected['issue_updated_at'], 'receipt_url': receipt_url, 'run_url': run_url,
            'run_id': str(run_id), 'run_attempt': str(run_attempt), 'verifier_commit': verifier_commit,
            'status': 'fixture_only' if selected['test_only'] else status,
            'verification_status': status, 'importable': not selected['test_only'] and not derivation_hold(selected),
            'derivation': selected.get('derivation'),
            'reason': reason, 'receipt': receipt}


def derivation_hold(selected):
    """The derivation report found a constants-only change of another author's verified submission:
    a pass stays open and is not importable until a maintainer decides (scripts/derivation.py)."""
    return (selected.get('derivation') or {}).get('hold') is True


HOLD_TEXT = ('Held for maintainer review: the derivation report on this {item} found that this version changes only numeric '
             'constants of another author\'s verified submission. This {item} stays open, and the result is not listed as '
             'Lean Verified until a maintainer decides.')


def receipt_artifact():
    run_id, attempt, number = os.environ['GITHUB_RUN_ID'], os.environ['GITHUB_RUN_ATTEMPT'], os.environ['ISSUE_NUMBER']
    name = f'verifier-receipt-and-logs-{run_id}-{attempt}-{number}'
    artifacts = api(f'actions/runs/{run_id}/artifacts?per_page=100')['artifacts']
    match = [a for a in artifacts if a['name'] == name and not a.get('expired')]
    if len(match) != 1:
        raise ValueError('Missing or ambiguous receipt artifact')
    artifact = match[0]
    return {'id': artifact['id'], 'name': name, 'digest': artifact.get('digest'),
            'archive_url': f'https://github.com/{REPOSITORY}/actions/runs/{run_id}/artifacts/{artifact["id"]}'}


def report_submission(current, selected):
    sub = issue_input(current)
    import smoke
    if smoke.active(selected):
        sub = smoke.issue_submission(sub)
    return sub


def report():
    selected = json.loads(Path('request/request.json').read_text())
    receipt_file = Path('result/receipt.json')
    receipt = json.loads(receipt_file.read_text()) if receipt_file.exists() else {}
    run_id, attempt, commit = os.environ['GITHUB_RUN_ID'], os.environ['GITHUB_RUN_ATTEMPT'], os.environ['GITHUB_SHA']
    run_url = f'https://github.com/{REPOSITORY}/actions/runs/{run_id}'
    # Setup can fail before the controller has stored its normal provenance.
    receipt.setdefault('run_url', run_url)
    receipt.setdefault('verifier_commit', commit)
    result = envelope(receipt, selected, run_id, attempt, commit, receipt_artifact()['archive_url'])
    result['receipt_artifact'] = receipt_artifact()
    result['receipt_sha256'] = hashlib.sha256(receipt_file.read_bytes()).hexdigest() if receipt_file.exists() else None
    gate_path = Path('result/gate.json')
    if gate_path.exists():
        result['record_gate'] = json.loads(gate_path.read_text())['record_gate']
    Path('published').mkdir(exist_ok=True)
    Path('published/direct-submission.json').write_text(canonical(result) + '\n')
    current = api(f"issues/{selected['issue_number']}")
    try:
        current_submission = report_submission(current, selected)
    except ValueError:
        current_submission = None
    stale = current_submission != selected['submission'] or body_hash(current.get('body') or '') != selected['issue_body_sha256']
    status = {'passed': 'Lean Verified', 'blocked': 'Blocked for maintainer review', 'pending_review': 'Pending review'}.get(result['verification_status'], 'Not verified')
    if result['test_only']:
        status = 'TEST ONLY: ' + ('proof checks passed' if result['verification_status'] == 'passed' else status)
    body = marker_for(selected['issue_number'], selected['submission_sha256'], selected['issue_body_sha256']) + '\n'
    # The site reads this first line and the two NOT_FINAL phrases below (bigospeedrun/site data/direct_refresh.py):
    # keep them byte for byte. A Not verified result says why on the next line.
    body += f"{status} for source commit `{selected['submission']['commit']}`.\n"
    if result['verification_status'] == 'not_verified':
        body += reason_line(receipt, result['reason']) + '\n'
    body += '\n'
    body += f"[Receipt and logs]({result['receipt_url']}) · [Workflow run]({run_url})\n\n"
    body += compile_error_comment(receipt)
    if stale:
        body += 'This result belongs to an older or closed submission. The current issue is not verified by this result.\n\n'
    if result['status'] in ['blocked', 'pending_review']:
        body += '@nmamano This result requires review and cannot admit a row. Review the kernel outcome and axiom audit in the receipt.\n\n'
    if gate_path.exists() and json.loads(gate_path.read_text())['status'] == 'claimed_only':
        body += 'The issue or current record changed before compilation. This submission remains Claimed; no proof run started.\n\n'
    body += 'A pass checks the stated bound in the fixed model. It does not establish novelty, priority, authorship, or practical speed.'
    # Nil rule 2026-10-17: no issue stays open indefinitely. Close after the final result
    # comment: completed on a verified pass, not planned on a genuine rejection. Stale and
    # claimed-only results are not final, and ambiguous or resource outcomes stay open for review.
    kernels = receipt.get('kernels', {})
    rejected = any(kernels.get(kernel, {}).get('status') == 'rejected' for kernel in ['lean', 'nanoda'])
    close = None
    # A test_only (smoke) run never closes its issue: the hosted smoke identities must stay open.
    if not stale and not result['test_only'] and not (gate_path.exists() and json.loads(gate_path.read_text())['status'] == 'claimed_only'):
        if result['status'] == 'passed' and derivation_hold(selected):
            body += '\n\n' + HOLD_TEXT.format(item='issue')
        elif result['status'] == 'passed':
            close = 'completed'
            body += '\n\nTo submit a stronger bound, open a new issue. This issue now closes.'
        elif result['status'] == 'blocked' or rejected or deterministic_setup_failure(receipt):
            close = 'not_planned'
            body += '\n\nTo submit a corrected proof, open a new issue. This issue now closes.'
    if not stale and not result['test_only']:
        line = board_line(selected['submission']['problem'])
        if line:
            body += '\n\n' + line
    # Content is generated solely from bounded fields. Never post proof logs.
    payload = {'issue_number': selected['issue_number'], 'body': body}
    if __import__('smoke').silent(selected):
        payload['silent'] = True
    if close:
        payload['close'] = close
    if gate_path.exists() and json.loads(gate_path.read_text())['status'] == 'claimed_only' and not stale and not result['test_only']:
        # The record improved between selection and compilation: the same claimed-only end as at selection.
        payload['claimed'] = selected['submission_sha256']
    if result['status'] == 'passed' and derivation_hold(selected) and not stale and not result['test_only']:
        payload['hold'] = {'submission_sha256': selected['submission_sha256'], 'version': selected['issue_body_sha256'],
                           'derivation': selected['derivation']}
    Path('published-comment.json').write_text(canonical(payload) + '\n')


def publish():
    # Called only after the immutable result artifact has uploaded successfully.
    comment = json.loads(Path('published-comment.json').read_text())
    if comment.get('silent'):
        print('Silent maintainer smoke: nothing is posted; read the result artifact.', flush=True)
        return
    comment_once(comment['issue_number'], comment['body'])
    # A final result closes the issue: completed on a pass, not planned on a rejection.
    # Only the report comment carries a close decision; earlier comments never close.
    if comment.get('close'):
        api(f"issues/{comment['issue_number']}", {'state': 'closed', 'state_reason': comment['close']}, method='PATCH')
    if comment.get('claimed'):
        close_claimed(comment['issue_number'], comment['claimed'], 'issue')
    if comment.get('hold'):
        # A derivation hold: the review label and one maintainer ping that names the release entry.
        import pr_submissions
        hold = comment['hold']
        pr_submissions.hold_ping(comment['issue_number'], 'issue', hold['submission_sha256'], hold['version'], hold['derivation'])


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('phase', choices=['select', 'materialize', 'preflight', 'report', 'publish'])
    args = parser.parse_args()
    globals()[args.phase]()
