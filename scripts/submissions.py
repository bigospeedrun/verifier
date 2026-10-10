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
import time
from datetime import datetime, timezone
from verdicts import admission

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
        raise ValueError('Supported problems: dft, 3sum, apsp')
    if not isinstance(value['bound'], str) or not re.fullmatch(r'(?:0|[1-9][0-9]{0,17})(?:/[1-9][0-9]{0,17})?', value['bound']):
        raise ValueError('bound must be a nonnegative rational string, with at most 18 digits per integer')
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
MODEL_IDS = {'dft': 'exact-dft/uniform-exact-arithmetic', '3sum': '3sum/word-ram', 'apsp': 'apsp/word-ram'}


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


def selected_profile(submission):
    if submission.get('entrypoint') == 'dft233':
        return json.loads((ROOT / 'profiles/dft233.json').read_text())
    return json.loads((ROOT / 'profiles/direct.json').read_text())[submission['problem']]


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


def api(path, data=None, method=None):
    scan_check(path)
    # This constant origin is the only destination for this scoped token.
    req = urllib.request.Request('https://api.github.com/repos/' + REPOSITORY + '/' + path,
          data=None if data is None else json.dumps(data).encode(), method=method,
          headers={'Authorization': 'Bearer ' + os.environ['GH_TOKEN'], 'Accept': 'application/vnd.github+json',
                   'X-GitHub-Api-Version': '2022-11-28', 'Content-Type': 'application/json'})
    with urllib.request.urlopen(req, timeout=scan_timeout()) as response:
        return json.load(response)


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
        scan_check(path)
        req = urllib.request.Request('https://api.github.com/repos/bigospeedrun/site/' + path,
                                     headers={'Accept': 'application/vnd.github+json',
                                              'Authorization': 'Bearer ' + os.environ['GH_TOKEN']})
        with urllib.request.urlopen(req, timeout=scan_timeout()) as response:
            return json.load(response)
    sha = read('commits/main')['sha']
    if not re.fullmatch('[0-9a-f]{40}', sha):
        raise ValueError('Invalid site commit')
    slug = 'exact-dft' if problem == 'dft' else problem
    obj = read(f'contents/data/{slug}.json?ref={sha}')
    raw = base64.b64decode(obj['content'], validate=False)
    return sha, raw


def current_record(problem, issue_url):
    """Read the board from a resolved immutable site commit, never the issue repo."""
    sha, raw = site_snapshot(problem)
    data = json.loads(raw)
    if data['problem_id'] != MODEL_IDS[problem]:
        raise ValueError('Current record model mismatch')
    records = [r for r in data['records'] if r.get('submission_url') != issue_url
               and r['id'] != 'classical-baseline'
               and not data['record_metadata'].get(r['id'], {}).get('reproduction_of')]
    if not records:
        raise ValueError('No current record; refuse to guess')
    # Mirrors the site comparison: exact score first, attained above a strict
    # frontier at equal saving. Lower-exponent frontiers sort before attained.
    key = lambda r: (Fraction(r['score']), -1 if r.get('score_relation') == 'strict-upper-bound' else 0)
    best = (max if problem == 'dft' else min)(records, key=key)
    leaders = [r for r in records if key(r) == key(best)]
    def lean_verified(row):
        metadata = data['record_metadata'].get(row['id'], {})
        rerun = row.get('rerun_status') or {}
        return metadata.get('site_tier') == 'verified' and rerun.get('state') == 'passed' and bool(rerun.get('receipt_path'))
    return {'schema_version': 1, 'score': str(Fraction(best['score'])),
            'score_relation': best.get('score_relation', 'attained'),
            'leader_ids': sorted(r['id'] for r in leaders),
            'any_lean_verified_at_bound': any(lean_verified(r) for r in leaders),
            'problem_id': data['problem_id'], 'site_commit': sha,
            'data_sha256': hashlib.sha256(raw).hexdigest(),
            'checked_at': datetime.now(timezone.utc).isoformat().replace('+00:00', 'Z')}


def qualifies_for_run(submission, record):
    candidate = (Fraction(submission['bound']), 0)
    current = (Fraction(record['score']), -1 if record['score_relation'] == 'strict-upper-bound' else 0)
    if candidate == current:
        # A tie can upgrade Claimed evidence. Missing evidence metadata cannot
        # authorize a costly run. Never relabel another author's record.
        return record.get('any_lean_verified_at_bound') is False
    return candidate > current if submission['problem'] == 'dft' else candidate < current


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


def select_bounded():
    """One trusted batch; resumable 40-candidate/4-minute scan, ten accounts."""
    import queue_lease
    import pr_submissions as pr
    selected, authors = [], set()
    selection_outputs(selected)
    import smoke
    lease = queue_lease.acquire(queue_lease.SMOKE_REF) if smoke.requested() else queue_lease.acquire()
    if lease is None:
        return
    import smoke
    if smoke.dispatch(lease):
        return
    Path('requests').mkdir(exist_ok=True)
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
                # One bounded comments page; do not walk attacker-sized threads.
                comments = api(f"issues/{issue['number']}/comments?per_page=100&page=1")
                if 'pull_request' in issue:
                    request = pr.select_candidate(issue, lease)
                    if request is None:
                        continue
                    route = 'pull_request'
                else:
                    try:
                        submission = issue_input(issue)
                    except ValueError:
                        continue
                    if submission is None:
                        continue
                    request = issue_request(issue, submission)
                    digest = request['submission_sha256']
                    if lease.admitted(queue_lease.admission_key(request)):
                        continue
                    record = current_record(submission['problem'], request['issue_url'])
                    if not qualifies_for_run(submission, record):
                        marker = f"<!-- bos-claimed-v1 {issue['number']} {digest} -->"
                        if not any(is_bot(c) and c.get('body', '').startswith(marker) for c in comments):
                            api(f"issues/{issue['number']}/comments", {'body': marker + '\nThis submission is listed as Claimed; the bound does not qualify for a proof run.'})
                        continue
                    request['record_gate'] = record
                    route = 'issue'
                lease.reserve(queue_lease.admission_key(request))
                authors.add(login)
                Path(f"requests/{issue['number']}.json").write_text(canonical(request) + '\n')
                selected.append({'issue_number': issue['number'], 'login': login, 'route': route})
                selection_outputs(selected)
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
            'verification_status': status, 'importable': not selected['test_only'],
            'reason': reason, 'receipt': receipt}


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
        current_submission = issue_input(current)
    except ValueError:
        current_submission = None
    stale = current_submission != selected['submission'] or body_hash(current.get('body') or '') != selected['issue_body_sha256']
    status = {'passed': 'Lean Verified', 'blocked': 'Blocked for maintainer review', 'pending_review': 'Pending review'}.get(result['status'], 'Not verified')
    body = marker_for(selected['issue_number'], selected['submission_sha256'], selected['issue_body_sha256']) + '\n'
    body += f"{status} for source commit `{selected['submission']['commit']}`.\n\n"
    body += f"[Receipt and logs]({result['receipt_url']}) · [Workflow run]({run_url})\n\n"
    if stale:
        body += 'This result belongs to an older or closed submission. The current issue is not verified by this result.\n\n'
    if result['status'] in ['blocked', 'pending_review']:
        body += '@nmamano This result requires review and cannot admit a row. Review the kernel outcome and axiom audit in the receipt.\n\n'
    if gate_path.exists() and json.loads(gate_path.read_text())['status'] == 'claimed_only':
        body += 'The issue or current record changed before compilation. This submission remains Claimed; no proof run started.\n\n'
    body += 'A pass checks the stated bound in the fixed model. It does not establish novelty, priority, authorship, or practical speed.'
    # Content is generated solely from bounded fields. Never post proof logs.
    Path('published-comment.json').write_text(canonical({'issue_number': selected['issue_number'], 'body': body}) + '\n')


def publish():
    # Called only after the immutable result artifact has uploaded successfully.
    comment = json.loads(Path('published-comment.json').read_text())
    api(f"issues/{comment['issue_number']}/comments", {'body': comment['body']})


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('phase', choices=['select', 'materialize', 'preflight', 'report', 'publish'])
    args = parser.parse_args()
    globals()[args.phase]()
