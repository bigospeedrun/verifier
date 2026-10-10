#!/usr/bin/env python3
"""PR sources are data. Only the workflow_run publisher has write permission."""
import argparse
import base64
import hashlib
import io
import json
import os
from pathlib import Path, PurePosixPath
import re
import urllib.error
import urllib.request
import urllib.parse
import zipfile
from functools import lru_cache

import submissions as s
from verdicts import AXIOMS

ROOT = Path(__file__).resolve().parents[1]
WORKFLOW = '.github/workflows/submissions.yml'
PUBLISHER = '.github/workflows/pr-publish.yml'
MAX_FILES = 500
MAX_ARCHIVE = 50 * 1024 * 1024
SHA = re.compile('[0-9a-f]{40}\\Z')


class LayoutError(ValueError):
    pass


class SupersededHead(ValueError):
    pass


def api(path, data=None, method=None, raw=False):
    s.scan_check(path)
    req = urllib.request.Request('https://api.github.com/repos/' + s.REPOSITORY + '/' + path,
        data=None if data is None else json.dumps(data).encode(), method=method,
        headers={'Authorization': 'Bearer ' + os.environ['GH_TOKEN'],
                 'Accept': 'application/vnd.github+json', 'Content-Type': 'application/json',
                 'X-GitHub-Api-Version': '2022-11-28'})
    class PublicRedirect(urllib.request.HTTPRedirectHandler):
        def redirect_request(self, request, fp, code, msg, headers, newurl):
            redirected = super().redirect_request(request, fp, code, msg, headers, newurl)
            if urllib.parse.urlsplit(newurl).netloc != 'api.github.com':
                redirected.remove_header('Authorization')
            return redirected
    opener = urllib.request.build_opener(PublicRedirect)
    with opener.open(req, timeout=s.scan_timeout()) as response:
        return bounded_read(response) if raw else json.load(response)


def bounded_read(response):
    content_length = response.headers.get('Content-Length')
    if content_length is not None and int(content_length) > MAX_ARCHIVE:
        raise ValueError('Artifact exceeds download limit')
    chunks, total = [], 0
    while total <= MAX_ARCHIVE:
        chunk = response.read(min(65536, MAX_ARCHIVE + 1 - total))
        if not chunk:
            return b''.join(chunks)
        chunks.append(chunk)
        total += len(chunk)
    raise ValueError('Artifact exceeds download limit')


def validate_artifact_size(artifact):
    size = artifact.get('size_in_bytes')
    if type(size) is not int or not 0 <= size <= MAX_ARCHIVE:
        raise ValueError('Artifact API size is missing or exceeds limit')


def digest(value):
    return hashlib.sha256(value).hexdigest()


def blob_sha(value):
    return hashlib.sha1(b'blob ' + str(len(value)).encode() + b'\0' + value).hexdigest()


@lru_cache(maxsize=1024)
def git_tree(sha):
    return api(f'git/trees/{sha}')


@lru_cache(maxsize=128)
def commit_tree(sha):
    return api(f'git/commits/{sha}')['tree']['sha']


def file_at(commit, path):
    """Walk Git trees without a recursive response that may be truncated."""
    tree = commit_tree(commit)
    parts = PurePosixPath(path).parts
    for i, part in enumerate(parts):
        listing = git_tree(tree)
        if listing.get('truncated'):
            raise LayoutError('Truncated Git tree')
        entries = [e for e in listing['tree'] if e['path'] == part]
        if not entries:
            return None
        entry = entries[0]
        if i == len(parts)-1:
            return entry
        if entry['type'] != 'tree' or entry['mode'] != '040000':
            raise LayoutError('Non-directory parent in submission path')
        tree = entry['sha']


def files_changed(number):
    result = []
    page = 1
    while True:
        batch = api(f'pulls/{number}/files?per_page=100&page={page}')
        result.extend(batch)
        if len(result) > MAX_FILES:
            raise LayoutError('Submission exceeds 500 files')
        if len(batch) < 100:
            return result
        page += 1


def validate_layout(pr, changed, base_exists, entries):
    login = pr['user']['login'].lower()
    if not re.fullmatch('[a-z0-9][a-z0-9-]{0,38}', login):
        raise LayoutError('Unsupported GitHub login')
    if not changed or len(changed) != pr['changed_files'] or len(changed) > MAX_FILES:
        raise LayoutError('Incomplete or oversized PR diff')
    folder = None
    paths = set()
    for file in changed:
        path = file['filename']
        match = re.fullmatch(r'submissions/(dft|3sum|apsp)/(' + re.escape(login) + r'-[a-z0-9][a-z0-9-]{0,39})/(.+)', path)
        if not match or file['status'] != 'added' or file.get('previous_filename'):
            raise LayoutError('PR must add only files inside its own new submission folder')
        prefix = '/'.join(path.split('/')[:3])
        if folder is not None and folder != prefix:
            raise LayoutError('PR contains more than one submission folder')
        folder = prefix
        relative = match[3]
        if relative not in ['manifest.json', 'Submission.lean'] and not re.fullmatch(r'Submission/(?:[A-Za-z_][A-Za-z0-9_]*/)*[A-Za-z_][A-Za-z0-9_]*\.lean', relative):
            raise LayoutError('Only manifest.json, Submission.lean and Submission/*.lean are permitted')
        if path in paths:
            raise LayoutError('Duplicate changed path')
        paths.add(path)
    if base_exists:
        raise LayoutError('Submission folder already exists on the base branch')
    expected = {folder + '/manifest.json', folder + '/Submission.lean'}
    if not expected <= paths or paths != set(entries):
        raise LayoutError('Missing root files or incomplete head tree')
    total = 0
    records = []
    for path in sorted(paths):
        e = entries[path]
        if e['mode'] != '100644' or e['type'] != 'blob' or not SHA.fullmatch(e['sha']):
            raise LayoutError('Symlinks, submodules, executable files and directories are not admitted')
        size = e['size']
        if type(size) is not int or not 0 <= size <= 20_000_000:
            raise LayoutError('Invalid or excessive file size')
        total += size
        records.append({'path': path, 'mode': e['mode'], 'sha': e['sha'], 'size': size})
    if total > 150_000_000:
        raise LayoutError('Submission source exceeds 150 MB')
    return folder, records


def parse_manifest(raw, problem):
    if len(raw) > 1024:
        raise LayoutError('Manifest exceeds 1 KB')
    def unique(pairs):
        obj = {}
        for k, v in pairs:
            if k in obj:
                raise LayoutError('Duplicate manifest key')
            obj[k] = v
        return obj
    obj = json.loads(raw, object_pairs_hook=unique)
    if not isinstance(obj, dict) or set(obj) != {'problem', 'bound'} or obj['problem'] != problem:
        raise LayoutError('Manifest must contain exactly problem and bound, matching the folder')
    sub = s.validate_submission({'schema_version': 1, 'problem': problem, 'bound': obj['bound'],
        'repo_url': 'https://github.com/example/proof', 'commit': 'a'*40, 'authors': []})
    if sub['bound'] != obj['bound']:
        raise LayoutError('Manifest bound must be a reduced exact rational')
    return obj


def inspect_pr(pr, manifest_bytes=None):
    if pr['base']['repo']['full_name'] != s.REPOSITORY or pr['base']['ref'] != 'main':
        raise LayoutError('PR must target verifier main')
    head, base = pr['head']['sha'], pr['base']['sha']
    if not SHA.fullmatch(head) or not SHA.fullmatch(base):
        raise LayoutError('Invalid commit pin')
    changed = files_changed(pr['number'])
    if not changed:
        raise LayoutError('Empty PR')
    # Resolve folder from a bounded path; validate_layout checks every path.
    folder = '/'.join(changed[0]['filename'].split('/')[:3])
    if not re.fullmatch(r'submissions/(dft|3sum|apsp)/[a-z0-9-]+', folder):
        raise LayoutError('PR changes a protected path')
    base_exists = file_at(base, folder) is not None
    head_entry = file_at(head, folder)
    if not head_entry or head_entry['type'] != 'tree':
        raise LayoutError('Missing submission tree')
    listing = api(f"git/trees/{head_entry['sha']}?recursive=1")
    if listing.get('truncated'):
        raise LayoutError('Truncated submission tree')
    entries = {folder + '/' + e['path']: e for e in listing['tree'] if e['type'] != 'tree'}
    folder, records = validate_layout(pr, changed, base_exists, entries)
    manifest_entry = entries[folder + '/manifest.json']
    if manifest_bytes is None:
        blob = api(f"git/blobs/{manifest_entry['sha']}")
        manifest_bytes = base64.b64decode(blob['content'], validate=False)
    if blob_sha(manifest_bytes) != manifest_entry['sha']:
        raise LayoutError('Manifest blob does not match the PR head')
    manifest = parse_manifest(manifest_bytes, folder.split('/')[1])
    # Source can be fetched through the base repo's PR ref by immutable SHA.
    # No independently owned public proof project is required.
    submission = s.validate_submission({'schema_version': 1, 'problem': manifest['problem'],
        'bound': manifest['bound'], 'repo_url': 'https://github.com/' + s.REPOSITORY,
        'commit': head, 'authors': [], 'source_subdir': folder})
    return {'schema_version': 2, 'route': 'pull_request', 'test_only': False,
        'submission': submission, 'submission_sha256': s.submission_hash(submission),
        'inputs': s.make_request(submission), 'pr_number': pr['number'],
        'pr_url': f"https://github.com/{s.REPOSITORY}/pull/{pr['number']}",
        'pr_submitter_login': pr['user']['login'], 'pr_created_at': pr['created_at'],
        'base_sha': base, 'head_sha': head, 'source_subdir': folder,
        'manifest_utf8': manifest_bytes.decode('utf-8'), 'manifest_sha256': digest(manifest_bytes),
        'changed_files': records, 'changed_files_sha256': digest(s.canonical(records).encode())}


def protected_files():
    """Executable/config trust boundary; submission additions are excluded."""
    return sorted(str(p.relative_to(ROOT)) for parent in ['.github/workflows', 'scripts', 'profiles', 'challenges/dft', 'challenges/3sum-apsp']
                  for p in (ROOT / parent).rglob('*') if p.is_file() and '__pycache__' not in p.parts)


def validate_controller(head, base):
    # The publisher does not check out PR code. It compares Git blob identities.
    for path in protected_files():
        expected = blob_sha((ROOT / path).read_bytes())
        for commit in [head, base]:
            entry = file_at(commit, path)
            if not entry or entry['mode'] != '100644' or entry['sha'] != expected:
                raise LayoutError('PR workflow/controller differs from the trusted publisher revision')


def select_candidate(issue, lease):
    import queue_lease
    pr = api(f"pulls/{issue['number']}")
    if lease.admitted(queue_lease.admission_key({'route': 'pull_request', 'pr_number': pr['number'], 'head_sha': pr['head']['sha']})):
        return None
    selected = {'schema_version': 2, 'route': 'pull_request', 'pr_number': pr['number'],
        'head_sha': pr['head']['sha'], 'base_sha': pr['base']['sha'],
        'pr_submitter_login': pr['user']['login'], 'test_only': False}
    try:
        selected = inspect_pr(pr)
        record = s.current_record(selected['submission']['problem'], selected['pr_url'])
        selected['record_gate'] = record
        selected.update(gate='ready' if s.qualifies_for_run(selected['submission'], record) else 'claimed_only', reason='record_gate')
    except LayoutError as exc:
        selected.update(gate='invalid_layout', reason=str(exc))
    selected['verifier_commit'] = os.environ['GITHUB_SHA']
    return selected


def materialize_pr():
    number = os.environ['ISSUE_NUMBER']
    if not re.fullmatch('[1-9][0-9]*', number):
        raise ValueError('Invalid PR number')
    selected = json.loads(Path(f'requests/{number}.json').read_text())
    if selected['pr_number'] != int(number) or (selected.get('test_only') is not False and not __import__('smoke').active(selected)):
        raise ValueError('PR identity mismatch or fixture')
    Path('pr-input').mkdir(exist_ok=True)
    Path('pr-input/pr-request.json').write_text(s.canonical(selected) + '\n')


def preflight_pr():
    import queue_lease
    selected = json.loads(Path('pr-input/pr-request.json').read_text())
    smoke_test = __import__('smoke').active(selected)
    queue_lease.assert_owner(queue_lease.SMOKE_REF if smoke_test and selected.get('lease_kind') == 'smoke' else queue_lease.REF)
    pr = api(f"pulls/{selected['pr_number']}")
    if pr['state'] != 'open' or pr['head']['sha'] != selected['head_sha']:
        selected.update(gate='superseded', reason='PR changed before compilation')
    elif selected.get('gate') == 'ready':
        inspect_pr(pr, selected['manifest_utf8'].encode())
        smoke_test = __import__('smoke').active(selected)
        record = selected['record_gate'] if smoke_test else s.current_record(selected['submission']['problem'], selected['pr_url'])
        selected['record_gate'] = record
        if not smoke_test and not s.qualifies_for_run(selected['submission'], record):
            selected.update(gate='claimed_only', reason='record_changed_before_compilation')
    Path('artifacts').mkdir(exist_ok=True)
    Path('artifacts/pr-request.json').write_text(s.canonical(selected) + '\n')
    Path('pr-request.json').write_text(s.canonical(selected) + '\n')
    with open(os.environ['GITHUB_OUTPUT'], 'a') as out:
        out.write('proceed=' + str(selected['gate'] == 'ready').lower() + '\n')


def verify_receipt(receipt, selected):
    if receipt.get('verifier_commit') != selected['verifier_commit']:
        raise ValueError('Receipt controller revision mismatch')
    if receipt.get('request') != s.make_request(selected['submission']):
        raise ValueError('Receipt request mismatch')
    if receipt.get('generated_challenge_sha256') != digest(s.challenge_source(selected['submission']).encode()):
        raise ValueError('Receipt trusted target mismatch')
    profile = s.selected_profile(selected['submission'])
    if receipt.get('profile') != profile:
        raise ValueError('Receipt profile mismatch')
    return s.verdict(receipt, selected)


def outcome(receipt, selected, conclusion):
    if conclusion in ['cancelled', 'timed_out', 'action_required', 'startup_failure']:
        return 'keep_open', 'Workflow did not complete; maintainer review required'
    if selected.get('gate') == 'invalid_layout':
        return 'close', selected['reason']
    if selected.get('gate') == 'claimed_only':
        return 'claimed_only', 'Bound below the record, or a tied leader is already Lean Verified'
    if selected.get('gate') == 'superseded':
        return 'keep_open', 'This event was superseded before compilation'
    if not receipt:
        return 'keep_open', 'Missing verification receipt; infrastructure review required'
    status, reason = verify_receipt(receipt, selected)
    kernels = receipt.get('kernels', {})
    if status == 'passed':
        return 'merge', reason
    if kernels.get('lean', {}).get('status') == 'rejected' or kernels.get('nanoda', {}).get('status') == 'rejected':
        return 'close', 'Lean or nanoda rejected the proof'
    audit = receipt.get('axiom_audit', {})
    reported = audit.get('reported_axioms', {})
    if audit.get('exit_code') == 0 and set(reported) == set(s.selected_profile(selected['submission'])['theorem_names']) and any(isinstance(a, list) and set(a)-AXIOMS for a in reported.values()):
        return 'close', 'Axiom audit found an unpermitted axiom'
    return 'keep_open', reason


def read_archive(raw, metadata):
    if len(raw) > MAX_ARCHIVE or metadata.get('digest') != 'sha256:' + digest(raw):
        raise ValueError('Artifact size or digest mismatch')
    result = {}
    with zipfile.ZipFile(io.BytesIO(raw)) as archive:
        if sum(e.file_size for e in archive.infolist()) > MAX_ARCHIVE:
            raise ValueError('Expanded artifact exceeds limit')
        for entry in archive.infolist():
            if not re.fullmatch('[A-Za-z0-9_.-]+', entry.filename) or entry.filename in result or entry.filename in ['.', '..']:
                raise ValueError('Unexpected artifact path')
            result[entry.filename] = archive.read(entry)
    return result


def validate_run_identity(run, allow_running=False):
    if (run.get('repository', {}).get('full_name') != s.REPOSITORY
            or run.get('path') != WORKFLOW or run.get('event') not in ['schedule', 'issues', 'workflow_dispatch']
            or run.get('status') not in (['in_progress', 'completed'] if allow_running else ['completed']) or run.get('head_branch') != 'main'
            or run.get('head_repository', {}).get('full_name') != s.REPOSITORY):
        raise ValueError('Untrusted verification workflow')
    workflow = api('actions/workflows/submissions.yml')
    if run['workflow_id'] != workflow['id']:
        raise ValueError('Workflow ID mismatch')


def validate_run(run, request, pr, allow_running=False):
    validate_run_identity(run, allow_running)
    if (request.get('test_only') is not False and not __import__('smoke').active(request)) or request.get('route') != 'pull_request' or request.get('pr_number') != pr['number']:
        raise ValueError('Fixture or PR identity mismatch')
    if run.get('head_sha') != request['verifier_commit']:
        raise ValueError('Run controller revision mismatch')
    if request['pr_submitter_login'] != pr['user']['login']:
        raise ValueError('PR submitter mismatch')


def publish_batch():
    event = json.loads(Path(os.environ['GITHUB_EVENT_PATH']).read_text())
    run = api(f"actions/runs/{event['workflow_run']['id']}")
    validate_run_identity(run)
    if run['run_attempt'] != event['workflow_run'].get('run_attempt'):
        raise ValueError('Superseded workflow attempt')
    artifacts = api(f"actions/runs/{run['id']}/artifacts?per_page=100")['artifacts']
    pattern = rf"pr-verification-{run['id']}-{run['run_attempt']}-[1-9][0-9]*"
    matches = [a for a in artifacts if re.fullmatch(pattern, a['name']) and not a.get('expired')]
    if len(matches) > 10 or len({a['name'] for a in matches}) != len(matches):
        raise ValueError('Oversized or duplicate PR batch')
    for artifact in matches:
        publish_pr(artifact)


def publish_pr(artifact_override=None, stage="final"):
    event = json.loads(Path(os.environ['GITHUB_EVENT_PATH']).read_text())
    run_id = event['workflow_run']['id']
    run = api(f'actions/runs/{run_id}')
    validate_run_identity(run, allow_running=stage == "lean")
    attempt = run['run_attempt']
    if event['workflow_run'].get('run_attempt') != attempt:
        raise ValueError('Superseded workflow attempt; no PR mutation')
    if artifact_override is None:
        artifacts = api(f'actions/runs/{run_id}/artifacts?per_page=100')['artifacts']
        matches = [a for a in artifacts if re.fullmatch(rf'pr-verification-{run_id}-{attempt}-[1-9][0-9]*', a['name']) and not a.get('expired')]
        if len(matches) != 1:
            raise ValueError('Expected one PR artifact')
        artifact = matches[0]
    else:
        artifact = artifact_override
    validate_artifact_size(artifact)
    raw = api(f"actions/artifacts/{artifact['id']}/zip", raw=True)
    files = read_archive(raw, artifact)
    request = json.loads(files['pr-request.json'])
    number = request['pr_number']
    if type(number) is not int or number <= 0:
        raise ValueError('Invalid PR number')
    pr = api(f'pulls/{number}')
    validate_run(run, request, pr, allow_running=stage == "lean")
    suffix = '-lean' if stage == 'lean' else ''
    if artifact['name'] != f'pr-verification-{run_id}-{attempt}-{number}{suffix}':
        raise ValueError('Artifact PR identity mismatch')
    recovering_merge = pr['state'] == 'closed' and pr.get('merged') is True
    if pr['state'] != 'open' and not recovering_merge:
        return
    receipt = json.loads(files['receipt.json']) if 'receipt.json' in files else None
    if stage == 'lean' and receipt and receipt.get('verification_stage') != 'lean':
        raise ValueError('Early artifact is not a Lean checkpoint')
    url = f"https://github.com/{s.REPOSITORY}/actions/runs/{run_id}/artifacts/{artifact['id']}"
    disposition, reason = 'keep_open', 'Result needs review'
    superseded = False
    try:
        # An old run must not judge the new head against the old manifest.
        if pr['head']['sha'] != request['head_sha']:
            raise SupersededHead('A newer commit has its own check; this result will not merge or close the PR')
        # Always re-read the entire live diff before making a merge decision.
        inspected = pr
        if recovering_merge:
            # Rebuild the publication artifact after an upload/runner failure.
            # The API-confirmed merge and original immutable base bind recovery.
            inspected = dict(pr, base=dict(pr['base'], sha=request['base_sha']))
        checked = inspect_pr(inspected, request.get('manifest_utf8', '').encode())
        validate_controller(checked['head_sha'], request['verifier_commit'])
        for field in ['submission', 'submission_sha256', 'source_subdir', 'manifest_sha256', 'changed_files_sha256']:
            if checked[field] != request.get(field):
                raise LayoutError('PR source/manifest changed since verification')
        if receipt and receipt.get('run_url') != f'https://github.com/{s.REPOSITORY}/actions/runs/{run_id}':
            raise ValueError('Receipt run mismatch')
        if receipt:
            for path, expected in receipt.get('artifact_sha256', {}).items():
                if path not in files or digest(files[path]) != expected:
                    raise ValueError('Receipt log hash mismatch')
        disposition, reason = outcome(receipt, request, run['conclusion'])
    except SupersededHead as exc:
        superseded = True
        disposition, reason = 'keep_open', str(exc)
    except LayoutError as exc:
        disposition, reason = 'close', str(exc)
    except ValueError as exc:
        disposition, reason = 'keep_open', str(exc)
    if recovering_merge and disposition == 'close':
        disposition, reason = 'blocked', 'Advisory rejection blocks this previously merged proof'
    envelope = {'verification_stage': stage, 'schema_version': 2, 'route': 'pull_request', 'test_only': request.get('test_only', True),
        'importable': disposition == 'merge' and request.get('test_only') is False, 'request': request, 'receipt': receipt,
        'run_id': str(run_id), 'run_attempt': str(attempt), 'verifier_commit': request['verifier_commit'],
        'run_url': f'https://github.com/{s.REPOSITORY}/actions/runs/{run_id}',
        'workflow_path': WORKFLOW, 'workflow_conclusion': run['conclusion'],
        'receipt_artifact': {'id': artifact['id'], 'name': artifact['name'], 'digest': artifact['digest'], 'url': url},
        'publisher_commit': os.environ['GITHUB_SHA'], 'publisher_run_id': os.environ['GITHUB_RUN_ID'],
        'publisher_run_attempt': os.environ['GITHUB_RUN_ATTEMPT'],
        'receipt_sha256': digest(files['receipt.json']) if 'receipt.json' in files else None,
        'disposition': disposition, 'reason': reason, 'merge_commit': None}
    comment = f"<!-- bos-pr-v2 {number} {request['head_sha']} -->\n" + f'PR proof result: **{disposition}**. {reason}.\n\n[Receipt and logs]({url})'
    if request.get('test_only'):
        comment += '\n\nTEST ONLY: this smoke result must never be imported.'
    if disposition == 'close' and receipt and receipt.get('kernels', {}).get('nanoda', {}).get('status') == 'rejected':
        comment += '\n\n@nmamano Nanoda rejected this proof; maintainer review is required.'
    # No proof output or unchecked issue text is posted.
    if recovering_merge:
        if disposition not in ['merge', 'blocked', 'keep_open'] or not pr.get('merge_commit_sha'):
            raise ValueError('Merged PR cannot be reconstructed as an accepted result')
        envelope['merge_commit'] = pr['merge_commit_sha']
        if disposition in ['blocked', 'keep_open']:
            api(f'issues/{number}/comments', {'body': comment + '\n\n@nmamano The advisory result blocks or suspends this merged proof; the site must replace its earlier passing status.'})
            label_review(number)
    else:
        api(f'issues/{number}/comments', {'body': comment})
    if disposition == 'merge' and not recovering_merge:
        # GitHub performs the final head compare atomically. Never retry without
        # the verified sha, and never bypass branch protection.
        try:
            result = api(f'pulls/{number}/merge', {'sha': request['head_sha'], 'merge_method': 'squash'}, method='PUT')
            if not result.get('merged'):
                raise ValueError('GitHub declined the merge')
            envelope['merge_commit'] = result['sha']
        except (urllib.error.HTTPError, ValueError):
            envelope.update(disposition='keep_open', reason='Merge declined or head changed; review required', importable=False)
            current = api(f'pulls/{number}')
            if current['head']['sha'] != request['head_sha']:
                envelope['reason'] = 'A newer commit has its own check; merge skipped'
            else:
                label_review(number)
    elif disposition == 'close' and not recovering_merge:
        current = api(f'pulls/{number}')
        if current['head']['sha'] != request['head_sha']:
            envelope.update(disposition='keep_open', reason='A newer commit has its own check; close skipped', importable=False)
        elif current['state'] == 'open':
            api(f'pulls/{number}', {'state': 'closed'}, method='PATCH')
    elif disposition == 'keep_open' and not recovering_merge and not superseded:
        label_review(number)
    Path('published').mkdir(exist_ok=True)
    Path(f'published/pr-submission-{number}{suffix}.json').write_text(s.canonical(envelope) + '\n')


def label_review(number):
    label = 'verification-needs-review'
    try:
        api('labels', {'name': label, 'color': 'd4c5f9', 'description': 'Proof check needs maintainer review'})
    except urllib.error.HTTPError as exc:
        if exc.code != 422:
            raise
    api(f'issues/{number}/labels', {'labels': [label]})
    api(f'issues/{number}/comments', {'body': '@nmamano This submission stays open because verification or publication needs review.'})


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('phase', choices=['materialize_pr', 'preflight_pr', 'publish_pr', 'publish_batch'])
    globals()[parser.parse_args().phase]()
