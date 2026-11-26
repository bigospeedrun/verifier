"""Default-branch admission lease. Fork read tokens cannot change this ref."""
import argparse
import base64
import hashlib
import json
import os
import re
import subprocess
import urllib.error
import urllib.request
from pathlib import Path
import submissions as s
import verdicts

REF = 'heads/automation/submission-queue'
SMOKE_REF = 'heads/automation/smoke-queue'


class Lease:
    def __init__(self, sha, state, tree, ref=REF):
        self.sha, self.state, self.tree = sha, state, tree
        self.ref = ref

    def save(self):
        commit = s.api('git/commits', {'message': s.canonical(self.state), 'tree': self.tree,
                                      'parents': [self.sha] if self.sha else []})['sha']
        if self.sha:
            s.api('git/refs/' + self.ref, {'sha': commit, 'force': False}, method='PATCH')
        else:
            s.api('git/refs', {'ref': 'refs/' + self.ref, 'sha': commit})
        self.sha = commit

    def item(self, path):
        """The file at path in the lease tree as of the current head (the API's content item), or None when it is absent."""
        try:
            return s.api(f'contents/{path}?ref={self.sha}')
        except urllib.error.HTTPError as exc:
            if exc.code == 404:
                return None
            raise

    def record(self, key):
        """The admission record of key (a dict), or None when the key has none."""
        item = self.item(admission_path(key))
        if item is None:
            return None
        if item.get('type') != 'file' or not 0 < item.get('size', 0) <= 1024:
            raise ValueError('Invalid admission state record')
        raw = base64.b64decode(item['content'], validate=False)
        if len(raw) > 1024:
            raise ValueError('Oversized admission state record')
        value = json.loads(raw)
        if value.get('schema_version') != 1 or value.get('key') != key:
            raise ValueError('Mismatched admission state record')
        return value

    def admitted(self, key):
        return self.record(key) is not None

    def reserve(self, key):
        # Persist before emitting runnable outputs. Never evict old keys: doing
        # so could cause unchanged rejected proofs to consume capacity again.
        value = {'schema_version': 1, 'key': key, 'run_id': self.state['run_id'],
                 'run_attempt': self.state['run_attempt']}
        self.tree = s.api('git/trees', {'base_tree': self.tree, 'tree': [
            {'path': admission_path(key), 'mode': '100644', 'type': 'blob',
             'content': s.canonical(value) + '\n'}]})['sha']
        self.save()


def admission_key(request):
    if request.get('route') == 'pull_request':
        identity = ['pull_request', request['pr_number'], request['head_sha']]
    else:
        identity = ['issue', request['issue_number'], request['submission_sha256'], request['issue_body_sha256']]
    return hashlib.sha256(s.canonical(identity).encode()).hexdigest()


def admission_path(key):
    if len(key) != 64 or any(c not in '0123456789abcdef' for c in key):
        raise ValueError('Invalid admission key')
    return f'admitted/{key[:2]}/{key}.json'


def acquire(ref=REF):
    run_id, attempt = os.environ['GITHUB_RUN_ID'], os.environ['GITHUB_RUN_ATTEMPT']
    try:
        sha = s.api('git/ref/' + ref)['object']['sha']
    except urllib.error.HTTPError as exc:
        if exc.code != 404:
            raise
        sha = None
    if sha:
        commit = s.api('git/commits/' + sha)
        state = json.loads(commit['message'])
        # A rerun must not reuse outputs from a still-active attempt.
        owner_path = 'actions/runs/' + state['run_id']
        if state['run_id'] == run_id and int(state['run_attempt']) < int(attempt):
            owner_path += '/attempts/' + state['run_attempt']
        owner = s.api(owner_path)
        if owner['status'] != 'completed':
            return None
        tree = commit['tree']['sha']
    else:
        state = {'schema_version': 1, 'page': 1, 'offset': 0}
        tree = s.api('git/trees', {'tree': [{'path': 'queue.json', 'mode': '100644', 'type': 'blob', 'content': '{}\n'}]})['sha']
    state.update(run_id=run_id, run_attempt=attempt)
    lease = Lease(sha, state, tree, ref)
    try:
        # Concurrent contenders create sibling commits. Only one can fast-forward.
        lease.save()
    except urllib.error.HTTPError as exc:
        if exc.code in [409, 422]:
            return None
        raise
    return lease


# A requeue (task 8b170a8c): a maintainer removes the one admission record of an issue whose check ended for a reason on OUR
# side, so that the next scan admits it again. Nothing here runs by itself: the scan never retries (reservations stay, see
# Lease.reserve), and the requeue is a dispatched job (submissions.yml, requeue_issue). Which receipts qualify is ONE rule,
# verdicts.no_verdict: the site importer's rule for a result without a verdict on the proof (decisions setup, timeout, chain).
# One more case, for the requeue only: a nanoda stack overflow (verifier#226, verdicts.nanoda_stack_candidate).
SITE_TRUST_URL = 'https://raw.githubusercontent.com/bigospeedrun/site/main/data/direct-trust.json'
MAX_TRUST_BYTES = 16 * 1024 * 1024
REASON = re.compile(r'[ -~]{1,200}')
RECEIPT_PAGES = 5


class Refused(Exception):
    """A requeue that the checks refuse. The message says why; nothing was changed."""


def untrusted_path(path):
    # A copy of the site's rule: untrusted_path() in data/direct_refresh.py of the site repository (the verifier cannot import the
    # site; tests/test_queue_security.py pins the three cases). No verifier script or workflow reads these paths.
    return path.startswith('submissions/') or path == 'auto-research.md' or path.startswith('auto-research/')


def controller_blobs(sha, root='.'):
    """{path: {sha, mode}} of the verifier commit, as the site importer lists it (git ls-tree -r, without the untrusted paths)."""
    out = subprocess.run(['git', '-C', str(root), 'ls-tree', '-r', '-z', sha], capture_output=True, check=True).stdout
    blobs = {}
    for record in out.split(b'\0'):
        if not record:
            continue
        meta, path = record.split(b'\t', 1)
        mode, kind, blob = meta.decode().split(' ')
        path = path.decode()
        if kind != 'tree' and not untrusted_path(path):
            blobs[path] = {'sha': blob, 'mode': mode}
    return blobs


def site_trust():
    """data/direct-trust.json of the public site repository. No token goes to this request."""
    request = urllib.request.Request(SITE_TRUST_URL, headers={'User-Agent': 'bigospeedrun-verifier-requeue'})
    with urllib.request.urlopen(request, timeout=60) as response:
        raw = response.read(MAX_TRUST_BYTES + 1)
    if len(raw) > MAX_TRUST_BYTES:
        raise ValueError('The site trust file is too large')
    return json.loads(raw)


def site_trusts(blobs, trust):
    """True when the importer would accept a receipt of a verifier commit with these controller blobs."""
    return blobs in [trust['controller_blobs'], *trust.get('previous_controller_blobs', {}).values()]


def old_receipt(run_id, attempt, number):
    """The FINAL receipt of the run attempt that the admission record names. The Lean-stage receipt (-lean) is a checkpoint, not
    the outcome of the run, so it is never read here."""
    receipt = json.loads(old_files(run_id, attempt, number)['receipt.json'])
    if not isinstance(receipt, dict):
        raise Refused('the old receipt is not an object')
    return receipt


def old_nanoda_log(run_id, attempt, number):
    """The part of the old final artifact's nanoda.log that the last nanoda attempt wrote (after the last 'VERIFIER nanoda:' line)."""
    raw = old_files(run_id, attempt, number).get('nanoda.log')
    if raw is None:
        raise Refused(f'the old run {run_id} has no nanoda log')
    text = raw.decode(errors='replace')
    marker = text.rfind('\nVERIFIER nanoda: ')
    return text if marker < 0 else text[text.index('\n', marker + 1) + 1:]


def old_files(run_id, attempt, number):
    """The files of the FINAL receipt artifact of that run attempt."""
    import pr_submissions as pr
    base = f'verifier-receipt-and-logs-{run_id}-{attempt}-{number}'
    found = {}
    for page in range(1, RECEIPT_PAGES + 1):
        got = s.api(f'actions/runs/{run_id}/artifacts?per_page=100&page={page}')['artifacts']
        found.update({a['name']: a for a in got if not a.get('expired')})
        if len(got) < 100:
            break
    else:
        raise Refused('too many artifacts in the old run to read')
    artifact = found.get(base)
    if artifact is None:
        raise Refused(f'the old run {run_id} has no final receipt artifact (expired, or the run ended before the final upload)')
    return pr.read_archive(pr.api(f"actions/artifacts/{artifact['id']}/zip", raw=True), artifact)


def requeue(number, reason, sha, actor, ref=REF):
    """Remove the one admission record of issue `number`, once per issue per verifier commit sha, and say so in the lease tree.
    Refused (nothing changed) unless: the site trust file lists this verifier commit; the issue is an open submission issue;
    the lease is free; the issue has a record; the old run's receipt ended without a verdict (verdicts.no_verdict); the old run used another
    verifier commit (our code changed since); and this issue has not been requeued at this commit. Returns the guard entry."""
    if not re.fullmatch(r'[1-9][0-9]{0,8}', str(number)):
        raise Refused('the issue number is not a number')
    if not REASON.fullmatch(reason or ''):
        raise Refused('the reason must be 1 to 200 printable ASCII characters')
    if not re.fullmatch('[0-9a-f]{40}', sha or ''):
        raise Refused('the verifier commit is not a full sha')
    if not site_trusts(controller_blobs(sha), site_trust()):
        raise Refused(f'the site trust file does not list the controller blobs of verifier commit {sha[:7]}: push the site trust commit '
                      f'first, or the importer rejects the receipt of the rerun')
    issue = s.api(f'issues/{number}')
    if s.TEST_LABEL in [label.get('name') for label in issue.get('labels') or [] if isinstance(label, dict)]:
        raise Refused('a maintainer test issue runs only by dispatch (smoke)')
    try:
        submission = s.issue_input(issue)
    except ValueError as error:
        raise Refused(f'the issue form is invalid ({type(error).__name__}); the issue text is not repeated here') from error
    if submission is None or submission['problem'] in s.CLOSED:
        raise Refused('not an open submission issue of an open problem (a PR, a closed issue and an edited form have other paths)')
    key = admission_key(s.issue_request(issue, submission))
    lease = acquire(ref)
    if lease is None:
        raise Refused(f'lease held by run {holder(ref)}; dispatch again when that run is completed')
    record = lease.record(key)
    if record is None:
        raise Refused('this version of the issue has no admission record: the next scan admits it by itself')
    run_id, attempt = str(record['run_id']), str(record['run_attempt'])
    if not re.fullmatch(r'[1-9][0-9]{0,19}', run_id) or not re.fullmatch(r'[1-9][0-9]{0,4}', attempt):
        raise Refused('the admission record names no valid run')
    receipt = old_receipt(run_id, attempt, number)
    decision = verdicts.no_verdict(receipt)
    # verifier#226 (Lead, 2026-11-26): a run whose advisory nanoda check overflowed its worker stack (Lean kernel and axiom audit
    # passed) is held for review only by a limit of ours. It is requeued once per verifier commit, like a timeout: the rerun
    # starts nanoda with a larger stack. The overflow is read from the last nanoda attempt's log (verdicts.nanoda_stack_overflow).
    if decision is None and verdicts.nanoda_stack_candidate(receipt) and verdicts.nanoda_stack_overflow(
            'exit-code', old_nanoda_log(run_id, attempt, number)):
        decision = 'nanoda_stack'
    if decision is None:
        raise Refused(f"the receipt of the old run {run_id} (status {str(receipt.get('status'))[:30]!r}) is a verdict on the proof or a stop that is not "
                      f"'no verdict': only a timeout, a check chain stop, a setup failure or a nanoda stack overflow on our side is requeued")
    old_commit = s.api(f'actions/runs/{run_id}')['head_sha']
    if old_commit == sha:
        raise Refused(f'the old run {run_id} already ran on this verifier commit: nothing changed on our side')
    guard = f'requeued/{number}-{sha[:12]}.json'
    if lease.item(guard) is not None:
        raise Refused(f'issue {number} was already requeued at verifier commit {sha[:7]}')
    entry = {'schema_version': 1, 'issue': int(number), 'key': key, 'old_run': run_id, 'old_attempt': attempt, 'old_decision': decision,
             'old_verifier_commit': old_commit, 'new_verifier_commit': sha, 'reason': reason, 'actor': actor or None,
             'run_id': os.environ.get('GITHUB_RUN_ID')}
    lease.tree = s.api('git/trees', {'base_tree': lease.tree, 'tree': [
        {'path': admission_path(key), 'mode': '100644', 'type': 'blob', 'sha': None},
        {'path': guard, 'mode': '100644', 'type': 'blob', 'content': s.canonical(entry) + '\n'}]})['sha']
    lease.save()  # force: false, so a lost race fails and changes nothing
    if lease.item(admission_path(key)) is not None or lease.item(guard) is None:
        raise RuntimeError('requeue read-back failed: the admission record is still there, or the guard file is missing')
    return entry


def assert_owner(ref=REF):
    sha = s.api('git/ref/' + ref)['object']['sha']
    state = json.loads(s.api('git/commits/' + sha)['message'])
    if (state['run_id'], state['run_attempt']) != (os.environ['GITHUB_RUN_ID'], os.environ['GITHUB_RUN_ATTEMPT']):
        raise ValueError('Batch lease belongs to another run/attempt; rerun the whole workflow')


def holder(ref=REF):
    sha = s.api('git/ref/' + ref)['object']['sha']
    return json.loads(s.api('git/commits/' + sha)['message'])['run_id']


def main():
    lease = acquire()
    with open(os.environ['GITHUB_OUTPUT'], 'a') as out:
        out.write('admitted=' + str(lease is not None).lower() + '\n')
    # A run that a person dispatched must not end green without a check. Scheduled polls skip quietly.
    if lease is None and os.environ.get('GITHUB_EVENT_NAME') == 'workflow_dispatch':
        print(f'::error::not admitted: lease held by run {holder()}; dispatch again when that run is completed')
        raise SystemExit(1)


def requeue_main():
    """The dispatched job: the values come from the environment. A refusal exits 1 with one printable log line and no workflow command."""
    try:
        entry = requeue(os.environ.get('REQUEUE_ISSUE', ''), os.environ.get('REQUEUE_REASON', ''), os.environ.get('GITHUB_SHA', ''),
                        os.environ.get('GITHUB_ACTOR', ''))
    except Refused as error:
        # The message can hold a little data of the issue or the receipt: no newline, no "::".
        print('::error::requeue refused: ' + re.sub(r'[^ -~]', ' ', str(error)).replace('::', ': :')[:400])
        raise SystemExit(1)
    print(f"requeued issue {entry['issue']}: removed its admission record (old run {entry['old_run']}, {entry['old_decision']}, "
          f"verifier {entry['old_verifier_commit'][:7]} -> {entry['new_verifier_commit'][:7]}); the next scan admits it.")


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('phase', choices=['acquire', 'check', 'requeue'])
    args = parser.parse_args()
    if args.phase == 'requeue':
        requeue_main()
    else:
        assert_owner() if args.phase == 'check' else main()
