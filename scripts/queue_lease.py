"""Default-branch admission lease. Fork read tokens cannot change this ref."""
import argparse
import base64
import hashlib
import json
import os
import urllib.error
from pathlib import Path
import submissions as s

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

    def admitted(self, key):
        path = admission_path(key)
        try:
            item = s.api(f'contents/{path}?ref={self.sha}')
        except urllib.error.HTTPError as exc:
            if exc.code == 404:
                return False
            raise
        if item.get('type') != 'file' or not 0 < item.get('size', 0) <= 1024:
            raise ValueError('Invalid admission state record')
        raw = base64.b64decode(item['content'], validate=False)
        if len(raw) > 1024:
            raise ValueError('Oversized admission state record')
        value = json.loads(raw)
        if value.get('schema_version') != 1 or value.get('key') != key:
            raise ValueError('Mismatched admission state record')
        return True

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


def assert_owner(ref=REF):
    sha = s.api('git/ref/' + ref)['object']['sha']
    state = json.loads(s.api('git/commits/' + sha)['message'])
    if (state['run_id'], state['run_attempt']) != (os.environ['GITHUB_RUN_ID'], os.environ['GITHUB_RUN_ATTEMPT']):
        raise ValueError('Batch lease belongs to another run/attempt; rerun the whole workflow')


def main():
    lease = acquire()
    with open(os.environ['GITHUB_OUTPUT'], 'a') as out:
        out.write('admitted=' + str(lease is not None).lower() + '\n')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('phase', choices=['acquire', 'check'])
    args = parser.parse_args()
    assert_owner() if args.phase == 'check' else main()
