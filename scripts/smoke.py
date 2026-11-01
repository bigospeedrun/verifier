"""Maintainer-dispatched, non-importable smokes: the fixed historical DFT proof, the pinned average-sensitivity
proof that had to pass before that problem opened (submissions.CLOSED), the Catalan split-build smoke and the Subset
Sum smoke. The Catalan and Subset Sum smokes run only on a maintainer test issue (label 'test') whose form is their
fixture, and they post nothing."""
import json
import os
from pathlib import Path
import re
import submissions as s

PIN = '837dc3130adc79f7b7ab4ddd56c15576bbd766b0'
REPO = 'https://github.com/chafreaky/wht-power-saving-lean'
BOUND = '47171/62500000'
TAG = 'dft-837dc31-v1'
# Anchen0823's public proof of BigOSpeedrun.AverageSensitivity.Bound (1881/500) (verifier PR #15), issue route only.
AS_FIXTURE = ('average-sensitivity', '1881/500', 'https://github.com/Anchen-AI4Math/average-sensitivity-lean',
              'cb8c10538e613329be16f9a949d0d75a4c7c67f0')
AS_TAG = 'avgsens-cb8c105-v1'
# Split-build smoke (docs/execution.md): Sean Litsey's Catalan proof in the Submission layout, bound 1091, issue
# route only. A test_only artifact excludes the claim of its issue on the site, so only a maintainer test issue may carry it.
CATALAN_FIXTURE = ('catalan', '1091', 'https://github.com/bigospeedrun/verifier-smoke-catalan',
                   'a3d48494df743e8dbf2dd5acb70dbe27759069e0')
CATALAN_TAG = 'catalan-a3d4849-split-v1'
# The Subset Sum smoke that must pass before that problem opens (Lead, 2026-11-01): darkhipo's public proof of the
# bound 3/4 (verifier issue #94), cloned from its own repository as the issue source and never copied (it has no
# license). Issue route only. 3/4 is above the classic bound 1/2, so this proof gives no row on the site. The pin is
# 6c06520, not 5d6d38f of the issue: the same 24 source files, without 152 tracked .lake build files (the verifier
# stages only the Lean sources of the source roots, so those files were never used; the clean tree is the fixture).
SS_FIXTURE = ('subset-sum', '3/4', 'https://github.com/darkhipo/subset-sum-mitm',
              '6c0652068fe17f08ce0087e424a4a8b98bd2664b')
SS_TAG = 'subset-sum-6c06520-v1'
# Smokes that post nothing and run only on a maintainer test issue.
SILENT = {CATALAN_TAG: CATALAN_FIXTURE, SS_TAG: SS_FIXTURE}


def fixture(sub):
    return (sub.get('problem'), sub.get('bound'), sub.get('repo_url'), sub.get('commit'))


def active(selected):
    sub = selected.get('submission', {})
    for tag, pinned in [(AS_TAG, AS_FIXTURE), *SILENT.items()]:
        if selected.get('test_only') is True and selected.get('live_smoke') == tag:
            return (selected.get('route') != 'pull_request' and fixture(sub) == pinned
                    and 'entrypoint' not in sub and 'source_subdir' not in sub)
    if selected.get('test_only') is not True or selected.get('live_smoke') != TAG:
        return False
    if sub.get('problem') != 'dft' or sub.get('bound') != BOUND:
        return False
    if selected.get('route') == 'pull_request':
        return bool(re.fullmatch(r'submissions/dft/[a-z0-9-]+-smoke-dft-837dc31', selected.get('source_subdir', '')))
    return sub.get('repo_url') == REPO and sub.get('commit') == PIN and sub.get('entrypoint') == 'dft233'


def issue_submission(sub):
    if fixture(sub) in [AS_FIXTURE, *SILENT.values()]:
        return s.validate_submission(sub)
    if (sub['problem'], sub['bound'], sub['repo_url'], sub['commit']) != ('dft', BOUND, REPO, PIN):
        raise ValueError('Smoke issue must pin the fixed historical DFT fixture')
    return s.validate_submission(dict(sub, entrypoint='dft233'))


def silent(selected):
    """The Catalan and Subset Sum smokes: no result comment, no Lean checkpoint comment, no label."""
    return active(selected) and selected.get('live_smoke') in SILENT


def requested():
    if os.environ.get('BOS_SMOKE_DISPATCH') != '1' or os.environ.get('GITHUB_EVENT_NAME') != 'workflow_dispatch':
        return None
    event = json.loads(Path(os.environ['GITHUB_EVENT_PATH']).read_text())
    inputs = event.get('inputs', {})
    return inputs if inputs.get('smoke_route', 'none') != 'none' else None


def dispatch(lease):
    inputs = requested()
    if inputs is None:
        return False
    route = inputs['smoke_route']
    number = inputs.get('smoke_number', '')
    if route not in ['issue', 'pull_request'] or not re.fullmatch('[1-9][0-9]*', number):
        raise ValueError('Smoke requires a route and submission number')
    tag = TAG
    if route == 'issue':
        issue = s.api(f'issues/{number}')
        sub = issue_submission(s.issue_input(issue))
        selected = s.issue_request(issue, sub)
        login = selected['issue_submitter_login']
    else:
        import pr_submissions as p
        pr = p.api(f'pulls/{number}')
        selected = p.inspect_pr(pr)
        selected.update(verifier_commit=os.environ['GITHUB_SHA'], gate='ready')
        login = selected['pr_submitter_login']
    if route == 'issue' and fixture(selected['submission']) == AS_FIXTURE:
        tag = AS_TAG
    silent_tag = next((name for name, pinned in SILENT.items() if fixture(selected['submission']) == pinned), None)
    if route == 'issue' and silent_tag:
        tag = silent_tag
        # Only a maintainer test issue: the label needs triage rights, and the acknowledgement pass skips it.
        # Not author_association: the job token sees a private org member as CONTRIBUTOR (issue #68, 2026-10-27).
        # The dispatching maintainer must be the issue's author: never another person's issue.
        labels = [label.get('name') for label in issue.get('labels') or [] if isinstance(label, dict)]
        actor = os.environ.get('GITHUB_ACTOR', '').lower()
        if 'test' not in labels or not actor or (issue.get('user') or {}).get('login', '').lower() != actor:
            raise ValueError('This smoke requires a maintainer test issue (label test)')
    selected.update(test_only=True, live_smoke=tag, lease_kind="smoke",
                    record_gate={'test_only': True, 'reason': 'authorized fixed-pin smoke; record gate bypassed'})
    if not active(selected):
        raise ValueError('Smoke request is outside the fixed test scope')
    # Explicit maintainer dispatch may repeat the fixture; automated scans cannot.
    Path('requests').mkdir(exist_ok=True)
    Path(f'requests/{number}.json').write_text(s.canonical(selected)+'\n')
    s.selection_outputs([s.matrix_entry(int(number), login.lower(), route, selected['submission'])])
    return True
