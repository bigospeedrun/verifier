"""Maintainer-dispatched, non-importable smokes: the fixed historical DFT proof, the pinned average-sensitivity
proof that had to pass before that problem opened (submissions.CLOSED), the Catalan split-build smoke, the Subset
Sum smoke and the Snaky statement-mismatch runs. These silent smokes run only on a maintainer test issue (label
'test') whose form is their fixture, and they post nothing."""
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
# license). Issue route only. The smoke is test_only, so it gives no row on the site. The pin is
# 8b105f0, not 5d6d38f of the issue: 6c06520 removed 152 tracked .lake build files (never staged), and 8b105f0 adds
# 'set_option autoImplicit true' to 16 modules (the smoke of 6c06520, run 41345507330, failed on autoImplicit = false).
SS_FIXTURE = ('subset-sum', '3/4', 'https://github.com/darkhipo/subset-sum-mitm',
              '8b105f01848fc0e370abfa3a23ed5c3de463f321')
SS_TAG = 'subset-sum-8b105f0-v1'
# Snaky runs that must FAIL before that problem opens (Lead, 2026-11-02, verifier #106): our own repository, proofs
# by sorry. Comparator compares the statement before it checks axioms, so the control (an exact statement copy) must
# fail on sorryAx, and each mutation of the copy, or the bound 19 for the theorem about 20, must fail as
# statement_mismatch.
SNAKY_REPO = 'https://github.com/bigospeedrun/verifier-smoke-snaky'
SNAKY_CONTROL = 'c89f80904e29433fa97449849e6df017b790a2fd'
SNAKY_MUTATIONS = {
    'snaky-control-c89f809-v1': ('snaky', '20', SNAKY_REPO, SNAKY_CONTROL),
    'snaky-m1-bound19-c89f809-v1': ('snaky', '19', SNAKY_REPO, SNAKY_CONTROL),
    'snaky-m2-cell-eca2430-v1': ('snaky', '20', SNAKY_REPO, 'eca2430c189ae50eb0eaf514d8cd43dee33fbd50'),
    'snaky-m3-symmetry-73041ba-v1': ('snaky', '20', SNAKY_REPO, '73041babbfd876eda749055ce15e31f75cb97dbe'),
    'snaky-m4-freshness-299e232-v1': ('snaky', '20', SNAKY_REPO, '299e232db1c9d5b5766df87b6d581003224540e9'),
    'snaky-m5-legality-9ddfaee-v1': ('snaky', '20', SNAKY_REPO, '9ddfaeef790579437b716529586eec3fcfdefaee'),
}
# The Snaky smoke that must PASS before that problem opens (Lead, 2026-11-02): darkhipo's public proof of the bound 20
# (verifier issue #106, posted 2026-11-02), cloned from its own repository (Apache-2.0) as the issue source. Issue route
# only. Its Submission/SnakyStatement.lean is a byte copy of the challenge (sha256 49e630b3).
SNAKY_FIXTURE = ('snaky', '20', 'https://github.com/darkhipo/snaky-twenty', 'f6248dc39a05a6c5665240d860d2dbb95db707d9')
SNAKY_TAG = 'snaky-f6248dc-v1'
# The Heilbronn runs before that problem opens (Lead, 2026-11-03, verifier #105), all on our own repository. The smoke
# must PASS: the classical saving 0 from bound_zero of challenges/heilbronn-triangle/Validation.lean. The public form
# refuses 0 (submissions.ZERO_REFUSED); only this pinned smoke reads it. The control (an exact statement copy, the
# saving 1/50893237 by sorry) must fail on sorryAx; each mutation must fail at Comparator's compare step
# (statement_mismatch): the bound 1/50893238 for the theorem about 1/50893237, the area divided by 3, the square
# [0,1] x [0,2], the condition 0 < c removed, the distinctness q != r removed.
HB_REPO = 'https://github.com/bigospeedrun/verifier-smoke-heilbronn'
HB_CONTROL = 'c471bc6115390c4513a6e8e74379d5aedc08bb88'
HB_FIXTURE = ('heilbronn-triangle', '0', HB_REPO, '42a4e7a05939129ed8802f1d2030ca110ca2ffb5')
HB_TAG = 'heilbronn-42a4e7a-v1'
HB_MUTATIONS = {
    'heilbronn-control-c471bc6-v1': ('heilbronn-triangle', '1/50893237', HB_REPO, HB_CONTROL),
    'heilbronn-m1-bound-c471bc6-v1': ('heilbronn-triangle', '1/50893238', HB_REPO, HB_CONTROL),
    'heilbronn-m2-area-c869f25-v1': ('heilbronn-triangle', '1/50893237', HB_REPO, 'c869f250b78b0460cee8e3744115ba053f052aac'),
    'heilbronn-m3-square-27734ae-v1': ('heilbronn-triangle', '1/50893237', HB_REPO, '27734ae9bad1351ca0acbfa81c2d0906815c94f0'),
    'heilbronn-m4-constant-6c77d88-v1': ('heilbronn-triangle', '1/50893237', HB_REPO, '6c77d88ec092c7e4d8e4e3d1c31ac67758da341f'),
    'heilbronn-m5-distinct-9a86923-v1': ('heilbronn-triangle', '1/50893237', HB_REPO, '9a8692368d3de6ec205c0eac37192a51b253a7d0'),
}
# The directed SSSP runs before that problem opens (Nil's GO, 2026-11-03), all on our own repository
# bigospeedrun/sssp-lean-scratch, one branch per case (Lead, 2026-11-03). The smoke must PASS: Race.bound for the C-HD
# row from the fork's chd_exact_within (staged as the pinned solution dependency) and our bridge. The control (an exact
# statement copy, Race.bound by sorry) must fail on sorryAx. Each mutation must fail at Comparator's compare step
# (statement_mismatch): the edge exponent b = 4/5 or the time exponent 5/6 for the theorem about 3/4 and 11/12, the cap
# without its outer floor, the fallback only above the cap, P.Exact removed.
SSSP_REPO = 'https://github.com/bigospeedrun/sssp-lean-scratch'
SSSP_BOUND = 'n log^3/4 ; n log^11/12'
SSSP_CONTROL = '5238e61d93dc750d8407a24264840fdad387f78c'
SSSP_FIXTURE = ('directed-sssp', SSSP_BOUND, SSSP_REPO, '98919233966fa6196cf67639c1eee2b2496d26b6')
SSSP_TAG = 'sssp-9891923-v1'
SSSP_MUTATIONS = {
    'sssp-control-5238e61-v1': ('directed-sssp', SSSP_BOUND, SSSP_REPO, SSSP_CONTROL),
    'sssp-m1-cap-floor-9be59eb-v1': ('directed-sssp', SSSP_BOUND, SSSP_REPO, '9be59eb30eb3751de724b85f9da985d4bcf841f2'),
    'sssp-m2-b-5238e61-v1': ('directed-sssp', 'n log^4/5 ; n log^11/12', SSSP_REPO, SSSP_CONTROL),
    'sssp-m3-time-5238e61-v1': ('directed-sssp', 'n log^3/4 ; n log^5/6', SSSP_REPO, SSSP_CONTROL),
    'sssp-m4-fallback-f06285b-v1': ('directed-sssp', SSSP_BOUND, SSSP_REPO, 'f06285b90fc64b33cf0cc9541cc7d066c9cf5e62'),
    'sssp-m5-exact-a922982-v1': ('directed-sssp', SSSP_BOUND, SSSP_REPO, 'a9229827f0a9327e8aec8bf61e3dc343481818e4'),
}
# The prime gaps runs before that problem opens (Lead GO 2026-11-06, task cbea6e9e, verifier #148), all on our own
# repository bigospeedrun/verifier-smoke-prime-gaps, one branch per case. The smoke must PASS: Race.bound for 246 from
# darkhipo's composition (darkhipo/prime-gaps-246-lean@ac0eb01b: Axiom Math's PrimeGapsLib and Jonas Whidden's
# bombieri-vinogradov) moved into the Submission layout (branch main), with the pinned PNT+ fork and LeanArchitect as
# solution dependencies. The control (an exact statement copy, Race.bound by sorry) must fail on sorryAx. Each
# mutation must fail at Comparator's compare step (statement_mismatch): the bound 245 for the theorem about 246, < for
# ≤, ∀ᶠ for ∃ᶠ, the gap over two steps (m + 2), the general Prime for Nat.Prime.
PG_REPO = 'https://github.com/bigospeedrun/verifier-smoke-prime-gaps'
PG_CONTROL = '1b31b82d168a32b9484ad947d2d2aa5eb52efce8'
PG_FIXTURE = ('prime-gaps', '246', PG_REPO, 'abc6a6eb2d4fa59a3e113631c0cad28ef4c5d9cd')
PG_TAG = 'prime-gaps-abc6a6e-v1'
PG_MUTATIONS = {
    'prime-gaps-control-1b31b82-v1': ('prime-gaps', '246', PG_REPO, PG_CONTROL),
    'prime-gaps-m1-bound245-1b31b82-v1': ('prime-gaps', '245', PG_REPO, PG_CONTROL),
    'prime-gaps-m2-strict-ff005c1-v1': ('prime-gaps', '246', PG_REPO, 'ff005c1eb5f6b88434e72a51941c61306415cb79'),
    'prime-gaps-m3-eventually-f707281-v1': ('prime-gaps', '246', PG_REPO, 'f70728128e83ad30ef0002ead8f51f3c511eb61c'),
    'prime-gaps-m4-two-steps-ce76e48-v1': ('prime-gaps', '246', PG_REPO, 'ce76e481a3b5aabea3773d93f4f62898bb44f835'),
    'prime-gaps-m5-prime-de38d4d-v1': ('prime-gaps', '246', PG_REPO, 'de38d4d0d862485d33fdb01f93cb8cef1639f45c'),
}
# The 3-SAT runs before that problem opens (Lead GO 2026-11-14, task 07840cc3, verifier #192), all on our own repository
# bigospeedrun/verifier-smoke-3sat, one branch per case. The smoke must PASS on the check chain, and its run is the
# memory measurement of the chain on free runners: Race.bound for 1/2 from OpenAI's exact_count_and_sat (openai/math
# 7ef5c0cc, the 3091 files of the import closure of OAI.Algorithms.SubexponentialSAT.Main, byte copies under OAI/) and
# our bridge under Submission/ (branch main). The control (the statement over a copy of OpenAI's definitions,
# Race.bound by sorry) must fail on sorryAx. Each mutation must fail at Comparator's compare step
# (statement_mismatch): the bound 3/5 for the theorem about 1/2, width 2 for 3, a one-sided verdict (→ for ↔), one
# machine per ε, and Clause.eval with ∀ for ∃ (a changed OpenAI definition).
SAT_REPO = 'https://github.com/bigospeedrun/verifier-smoke-3sat'
SAT_CONTROL = 'a11e20677fe5c49d4d41ff5498c813c45fd80b96'
SAT_FIXTURE = ('3sat', '1/2', SAT_REPO, 'f76c9973f68108afbd0a24e50512d0cb0370fe77')
SAT_TAG = '3sat-f76c997-v1'
SAT_MUTATIONS = {
    '3sat-control-a11e206-v1': ('3sat', '1/2', SAT_REPO, SAT_CONTROL),
    '3sat-m1-bound3-5-a11e206-v1': ('3sat', '3/5', SAT_REPO, SAT_CONTROL),
    '3sat-m2-width-e92f108-v1': ('3sat', '1/2', SAT_REPO, 'e92f108c4761355e401a4be4c9db8bb4244cdea9'),
    '3sat-m3-verdict-2639f4c-v1': ('3sat', '1/2', SAT_REPO, '2639f4c80640d30fd13510b46628fd6042230304'),
    '3sat-m4-uniform-1872c8e-v1': ('3sat', '1/2', SAT_REPO, '1872c8e1845e54d2f0c8f3a1a617b3bf7b7f26b3'),
    '3sat-m5-clause-667994f-v1': ('3sat', '1/2', SAT_REPO, '667994fa617c12dd3a1807d2b00b44cce3157c9d'),
}
# Smokes that post nothing and run only on a maintainer test issue.
SILENT = {CATALAN_TAG: CATALAN_FIXTURE, SS_TAG: SS_FIXTURE, SNAKY_TAG: SNAKY_FIXTURE, **SNAKY_MUTATIONS,
          HB_TAG: HB_FIXTURE, **HB_MUTATIONS, SSSP_TAG: SSSP_FIXTURE, **SSSP_MUTATIONS, PG_TAG: PG_FIXTURE, **PG_MUTATIONS,
          SAT_TAG: SAT_FIXTURE, **SAT_MUTATIONS}


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
    """The Catalan, Subset Sum, Snaky and Heilbronn smokes: no result comment, no Lean checkpoint comment, no label."""
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
        # smoke=True: only a pinned fixture passes issue_submission, so a bound of 0 elsewhere is still refused there.
        sub = issue_submission(s.issue_input(issue, smoke=True))
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
