"""Receipt admission policy, separate from process or workflow completion."""
import re

AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def kernel_outcome(kernel, code, output, systemd_result='', guard_stop=None):
    required = ['Lean default kernel accepts the solution', 'Your solution is okay!']
    if kernel == 'nanoda':
        required += ['nanoda kernel accepts the solution']
    if kernel in ['challenge', 'export']:
        # A chain's export units (chain.py): Comparator built and exported the challenge, or the solution; it ran no
        # comparison and no kernel. Their failures read like those of the Lean check.
        required = ['BOS export: wrote ' + ('challenge' if kernel == 'challenge' else 'solution')]
    if code == 0 and all(line.lower() in output.lower() for line in required):
        return {'status': 'passed', 'reason': 'comparator_acceptance'}
    # Resource evidence comes from the host service manager, never proof output.
    if guard_stop:
        return {'status': 'incomplete', 'reason': 'disk_limit'}
    if systemd_result in ['oom-kill', 'timeout']:
        return {'status': 'incomplete', 'reason': 'out_of_memory' if systemd_result == 'oom-kill' else 'timeout'}
    # A nonzero Lean build with a located elaboration/parser diagnostic is a
    # source failure. Host resource evidence above always takes precedence.
    diagnostics = re.findall(r"^error: ((?!(?:VerifierChallenge|VerifierAudit)\.lean:)[A-Za-z_][A-Za-z0-9_]*(?:/[A-Za-z_][A-Za-z0-9_]*)*\.lean:\d+:\d+: (?:Type mismatch|Application type mismatch|unsolved goals|Unknown identifier|Unknown constant|unknown identifier|unknown constant|unexpected token|unexpected end of input|Tactic|tactic|failed to synthesize|failed to compile definition|Invalid field)[^\n]*)", output, re.M)
    if kernel in ['lean', 'challenge', 'export'] and code != 0 and 'error: build failed' in output and diagnostics:
        return {'status': 'rejected', 'reason': 'lean_compile_error',
                'diagnostic': diagnostics[0][:500]}
    if kernel == 'nanoda' and code != 0 and 'Nanoda kernel rejected the solution' in output and 'assertion failed: self.def_eq(u, v)' in output:
        return {'status': 'rejected', 'reason': 'nanoda_type_equality_rejection'}
    if kernel == 'lean' and code != 0 and 'Lean default kernel rejects the solution' in output:
        return {'status': 'rejected', 'reason': 'lean_kernel_rejection'}
    # Comparator refuses a solution whose theorem states something else than the trusted challenge, for example
    # 37615398/10000000 against the reduced 18807699/5000000 the challenge states (issue #61, 2026-10-24). The status
    # stays pending_review as before; the reason only lets the result comment say why.
    mismatch = re.search(r"^uncaught exception: Challenge and solution theorem statement do not match: '([A-Za-z_][A-Za-z0-9_.]{0,99})'$", output, re.M)
    if kernel == 'lean' and code != 0 and mismatch:
        return {'status': 'pending_review', 'reason': 'statement_mismatch', 'theorem': mismatch.group(1)}
    # The same compare step refuses a definition that the theorem uses when it differs from the challenge's (Lead,
    # 2026-11-02: Snaky test run 41544953483 moved one cell of OAI.SnakyPrototype.snaky in the statement copy).
    changed = re.search(r"^uncaught exception: Const does not match between challenge and target '([A-Za-z_][A-Za-z0-9_.]{0,99})'$", output, re.M)
    if kernel == 'lean' and code != 0 and changed:
        return {'status': 'pending_review', 'reason': 'statement_mismatch', 'theorem': changed.group(1), 'mismatch': 'definition'}
    return {'status': 'pending_review', 'reason': 'ambiguous_failure' if code else 'missing_acceptance'}


def admission(receipt, names):
    audit = receipt.get('axiom_audit', {})
    reported = audit.get('reported_axioms', {})
    if audit.get('status') != 'passed' or set(reported) != set(names):
        return 'not_verified', 'axiom_audit_incomplete'
    if any(not isinstance(items, list) or any(not isinstance(x, str) or x not in AXIOMS for x in items) for items in reported.values()):
        return 'blocked', 'unpermitted_axiom'
    theorems = receipt.get('theorems', {})
    if set(theorems) != set(names) or any(theorems[n].get('reported_axioms') != reported[n] for n in names):
        return 'not_verified', 'theorem_axiom_mismatch'
    if receipt.get('kernels', {}).get('lean', {}).get('status') != 'passed':
        return 'not_verified', 'lean_not_passed'
    if any(receipt.get('theorems', {}).get(n, {}).get('lean_kernel') != 'passed' for n in names):
        return 'not_verified', 'theorem_lean_not_passed'
    nanoda = receipt.get('kernels', {}).get('nanoda', {})
    if nanoda.get('status') == 'rejected' or any(theorems[n].get('nanoda_kernel') == 'rejected' for n in names):
        return 'blocked', 'nanoda_rejected'
    if any(theorems[n].get('nanoda_kernel') != nanoda.get('status') for n in names):
        return 'pending_review', 'nanoda_theorem_mismatch'
    if receipt.get('verification_stage') == 'lean' and nanoda.get('status') == 'pending' and nanoda.get('reason') == 'advisory_queued':
        return 'passed', 'lean_and_axiom_passed_nanoda_pending'
    if nanoda.get('status') == 'passed':
        return 'passed', 'lean_and_axiom_passed'
    # not_run_chain: a chain (runner github-chain) runs no nanoda pass (chain.py); the Lead's design keeps nanoda advisory.
    if nanoda.get('status') == 'incomplete' and nanoda.get('reason') in ['out_of_memory', 'timeout', 'disk_limit', 'total_deadline', 'not_run_chain']:
        return 'passed', 'lean_and_axiom_passed_nanoda_incomplete'
    return 'pending_review', 'nanoda_ambiguous'


def compile_error_comment(receipt):
    lean = receipt.get('kernels', {}).get('lean', {})
    if lean.get('reason') == 'statement_mismatch':
        # The name was matched by kernel_outcome's pattern; check it again, as the receipt is read back from disk.
        name = str(lean.get('theorem', ''))
        name = name if re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.]{0,99}', name) else 'the theorem'
        if lean.get('mismatch') == 'definition':
            return (f"\n\nA definition that the theorem statement uses does not match the challenge: `{name}`. Copy the"
                    ' statement file of the challenge byte for byte, and do not change its definitions.')
        return (f"\n\nThe proof's theorem statement does not match the challenge: `{name}`. The statements are compared as"
                ' written, so write the bound in the theorem as the same reduced fraction as in this submission.')
    if lean.get('status') != 'rejected' or lean.get('reason') != 'lean_compile_error':
        return ''
    # A diagnostic is untrusted text: one bounded line in a code span, so GitHub renders no mention, link or markup in it.
    # The fence is longer than any backtick run in the text, so the text cannot close it (verifier#225: entities such as
    # &#96; read badly in the raw comment text).
    text = ' '.join(str(lean.get('diagnostic', 'Lean compilation failed')).split())[:500]
    # Defense in depth (Lead, 2026-11-26): the bot never pings anyone, even if the span fails. An entity shows as
    # written inside a code span, so @ becomes the full-width sign.
    text = text.replace('@', '\uff20')
    fence = '`' * (max((len(run) for run in re.findall(r'`+', text)), default=0) + 1)
    return f'\n\nCompile error:\n\n> {fence} {text} {fence}'


# Prepare errors that come from the submission itself (scripts/verifier.py): the same source fails the same way
# on every run, so its issue closes and the author opens a new one (verifier#89, 2026-10-30: a zip-only
# repository was left open as setup_failed with no reason). Any other setup failure can be temporary: it stays open.
SETUP_ERRORS = {
    'solution module is missing': 'the submission has no Submission.lean at the root of its source. The verifier reads Lean files only, not an archive',
    'unclosed block comment in source': 'a Lean file of the submission has a block comment that is not closed',
    'cyclic submission imports': 'the Lean files of the submission import each other in a cycle',
    'unsupported import header': 'a Lean file of the submission has an import header that the verifier does not accept',
    'submission imports a reserved verifier module': 'the submission imports a module name that the verifier reserves (VerifierChallenge or VerifierAudit)',
    'build order has an unmet local dependency': 'a Lean file of the submission imports a submission module that is not in it',
    'only regular Lean source files with ordinary module names are admitted': 'a Lean file of the submission is not a regular file or has no ordinary module name',
    'individual Lean source exceeds 20 MB': 'a Lean file of the submission is larger than 20 MB',
    'Lean source input exceeds 150 MB': 'the Lean source of the submission is larger than 150 MB in total',
}

KERNEL_REASONS = {
    'lean_compile_error': 'Lean did not compile the proof',
    'lean_kernel_rejection': "Lean's kernel rejected the proof",
    'statement_mismatch': "the proof's theorem statement does not match the challenge",
    'out_of_memory': 'the Lean check ran out of memory',
    'timeout': 'the Lean check ran out of time',
    'disk_limit': 'the Lean check reached its disk limit',
    'build_chain_cap': 'the Lean build did not finish within the job and hour limits of the check chain',
    'check_chain_cap': 'the kernel check did not finish within the job and hour limits of the check chain',
    'chain_coverage': 'the segments of the kernel check do not cover the proof once, in order',
    'no_segment_record': 'the kernel check of the check chain did not start. This is a verifier problem; a maintainer looks at it',
}

VERDICT_REASONS = {
    'statement_or_request_mismatch': 'the receipt does not match the request or the trusted statement',
    'axiom_audit_incomplete': 'the axiom audit did not complete',
    'theorem_axiom_mismatch': 'the axiom audit does not match the theorems',
}


def deterministic_setup_failure(receipt):
    return receipt.get('status') == 'setup_failed' and receipt.get('error') in SETUP_ERRORS


def reason_line(receipt, reason):
    """One line that says why a result is Not verified, from fixed text only: a receipt can hold untrusted text."""
    if receipt.get('status') == 'setup_failed':
        text = SETUP_ERRORS.get(receipt.get('error'), 'the verifier setup failed before the proof check. This can be a temporary problem; a maintainer looks at it')
    elif receipt.get('status') == 'timeout':
        text = 'the proof check ran out of time'
    else:
        text = KERNEL_REASONS.get(receipt.get('kernels', {}).get('lean', {}).get('reason')) or VERDICT_REASONS.get(reason)
        if text is None:
            code = reason if isinstance(reason, str) and re.fullmatch(r'[a-z_]{1,60}', reason) else 'unknown'
            text = f'verifier code {code}'
    return f'Reason: {text}.'


# The receipts that end WITHOUT a verdict on the proof (no_verdict): the rule of the site importer (data/direct_import.py of the site
# repository: setup_failed, timed_out, chain_stopped, which give its decisions 'setup', 'timeout' and 'chain'), copied here because the
# verifier cannot import the site. A requeue (queue_lease.py requeue, task 8b170a8c) is allowed only for these receipts. Keep both copies
# equal: the tests pin this one on real receipts (tests/fixtures/receipts), and the site's own tests pin the importer's on its fixtures.
CHAIN_CAP_REASONS = ('build_chain_cap', 'check_chain_cap')
CHAIN_FAULT_REASONS = ('chain_coverage', 'no_segment_record', 'no_segment_receipt', 'export_not_run')


def _dict(value):
    return value if isinstance(value, dict) else {}


def chain_receipt(receipt):
    return _dict(receipt.get('profile')).get('runner') == 'github-chain'


def proof_verdict(receipt):
    """A kernel rejected the proof, or the audit reported a forbidden axiom: a verdict, never a time or chain stop."""
    kernels = _dict(receipt.get('kernels'))
    reported = _dict(_dict(receipt.get('axiom_audit')).get('reported_axioms'))
    theorems = _dict(receipt.get('theorems'))
    rejected = (_dict(kernels.get('lean')).get('status') == 'rejected' or _dict(kernels.get('nanoda')).get('status') == 'rejected'
                or any(isinstance(t, dict) and 'rejected' in (t.get('lean_kernel'), t.get('nanoda_kernel')) for t in theorems.values()))
    forbidden = any(not isinstance(axioms, list) or any(not isinstance(a, str) or a not in AXIOMS for a in axioms) for axioms in reported.values())
    return rejected or forbidden


def chain_lean_stop(receipt, reasons):
    lean = _dict(_dict(receipt.get('kernels')).get('lean'))
    audit = _dict(receipt.get('axiom_audit'))
    return (chain_receipt(receipt) and lean.get('status') == 'incomplete' and lean.get('reason') in reasons
            and audit.get('status', 'not_started') in ('passed', 'not_started'))


def chain_stopped(receipt):
    """A check chain stopped for a verifier problem before a verdict."""
    return chain_lean_stop(receipt, CHAIN_FAULT_REASONS) and not proof_verdict(receipt)


def timed_out(receipt):
    """The verifier stopped the check for time: the receipt status is 'timeout' (the total deadline), or the Lean kernel is incomplete
    with the reason 'timeout'; after Lean passed, when the audit stopped for time; in a check chain, a cap reason or an audit stop."""
    kernels = _dict(receipt.get('kernels'))
    lean = _dict(kernels.get('lean'))
    audit = _dict(receipt.get('axiom_audit'))
    if lean.get('status') == 'passed':
        stopped = ((audit.get('status') == 'not_completed_or_rejected' and audit.get('systemd_result') == 'timeout' and not audit.get('guard_stop'))
                   or (audit.get('status') == 'not_started' and receipt.get('status') == 'timeout'))
    else:
        stopped = receipt.get('status') == 'timeout' or (lean.get('status') == 'incomplete' and lean.get('reason') == 'timeout')
        if chain_receipt(receipt) and lean.get('status') == 'incomplete' and lean.get('reason') in CHAIN_CAP_REASONS:
            stopped = chain_lean_stop(receipt, CHAIN_CAP_REASONS)
        export = _dict(receipt.get('chain_export'))
        if chain_receipt(receipt) and lean.get('status') == 'not_started' and export.get('status') == 'passed':
            stopped = ((audit.get('status') == 'not_completed_or_rejected' and audit.get('systemd_result') == 'timeout'
                        and not audit.get('guard_stop')) or audit.get('status') == 'not_started')
    return stopped and not proof_verdict(receipt)


def setup_failed(receipt):
    """The verifier failed before any proof check, and not for a fault of the submission (SETUP_ERRORS): our failure, not a verdict."""
    kernels = _dict(receipt.get('kernels'))
    return (receipt.get('status') == 'setup_failed' and receipt.get('error') not in SETUP_ERRORS
            and _dict(kernels.get('lean')).get('status', 'not_started') == 'not_started'
            and _dict(receipt.get('axiom_audit')).get('status', 'not_started') == 'not_started'
            and _dict(kernels.get('nanoda')).get('status', 'not_started') in ('not_started', 'pending'))


def no_verdict(receipt):
    """'setup', 'timeout' or 'chain' when the receipt ends without a verdict on the proof (the importer's decisions of the same names, in
    its order), else None. A passed, rejected or otherwise decided receipt is never one."""
    if not isinstance(receipt, dict):
        return None
    if setup_failed(receipt):
        return 'setup'
    if timed_out(receipt):
        return 'timeout'
    if chain_stopped(receipt):
        return 'chain'
    return None
