"""Receipt admission policy, separate from process or workflow completion."""
import re
import html

AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def kernel_outcome(kernel, code, output, systemd_result='', guard_stop=None):
    required = ['Lean default kernel accepts the solution', 'Your solution is okay!']
    if kernel == 'nanoda':
        required += ['nanoda kernel accepts the solution']
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
    if kernel == 'lean' and code != 0 and 'error: build failed' in output and diagnostics:
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
    if nanoda.get('status') == 'incomplete' and nanoda.get('reason') in ['out_of_memory', 'timeout', 'disk_limit', 'total_deadline']:
        return 'passed', 'lean_and_axiom_passed_nanoda_incomplete'
    return 'pending_review', 'nanoda_ambiguous'


def compile_error_comment(receipt):
    lean = receipt.get('kernels', {}).get('lean', {})
    if lean.get('reason') == 'statement_mismatch':
        # The name was matched by kernel_outcome's pattern; check it again, as the receipt is read back from disk.
        name = str(lean.get('theorem', ''))
        name = name if re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.]{0,99}', name) else 'the theorem'
        return (f"\n\nThe proof's theorem statement does not match the challenge: `{name}`. The statements are compared as"
                ' written, so write the bound in the theorem as the same reduced fraction as in this submission.')
    if lean.get('status') != 'rejected' or lean.get('reason') != 'lean_compile_error':
        return ''
    # A diagnostic is untrusted text: one bounded quote, no mentions or markup.
    text = ' '.join(str(lean.get('diagnostic', 'Lean compilation failed')).split())[:500]
    text = html.escape(text).replace('@', '&#64;').replace('`', '&#96;').replace('[', '&#91;').replace(']', '&#93;')
    return '\n\nCompile error:\n\n> ' + text


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
