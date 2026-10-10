"""Receipt admission policy, separate from process or workflow completion."""
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
    if kernel == 'nanoda' and code != 0 and 'Nanoda kernel rejected the solution' in output and 'assertion failed: self.def_eq(u, v)' in output:
        return {'status': 'rejected', 'reason': 'nanoda_type_equality_rejection'}
    if kernel == 'lean' and code != 0 and 'Lean default kernel rejects the solution' in output:
        return {'status': 'rejected', 'reason': 'lean_kernel_rejection'}
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
