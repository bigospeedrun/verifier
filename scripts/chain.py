#!/usr/bin/env python3
"""Trusted controller of a check chain (runner github-chain, docs/execution.md, Check chain). Never execute this file
from a submission.

A chain is a fixed graph of hosted jobs in one workflow run (submission-check.yml): build1..build4, export,
check1..check4 and final. Each build job continues the Lake build of the one before it (verifier.pack / unpack). The
export job writes the challenge and solution exports and runs the axiom audit; then it, and each check job after it,
runs one segment of the kernel check (Comparator --bos-check, patches/comparator-segmented-check.patch) until its own
deadline. The final job reads each job's receipt by the sha256 that the job wrote as a job output, checks that the
segments cover the walk once, in order, from one export, and writes the one receipt that the report job reads.

Credit: darkhipo (MultiAgency swarm, verifier PR #191, closed) proposed one merged Lean-stage receipt with the
provenance of the chain; the final receipt's `chain` field does this.
"""
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
import verifier as v
from verdicts import kernel_outcome

BUILD_LEGS = ['build1', 'build2', 'build3', 'build4']
CHECK_LEGS = ['check1', 'check2', 'check3', 'check4']
LEGS = BUILD_LEGS + ['export'] + CHECK_LEGS
# Caps a profile may lower (profile 'chain'): the jobs that the workflow declares, and the hours from the start of
# build1 after which no new job starts. queue_lease has no time expiry: a chain holds the queue for all its time.
MAX_HOURS = 30
EXPORT_ARTIFACT = v.ROOT / 'export-artifact'
EXPORT_FILES = {'solution': 'solution.export.zst', 'challenge': 'challenge.export.zst'}
EXPORT_MAX_BYTES = 8 * 1024**3
EXPORT_MAX_RAW_BYTES = 60 * 1024**3
# A segment starts only with at least this much time before the job's deadline; it keeps the last 3 minutes for
# its receipt (the comparator stops between two declarations).
SEGMENT_MIN_SECONDS = 20 * 60
SEGMENT_MARGIN_SECONDS = 3 * 60
SEGMENT_RECEIPT_MAX_BYTES = 64 * 1024
HASH_START = '00000000000006bb'  # Comparator/Segment.lean hashStart (1723) in hashHex form.
SHA256 = re.compile(r'[0-9a-f]{64}\Z')
HASH = re.compile(r'[0-9a-f]{16}\Z')


def caps(profile):
    """The profile's chain caps, refused when out of range (a profile is trusted, but a typo must not widen a cap)."""
    chain = profile.get('chain', {})
    if not isinstance(chain, dict) or set(chain) - {'max_build_jobs', 'max_check_jobs', 'max_hours'}:
        raise ValueError('chain must be an object with max_build_jobs, max_check_jobs and max_hours')
    result = {'max_build_jobs': chain.get('max_build_jobs', 1), 'max_check_jobs': chain.get('max_check_jobs', 1),
              'max_hours': chain.get('max_hours', MAX_HOURS)}
    for key, top in [('max_build_jobs', len(BUILD_LEGS)), ('max_check_jobs', len(CHECK_LEGS)), ('max_hours', MAX_HOURS)]:
        if type(result[key]) is not int or not 1 <= result[key] <= top:
            raise ValueError(f'chain {key} must be an integer from 1 to {top}')
    return result


def outputs(**values):
    if os.environ.get('GITHUB_OUTPUT'):
        with open(os.environ['GITHUB_OUTPUT'], 'a') as out:
            for key, value in values.items():
                out.write(f'{key}={value}\n')


def chain_started(data):
    """The start of build1 (its prepare), passed on by job outputs. build1 itself uses its own start."""
    if os.environ.get('BOS_CHAIN_LEG') == 'build1':
        return data.get('started_unix', time.time())
    value = os.environ.get('BOS_CHAIN_STARTED', '')
    if not re.fullmatch(r'[0-9]{9,11}(\.[0-9]{1,9})?', value):
        raise ValueError('BOS_CHAIN_STARTED must be a unix time')
    started = float(value)
    if not time.time() - (MAX_HOURS + 6) * 3600 <= started <= time.time():
        raise ValueError('BOS_CHAIN_STARTED is out of range')
    return started


def within_hours(started, profile):
    return time.time() - started < caps(profile)['max_hours'] * 3600


def build_state(data):
    """How the build of this job ended: done (Lake built the solution module), continue (the unit reached the job's
    deadline; Lake keeps each finished module), or stop with the outcome of the last attempt."""
    build = data.get('build')
    if not isinstance(build, dict) or not build.get('attempts'):
        return 'stop', {'status': 'incomplete', 'reason': 'build_not_run'}
    last = build['attempts'][-1]
    if last.get('exit_code') == 0 and last.get('systemd_result') == 'success':
        return 'done', None
    if last.get('guard_stop'):
        return 'stop', {'status': 'incomplete', 'reason': 'disk_limit'}
    if last.get('systemd_result') == 'timeout':
        return 'continue', None
    if last.get('systemd_result') == 'oom-kill':
        if last.get('lake_jobs', 1) > 1:
            return 'continue', None  # The deadline cut the back-off; the next job starts at this count.
        return 'stop', {'status': 'incomplete', 'reason': 'out_of_memory'}
    log = v.ART / 'build.log'
    text = log.read_text(errors='replace')[-4 * 1024**2:] if log.is_file() else ''
    return 'stop', kernel_outcome('lean', last.get('exit_code', 1), text, last.get('systemd_result', ''))


def take_export(name):
    """Move one export file out of the sandbox /tmp into control/export (read-only in every later unit)."""
    source = v.WORK / 'scratch' / f'{name}.export'
    st = os.lstat(source)
    if not v.stat.S_ISREG(st.st_mode) or st.st_nlink != 1:
        raise ValueError('the export is not a regular file')
    target = v.WORK / 'control/export' / f'{name}.export'
    target.parent.mkdir(exist_ok=True)
    os.rename(source, target)
    return target


def empty_folder(folder):
    """Remove everything in a folder (trusted; the sandbox's writable folders between two units)."""
    for child in folder.iterdir():
        if child.is_dir() and not child.is_symlink():
            shutil.rmtree(child)
        else:
            child.unlink()


def challenge():
    """The export job, before unpack: the challenge build and export in its own unit. No submission build file is on the
    machine yet (the build folder is the empty one from prepare), and the submission sources are not built: the
    challenge imports only Mathlib. The file then moves out of the sandbox /tmp, and the build folder and /tmp are
    emptied for unpack, so no later unit can change it (Lead, 2026-11-14)."""
    build = v.WORK / 'stage/.lake/build'
    if any(build.iterdir()):
        raise RuntimeError('the build folder is not the empty folder from prepare')
    v.verify(['challenge'])
    data = v.receipt()
    record = data['kernels'].pop('challenge', None)
    data['chain_challenge'] = record
    data['status'] = 'chain_export'
    v.save(data)
    if not record or record.get('status') != 'passed':
        raise RuntimeError('the challenge export failed')
    take_export('challenge')
    empty_folder(build)
    empty_folder(v.WORK / 'scratch')


def export():
    """The export job, after unpack: the solution build (Lake finds it up to date) and export, as in a normal check. The
    file moves out of the sandbox /tmp and /tmp is emptied before the axiom audit, which imports the submission modules
    (an `initialize` block runs on import), so the audit unit cannot change it (Integrations F1, 2026-11-14). Then the
    two export files, compressed, for the check jobs, and segment 0."""
    if not (v.WORK / 'control/export/challenge.export').is_file():
        raise RuntimeError('the challenge export of this job is missing')
    v.verify(['export'])
    data = v.receipt()
    record = data['kernels'].pop('export', None)
    data['chain_export'] = record
    data['status'] = 'chain_export'
    v.save(data)
    if not record or record.get('status') != 'passed':
        return
    take_export('solution')
    empty_folder(v.WORK / 'scratch')
    v.verify(['audit'])
    EXPORT_ARTIFACT.mkdir(exist_ok=True)
    pins = {}
    for name, file in EXPORT_FILES.items():
        target = v.WORK / 'control/export' / f'{name}.export'
        with target.open('rb') as src, (EXPORT_ARTIFACT / file).open('xb') as out:
            subprocess.run(v.ZSTD_PACK, stdin=src, stdout=out, check=True)
        if (EXPORT_ARTIFACT / file).stat().st_size > EXPORT_MAX_BYTES:
            raise ValueError('a compressed export exceeds EXPORT_MAX_BYTES')
        pins[name] = {'sha256': v.digest(EXPORT_ARTIFACT / file), 'bytes': target.stat().st_size,
                      'compressed_bytes': (EXPORT_ARTIFACT / file).stat().st_size}
    data = v.receipt(); data['chain_export']['files'] = pins; data['status'] = 'chain_export'; v.save(data)
    if data.get('axiom_audit', {}).get('status') != 'passed':
        return  # No admission without the audit (verdicts.admission): the chain stops here.
    segment(pins['solution']['sha256'], 0, HASH_START)


def restore_export():
    """A check job: the two compressed exports of the export job, by the sha256s that it wrote as job outputs."""
    pins = {}
    for name, file in EXPORT_FILES.items():
        expected = os.environ.get('BOS_EXPORT_SHA256' if name == 'solution' else 'BOS_CHALLENGE_SHA256', '')
        if not SHA256.fullmatch(expected):
            raise ValueError('the export pins must be 64 lowercase hex digits')
        packed = EXPORT_ARTIFACT / file
        if packed.is_symlink() or not packed.is_file() or packed.stat().st_size > EXPORT_MAX_BYTES or v.digest(packed) != expected:
            raise ValueError('an export artifact is missing or its sha256 does not match')
        target = v.WORK / 'control/export' / f'{name}.export'
        target.parent.mkdir(exist_ok=True)
        v.decompress(packed, target, EXPORT_MAX_RAW_BYTES)
        packed.unlink()
        pins[name] = {'sha256': expected, 'bytes': target.stat().st_size}
    data = v.receipt(); data['chain_export'] = {'files': pins}; v.save(data)
    return pins['solution']['sha256']


def check():
    """A check job, after setup: one segment from the end of the segment before it."""
    start = os.environ.get('BOS_CHECK_FROM', '')
    hash_from = os.environ.get('BOS_HASH_FROM', '')
    if not re.fullmatch(r'0|[1-9][0-9]{0,11}', start) or not HASH.fullmatch(hash_from):
        raise ValueError('BOS_CHECK_FROM and BOS_HASH_FROM must come from the job before')
    segment(restore_export(), int(start), hash_from)


def segment(export_sha256, start, hash_from):
    """One segment unit, with a new empty /tmp. Its record goes to the receipt's chain_segment field."""
    data = v.receipt()
    deadline = data['started_unix'] + v.DEADLINE_SECONDS
    remaining = deadline - time.time()
    record = {'export_sha256': export_sha256, 'from': start, 'expected_hash_from': hash_from}
    if remaining < SEGMENT_MIN_SECONDS:
        record.update(status='not_run', reason='job_time')
        data['chain_segment'] = record; v.save(data)
        return
    scratch = v.WORK / f'scratch-check-{start}'
    scratch.mkdir()
    control = v.WORK / 'control'
    budget_ms = int((remaining - SEGMENT_MARGIN_SECONDS) * 1000)
    args = ['--bos-check', str(control / 'lean.json'), str(control / 'export/solution.export'),
            str(control / 'export/challenge.export') if start == 0 else '-', '/tmp/segment.json', str(start),
            str(budget_ms), '0']
    v.write_json(control / 'check-args.json', args)
    command_args = v.sandbox_args(scratch=scratch) + ['/usr/bin/python3', str(control / 'inside.py'), str(v.WORK), 'check']
    code, systemd_result, guard_stop, unit_start, usage = v.launch_github('check', command_args, deadline)
    record.update(exit_code=code, systemd_result=systemd_result, guard_stop=guard_stop,
                  wall_seconds=round(time.monotonic() - unit_start, 3), **usage, log='check.log')
    path = scratch / 'segment.json'
    receipt = None
    try:
        st = os.lstat(path)
        if v.stat.S_ISREG(st.st_mode) and st.st_size <= SEGMENT_RECEIPT_MAX_BYTES:
            receipt = json.loads(path.read_text())
    except (OSError, ValueError):
        receipt = None
    if code != 0 or not isinstance(receipt, dict) or receipt.get('schema') != 'bos-segment-v1':
        reason = ('disk_limit' if guard_stop else 'out_of_memory' if systemd_result == 'oom-kill'
                  else 'timeout' if systemd_result == 'timeout' else 'no_segment_receipt')
        record.update(status='incomplete', reason=reason)
    else:
        record['segment'] = receipt
        record['status'] = 'linked' if receipt.get('status') == 'mismatch' or receipt.get('hash_from') == hash_from else 'unlinked'
    data = v.receipt(); data['chain_segment'] = record; v.save(data)
    print(f"check segment from {start}: {record['status']} {receipt.get('status') if isinstance(receipt, dict) else ''}", flush=True)


def leg():
    """Last step of every chain job (always): the job outputs that the next job and the final job read, and the
    sha256 of this job's receipt. The receipt file is not changed after this step."""
    name = os.environ.get('BOS_CHAIN_LEG', '')
    if name not in LEGS:
        raise ValueError('BOS_CHAIN_LEG must name a chain job')
    v.ART.mkdir(exist_ok=True)
    if not (v.ART / 'receipt.json').exists():
        v.save({'schema_version': 1, 'status': 'setup_failed', 'steps': [], 'kernels': {}})
    data = v.receipt()
    profile = data.get('profile') if isinstance(data.get('profile'), dict) else {}
    out = {'next': 'false'}
    state = {'leg': name}
    try:
        started = chain_started(data)
        out['chain_started'] = repr(started)
        cap = caps(profile) if profile else None
        if name in BUILD_LEGS and cap and data.get('status') != 'setup_failed':
            result, outcome = build_state(data)
            # A pack made in this job: unpack restores the record of the job before, and a pack of the same restored
            # files has the same sha256 (pack is deterministic). No new pack: the chain stops.
            pack = data.get('pack', {}).get('sha256', '')
            if pack and pack == data.get('unpack', {}).get('sha256'):
                pack, result, outcome = '', 'stop', {'status': 'incomplete', 'reason': 'build_not_run'}
            state.update(build=result, outcome=outcome)
            out['done'] = 'true' if result == 'done' and pack else 'false'
            # No job starts after max_hours, the export job too (Integrations N1): a chain holds the queue lease
            # for at most max_hours plus one job.
            if out['done'] == 'true' and not within_hours(started, profile):
                out['done'] = 'false'
                state['outcome'] = {'status': 'incomplete', 'reason': 'build_chain_cap'}
            index = BUILD_LEGS.index(name) + 1
            if result == 'continue':
                if index >= cap['max_build_jobs'] or not within_hours(started, profile):
                    state['outcome'] = {'status': 'incomplete', 'reason': 'build_chain_cap'}
                elif pack:
                    out['next'] = 'true'
        elif name not in BUILD_LEGS and cap:
            record = data.get('chain_segment')
            if isinstance(record, dict):
                seg = record.get('segment') if isinstance(record.get('segment'), dict) else {}
                index = 0 if name == 'export' else CHECK_LEGS.index(name) + 1
                stopped = record.get('status') == 'linked' and seg.get('status') == 'stopped'
                not_run = record.get('status') == 'not_run'
                if stopped or not_run:
                    if index >= cap['max_check_jobs'] or not within_hours(started, profile):
                        state['outcome'] = {'status': 'incomplete', 'reason': 'check_chain_cap'}
                    else:
                        check_from = seg.get('to') if stopped else record.get('from')
                        hash_from = seg.get('hash_to') if stopped else record.get('expected_hash_from')
                        if type(check_from) is not int or not 0 <= check_from < 10**12 \
                                or not isinstance(hash_from, str) or not HASH.fullmatch(hash_from):
                            raise ValueError('the next segment start is not an index and a hash')
                        out.update(next='true', check_from=str(check_from), hash_from=hash_from)
            files = data.get('chain_export', {}).get('files', {}) if isinstance(data.get('chain_export'), dict) else {}
            if name == 'export' and files:
                out['export_sha256'] = files['solution']['sha256']
                out['challenge_sha256'] = files['challenge']['sha256']
    except Exception as exc:  # The outputs say stop; the receipt keeps the reason.
        out = {'next': 'false'}
        state['error'] = str(exc)[:500]
    gate = v.ART / 'gate.json'
    if gate.is_file() and not gate.is_symlink():
        state['gate_sha256'] = v.digest(gate)  # The final job copies gate.json only by this pin.
    data = v.receipt()
    data['chain_leg'] = state
    data['verifier_commit'] = data.get('verifier_commit') or os.environ.get('GITHUB_SHA')
    data.setdefault('run_url', run_url())
    v.save(data)
    out['leg_sha256'] = v.digest(v.ART / 'receipt.json')
    outputs(**out)
    print('chain leg ' + name + ': ' + json.dumps(out, sort_keys=True), flush=True)


def coverage(segments, export_sha256):
    """The final job's rule (trusted): the segments, in job order, cover the walk once. Each one replays the same export
    (one sha256), starts where the one before it stopped and with its hash, checks at least one declaration when it
    stops, and the last one ended the walk with the postponed and quotient checks. The first one ran the statement and
    axiom checks. Returns the Lean record: passed, rejected, pending_review (mismatch) or incomplete."""
    expected_from, expected_hash = 0, HASH_START
    for i, record in enumerate(segments):
        seg = record.get('segment')
        if record.get('status') == 'incomplete':
            return {'status': 'incomplete', 'reason': record.get('reason', 'timeout')}
        if record.get('status') == 'not_run' and record.get('from') == expected_from:
            continue
        if not isinstance(seg, dict) or record.get('export_sha256') != export_sha256 or record.get('from') != expected_from \
                or seg.get('from') != expected_from:
            return {'status': 'incomplete', 'reason': 'chain_coverage'}
        if seg.get('status') == 'mismatch':
            if expected_from != 0:
                return {'status': 'incomplete', 'reason': 'chain_coverage'}
            return compare_outcome(str(seg.get('error', '')))
        if seg.get('hash_from') != expected_hash or (expected_from == 0 and seg.get('compare') != 'passed'):
            return {'status': 'incomplete', 'reason': 'chain_coverage'}
        to = seg.get('to')
        if type(to) is not int or to < expected_from:
            return {'status': 'incomplete', 'reason': 'chain_coverage'}
        if seg.get('status') == 'rejected':
            return {'status': 'rejected', 'reason': 'lean_kernel_rejection', 'segment': i, 'at': to}
        if seg.get('status') == 'stopped':
            if to == expected_from or not HASH.fullmatch(str(seg.get('hash_to', ''))):
                return {'status': 'incomplete', 'reason': 'chain_coverage'}
            expected_from, expected_hash = to, seg['hash_to']
            continue
        if seg.get('status') == 'passed' and seg.get('complete') is True and seg.get('quot_post_check') == 'passed' \
                and i == len(segments) - 1:
            return {'status': 'passed', 'reason': 'segmented_comparator_acceptance', 'declarations': to,
                    'segments': len(segments)}
        return {'status': 'incomplete', 'reason': 'chain_coverage'}
    return {'status': 'incomplete', 'reason': 'check_chain_cap'}


def compare_outcome(error):
    """Comparator's statement check failed in the segment at 0: the same reasons as kernel_outcome's."""
    for pattern, extra in [(r"^Challenge and solution theorem statement do not match: '([A-Za-z_][A-Za-z0-9_.]{0,99})'$", {}),
                           (r"^Const does not match between challenge and target '([A-Za-z_][A-Za-z0-9_.]{0,99})'$", {'mismatch': 'definition'})]:
        found = re.search(pattern, error, re.M)
        if found:
            return {'status': 'pending_review', 'reason': 'statement_mismatch', 'theorem': found.group(1), **extra}
    return {'status': 'pending_review', 'reason': 'ambiguous_failure'}


def run_url():
    return f"https://github.com/{os.environ.get('GITHUB_REPOSITORY', '')}/actions/runs/{os.environ.get('GITHUB_RUN_ID', '')}"


def artifact_prefix():
    """The artifact names of this run's chain for this issue: chain-leg-<run>-<attempt>-<issue>-<leg>."""
    run, attempt, issue = os.environ['GITHUB_RUN_ID'], os.environ['GITHUB_RUN_ATTEMPT'], os.environ['ISSUE_NUMBER']
    if not all(re.fullmatch(r'[1-9][0-9]{0,19}', x) for x in [run, attempt, issue]):
        raise ValueError('invalid run, attempt or issue number')
    return f'chain-leg-{run}-{attempt}-{issue}-'


def job(needs, name):
    """needs.<job> of the workflow (toJSON(needs)); the job ids are chain_<leg>."""
    value = needs.get('chain_' + name)
    return value if isinstance(value, dict) else None


def pick():
    """The export job: the build job whose pack it restores. The build jobs that ran must be build1..buildK in order,
    and only the last one says done."""
    needs = json.loads(os.environ['BOS_CHAIN_NEEDS'])
    ran = [n for n in BUILD_LEGS if job(needs, n) and job(needs, n).get('result') != 'skipped']
    if not ran or ran != BUILD_LEGS[:len(ran)]:
        raise ValueError('the build jobs that ran are not build1..buildK')
    done = [n for n in ran if (job(needs, n).get('outputs') or {}).get('done') == 'true']
    if done != [ran[-1]]:
        raise ValueError('only the last build job may say done')
    last = job(needs, ran[-1])
    sha = (last.get('outputs') or {}).get('build_sha256', '')
    record = (last.get('outputs') or {}).get('build_record_sha256', '')
    if not SHA256.fullmatch(sha) or not SHA256.fullmatch(record):
        raise ValueError('the last build job has no pack sha256 or no record sha256')
    outputs(leg=ran[-1], build_sha256=sha, build_record_sha256=record, result=last.get('result', ''))


def read_legs(needs, folder):
    """The receipt of each chain job that ran, from its artifact, by the leg_sha256 that the job wrote as an output."""
    legs = {}
    prefix = artifact_prefix()
    for name in LEGS:
        found = job(needs, name)
        if not found or found.get('result') == 'skipped':
            continue
        expected = (found.get('outputs') or {}).get('leg_sha256', '')
        path = folder / (prefix + name) / 'receipt.json'
        if not SHA256.fullmatch(expected) or path.is_symlink() or not path.is_file() or v.digest(path) != expected:
            legs[name] = None  # Ran, but its receipt is missing or does not match its pin.
            continue
        receipt = json.loads(path.read_text())
        # Only receipts of this run and this verifier commit (the artifact names hold the run id and attempt too).
        if not isinstance(receipt, dict) or receipt.get('run_url') != run_url() \
                or receipt.get('verifier_commit') != os.environ.get('GITHUB_SHA'):
            legs[name] = None
            continue
        legs[name] = receipt
    return legs


def final():
    """The final job: one receipt from the chain jobs' receipts (pinned by their outputs), then verifier.finalize."""
    needs = json.loads(os.environ['BOS_CHAIN_NEEDS'])
    folder = v.ROOT / 'chain-legs'
    legs = read_legs(needs, folder)
    v.ART.mkdir(exist_ok=True)
    ran = [name for name in LEGS if name in legs]
    # The gate record (claimed only) of the export job, else of build1.
    for name in ['export', 'build1']:
        gate = folder / (artifact_prefix() + name) / 'gate.json'
        pin = ((legs.get(name) or {}).get('chain_leg') or {}).get('gate_sha256')
        if pin and gate.is_file() and not gate.is_symlink() and v.digest(gate) == pin:
            shutil.copyfile(gate, v.ART / 'gate.json')
            break
    base_name = next((n for n in ['export'] + BUILD_LEGS[::-1] if legs.get(n)), None)
    if base_name is None:
        return  # finalize writes setup_failed.
    data = dict(legs[base_name])
    if data.get('status') == 'setup_failed' and 'request' not in data:
        v.save(data)  # The gate stopped the chain, or setup failed: as a split run's check job (finalize).
        return
    builds = [legs.get(n) for n in BUILD_LEGS if n in legs]
    data['chain'] = {'legs': [{'leg': n, 'receipt_sha256': (job(needs, n).get('outputs') or {}).get('leg_sha256'),
                               'result': job(needs, n).get('result'), 'state': (legs[n] or {}).get('chain_leg')} for n in ran]}
    if any(b is None for b in builds) or (legs.get('export') is None and 'export' in legs):
        data['kernels'] = {'lean': {'status': 'incomplete', 'reason': 'chain_coverage'}}
    elif legs.get('export') is None:
        state = (builds[-1] or {}).get('chain_leg', {}) if builds else {}
        outcome = state.get('outcome') or {'status': 'incomplete', 'reason': 'build_chain_cap'}
        data['kernels'] = {'lean': dict(outcome)}
        data['axiom_audit'] = data.get('axiom_audit', {'status': 'not_started'})
    else:
        export = legs['export']
        record = export.get('chain_export') or {}
        if record.get('status') != 'passed':
            lean = {k: record[k] for k in ['status', 'reason', 'diagnostic', 'theorem', 'mismatch'] if k in record} or \
                {'status': 'incomplete', 'reason': 'export_not_run'}
        else:
            segments = [legs[n].get('chain_segment') for n in ['export'] + CHECK_LEGS if n in legs and legs[n]]
            if any(n in legs and legs[n] is None for n in CHECK_LEGS):
                lean = {'status': 'incomplete', 'reason': 'chain_coverage'}
            elif not any(isinstance(s, dict) for s in segments):
                # Without the audit no segment runs (export). After a passed audit, a missing segment record is a
                # verifier problem (Integrations N2).
                lean = ({'status': 'incomplete', 'reason': 'no_segment_record'}
                        if export.get('axiom_audit', {}).get('status') == 'passed' else {'status': 'not_started'})
            else:
                sha = (record.get('files') or {}).get('solution', {}).get('sha256')
                lean = coverage([s for s in segments if isinstance(s, dict)], sha)
        lean['segments_detail'] = [
            {'leg': n, **{k: (legs[n].get('chain_segment') or {}).get(k) for k in ['status', 'reason', 'from', 'wall_seconds',
                                                                                     'sampled_peak_cgroup_bytes', 'systemd_result']},
             'segment': {k: ((legs[n].get('chain_segment') or {}).get('segment') or {}).get(k)
                         for k in ['status', 'from', 'to', 'todo_constants', 'parse_ms', 'replay_ms']}}
            for n in ['export'] + CHECK_LEGS if legs.get(n)]
        data['kernels'] = {'lean': lean}
    data['kernels']['nanoda'] = {'status': 'incomplete', 'reason': 'not_run_chain'}
    data['build'] = next((b.get('build') for b in reversed(builds) if b and b.get('build')), data.get('build'))
    data['verification_stage'] = 'final'
    passed = data['kernels']['lean'].get('status') == 'passed' and data.get('axiom_audit', {}).get('status') == 'passed'
    data['status'] = 'passed' if passed else 'not_verified'
    for key in ['chain_segment', 'chain_leg', 'error']:
        data.pop(key, None)
    v.save(data)


def main():
    phase = sys.argv[1] if len(sys.argv) == 2 else ''
    if phase not in ['challenge', 'pick', 'export', 'check', 'leg', 'final']:
        raise SystemExit('usage: chain.py challenge|pick|export|check|leg|final')
    try:
        globals()[phase]()
    except Exception as exc:
        if (v.ART / 'receipt.json').exists():
            data = v.receipt(); data['error'] = str(exc); v.save(data)
        print(f'{phase}: {exc}', file=sys.stderr)
        raise SystemExit(1)


if __name__ == '__main__':
    main()
