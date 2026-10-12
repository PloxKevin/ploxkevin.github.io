"""Prepare a new TMP runner only after the actual installed-owner29 audit/export.

Default execution is read-only. --apply creates two unused /tmp paths; it does
not invoke Lean or alter sources, owners, selections, snapshots or publication.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import hashlib
import json

ROOT = Path(__file__).resolve().parents[3]
SELF = 'book/coverage/checks/root_prepare_tmp_source65_owner29_context_v1.py'
CONTEXT = Path('/tmp/root_tmp_lean_current65_owner29_context_v1.json')
RUNNER = Path('/tmp/root_tmp_lean_current65_owner29_runner_v1.py')
OLD_CONTEXT = Path('/tmp/root_tmp_lean_current65_owner28_context_v1.json')
OLD_RUNNER = Path('/tmp/root_tmp_lean_current65_owner28_runner_v1.py')
OLD_CONTEXT_SHA = '10ca7b21579a0fcd69454c1a2c211156607bd59301b2ba0bfea11e3f2dc71e78'
OLD_RUNNER_SHA = 'bf3d5182ac8de730a86571059fa6d168b2c7d66e599fd3954f2c741b900ad8e7'
SNAPSHOT = 'reports/full-coverage/checkpoint-29'
SELECTION = SNAPSHOT + '-selection.json'
MANIFEST = SNAPSHOT + '-manifest.json'
AUDIT = 'reports/full-coverage/lean-checkpoint-29/verification-original.json'
VERIFY = 'reports/full-coverage/verify-checkpoint29-execution-v1.json'
EXPORT = 'reports/full-coverage/export-checkpoint29-execution-v1.json'
OWNERS = tuple('book/coverage/' + n + '.json' for n in
               ('core', 'foundations', 'modules', 'applied', 'applied-promotions'))
INVENTORY_SHA = '5f68ee3c68c1da1275a0a2667fe43b42263b8fc31800a834371de5bfbed01b68'
CORRECTIONS_SHA = '5c3a871bbc5782a02c5b19bfa33a8fa6e4dc311a9e72c525d76fcc526f37eafd'
STATUS = 'actual_current65_owner29_selected29_audited_context_for_new_tmp_trials_only'


def safe(n):
    assert type(n) is str and n and not Path(n).is_absolute()
    assert '..' not in Path(n).parts and Path(n).as_posix() == n
    p = ROOT / n
    assert p.resolve().is_relative_to(ROOT) and not p.is_symlink()
    return p


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def read(n):
    return json.loads(safe(n).read_bytes())


def ref(n):
    return {'file': n, 'sha256': sha(safe(n))}


def zero(n, expected_hash, command):
    assert sha(safe(n)) == expected_hash
    d = read(n)
    assert d['status'] == 'passed'
    codes = [d[k] for k in ('actual_exit_code', 'exit_code') if k in d]
    assert codes and all(type(v) is int and v == 0 for v in codes)
    commands = [d[k] for k in ('actual_command', 'command') if k in d]
    assert commands and all(v == command for v in commands)
    directories = [d[k] for k in ('actual_workdir', 'working_directory', 'workdir', 'cwd') if k in d]
    assert directories and all(v == str(ROOT) for v in directories)
    before, after = d['helper_sha256_before'], d['helper_sha256_after']
    assert type(before) is dict and before and before == after
    assert command[1] in before
    for name, h in before.items():
        assert sha(safe(name)) == h
    logs = [(d[k], d[h]) for k, h in
            (('log', 'log_sha256'), ('raw_log', 'raw_log_sha256')) if k in d or h in d]
    assert logs
    for name, h in logs:
        assert sha(safe(name)) == h
    return d


def merge(target, values):
    assert type(values) is dict and values
    for n, h in values.items():
        assert type(h) is str and len(h) == 64 and sha(safe(n)) == h
        assert n not in target or target[n] == h
        target[n] = h


def prepare(args):
    assert not CONTEXT.exists() and not RUNNER.exists()
    assert sha(OLD_CONTEXT) == OLD_CONTEXT_SHA and sha(OLD_RUNNER) == OLD_RUNNER_SHA
    for n, h in ((SELECTION, args.selection_sha256), (MANIFEST, args.manifest_sha256),
                 (AUDIT, args.audit_sha256)):
        assert sha(safe(n)) == h
    selection, manifest, audit = read(SELECTION), read(MANIFEST), read(AUDIT)
    assert selection['proof_file_count'] == len(selection['proof_files']) == 1197
    assert selection['new_file_count'] == 11
    proofs = {n: r['sha256'] for n, r in selection['proof_files'].items()}
    assert manifest['selection'] == SELECTION and manifest['selection_sha256'] == args.selection_sha256
    assert manifest['snapshot'] == SNAPSHOT and manifest['proof_files'] == selection['proof_files']
    assert manifest['status'] == 'formal_verification_passed_partial_coverage'
    assert audit['status'] == 'passed' and audit['proof_file_count'] == len(audit['proof_sha256']) == 1197
    assert audit['theorem_count'] == len(audit['declarations']) == 10114
    assert audit['proof_sha256'] == proofs
    assert len({d['name'] for d in audit['declarations']}) == 10114
    assert {d['name'] for d in audit['declarations']} == set(audit['axiom_dependencies'])
    standard = {'Classical.choice', 'Quot.sound', 'propext'}
    assert set(audit['allowed_standard_axioms']) == standard
    assert all(type(xs) is list and set(xs) <= standard for xs in audit['axiom_dependencies'].values())
    assert type(audit['checks']) is list and audit['checks']
    assert all(type(c['exit_code']) is int and c['exit_code'] == 0 for c in audit['checks'])
    assert any(c['command'] == ['lake', 'build'] for c in audit['checks'])
    kernels = [c for c in audit['checks'] if c['command'][:3] == ['lake', 'env', 'leanchecker']]
    assert len(kernels) == 1197
    assert sum(bool(c.get('reused_from')) for c in kernels) == 1186
    assert sum(not bool(c.get('reused_from')) for c in kernels) == 11
    verified = manifest['successful_verification']
    assert verified == {'proof_file_count': 1197, 'theorem_count': 10114,
                        'all_check_exit_codes': 0, 'report': AUDIT,
                        'report_sha256': args.audit_sha256}
    assert sha(safe(SNAPSHOT + '/reports/lean-verification/verification.json')) == args.audit_sha256
    verify_command = ['python3', SNAPSHOT + '/verification/lean/verify.py',
                      '--reuse-kernel-from', str(ROOT / 'reports/full-coverage/checkpoint-28')]
    export_command = ['python3', 'book/coverage/export_audit29_v1.py',
                      '--snapshot', SNAPSHOT, '--output', 'reports/full-coverage/lean-checkpoint-29']
    native_verify = zero(VERIFY, args.verify_execution_sha256, verify_command)
    native_export = zero(EXPORT, args.export_execution_sha256, export_command)
    inventory = read('book/coverage/inventory.json')
    assert sha(safe('book/coverage/inventory.json')) == INVENTORY_SHA
    assert sha(safe('book/coverage/inventory-after-correction65.json')) == INVENTORY_SHA
    assert sha(safe('book/coverage/material-corrections.json')) == CORRECTIONS_SHA
    assert len(read('book/coverage/material-corrections.json')['corrections']) == 65
    assert len(inventory['source_sha256']) == 31 and audit['source_sha256'] == inventory['source_sha256']
    frozen = manifest['frozen_inputs_sha256']
    working = manifest['working_inputs_sha256']
    owners = {n: working[n] for n in OWNERS}
    held, pins = {}, {}
    merge(held, proofs)
    merge(held, inventory['source_sha256'])
    merge(held, owners)
    for n, h in {**proofs, **audit['source_sha256'], **audit['project_sha256']}.items():
        assert sha(safe(SNAPSHOT + '/' + n)) == h
        assert frozen[n] == h
        pins[SNAPSHOT + '/' + n] = h
    assert len(audit['project_sha256']) == 5
    for n, h in audit['project_sha256'].items():
        if n != 'verification/lean/SafeLearning.lean':
            merge(held, {n: h})
    aggregate = '\n'.join('import SafeLearning.' + Path(n).stem for n in sorted(proofs)) + '\n'
    assert safe(SNAPSHOT + '/verification/lean/SafeLearning.lean').read_bytes() == aggregate.encode()
    merge(held, {'verification/lean/SafeLearning.lean': sha(safe('verification/lean/SafeLearning.lean'))})
    for n in ('book/coverage/inventory.json', 'book/coverage/inventory-after-correction65.json',
              'book/coverage/material-corrections.json', 'book/coverage/lean_names.py', SELF):
        merge(pins, {n: sha(safe(n))})
    for n in (SELECTION, MANIFEST, AUDIT, VERIFY, EXPORT):
        merge(pins, {n: sha(safe(n))})
    for d in (native_verify, native_export):
        merge(pins, d['helper_sha256_before'])
        for k, h in (('log', 'log_sha256'), ('raw_log', 'raw_log_sha256')):
            if k in d:
                merge(pins, {d[k]: d[h]})
    # The snapshot's raw owners are independently pinned. Applied may have its
    # three unselected metadata rows pruned there; never substitute raw bytes.
    for n in OWNERS + ('book/coverage/inventory.json', 'book/coverage/material-corrections.json'):
        assert sha(safe(SNAPSHOT + '/' + n)) == frozen[n]
        merge(pins, {SNAPSHOT + '/' + n: frozen[n]})
    context = {'status': STATUS, 'prepared_at_utc': datetime.now(timezone.utc).isoformat(),
               'pins_sha256': pins, 'held_current_source_sha256': held,
               'owners_sha256': owners, 'selection': ref(SELECTION), 'manifest': ref(MANIFEST),
               'actual_audit': ref(AUDIT), 'actual_audit_execution': ref(VERIFY),
               'actual_export_execution': ref(EXPORT),
               'original_source65_owner28_context': {'file': str(OLD_CONTEXT), 'sha256': OLD_CONTEXT_SHA},
               'original_source65_owner28_runner': {'file': str(OLD_RUNNER), 'sha256': OLD_RUNNER_SHA},
               'protected_selected29_proof_sources': 1197, 'held_current65_book_assets': 31,
               'held_installed29_owners': 5, 'scope': 'New TMP executions hold actual selected29 audited Source65 bytes and installed owner29 inputs. Original execution records, bodies and times remain historical and unchanged.',
               'coverage_complete': False}
    return context


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    for name in ('selection', 'manifest', 'audit', 'verify-execution', 'export-execution'):
        ap.add_argument('--' + name + '-sha256', required=True)
    ap.add_argument('--apply', action='store_true')
    args = ap.parse_args()
    context = prepare(args)
    payload = (json.dumps(context, indent=2) + '\n').encode()
    context_sha = hashlib.sha256(payload).hexdigest()
    template = OLD_RUNNER.read_text()
    template = template.replace('unchanged audited owner28 context', 'actual audited owner29 context')
    template = template.replace(str(OLD_CONTEXT), str(CONTEXT)).replace(OLD_CONTEXT_SHA, context_sha)
    template = template.replace('actual_current65_owner28_context_after_reviewed_source_corrections_for_new_tmp_trials_only', STATUS)
    template = template.replace('current28_names', 'current29_names')
    template = template.replace('actual_source65_installed28_context', 'actual_source65_installed29_context')
    template = template.replace('actual_installed28_selection', 'actual_installed29_selection')
    template = template.replace('actual_frozen28_original_audit', 'actual_frozen29_original_audit')
    template = template.replace('protected_selected28_proof_sources\':1186', 'protected_selected29_proof_sources\':1197')
    template = template.replace('unchanged_installed28_live_owners', 'unchanged_installed29_live_owners')
    template = template.replace('installed28_owner_sha256', 'installed29_owner_sha256')
    assert str(OLD_CONTEXT) not in template and OLD_CONTEXT_SHA not in template
    # Bind both map roles explicitly even if their paths coincide.
    template = template.replace("**context['held_current_source_sha256']}",
                                "**context['held_current_source_sha256'],**context['owners_sha256']}")
    merge({}, {**context['pins_sha256'], **context['held_current_source_sha256'], **context['owners_sha256']})
    assert sha(OLD_CONTEXT) == OLD_CONTEXT_SHA and sha(OLD_RUNNER) == OLD_RUNNER_SHA
    if args.apply:
        assert not CONTEXT.exists() and not RUNNER.exists()
        with CONTEXT.open('xb') as f:
            f.write(payload)
        with RUNNER.open('x') as f:
            f.write(template)
        assert sha(CONTEXT) == context_sha
    print(json.dumps({'status': 'prepared_new_owner29_context_and_runner' if args.apply else 'passed_readonly_owner29_context_preparation',
                      'context': {'file': str(CONTEXT), 'sha256': context_sha},
                      'runner': {'file': str(RUNNER), 'sha256': hashlib.sha256(template.encode()).hexdigest()},
                      'actual_audit': context['actual_audit'], 'compiler_invoked': False, 'coverage_complete': False}))


if __name__ == '__main__':
    main()
