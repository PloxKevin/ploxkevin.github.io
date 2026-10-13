"""Export the genuine checkpoint35 audit and freeze exact reviewed source bytes.

Only the selected sources and explicit ledgers are included. Immutable objects
are shared by hardlink; prior snapshots, caches and historical archives remain
at their original locations. Exact completed stages are accepted on a rerun.
"""
import argparse
import copy
import importlib.util
import json
import os
import sys
from pathlib import Path
from prepare_runtime35 import ROOT, RUNTIME, SELECTION, encode, exact, path, put, read, ref, sha

ORIGINAL = RUNTIME + '/reports/lean-verification'
EXPORT = 'reports/full-coverage/lean-checkpoint-35-source90-v1'
SNAPSHOT = 'reports/full-coverage/checkpoint-35'
MANIFEST = 'reports/full-coverage/checkpoint-35-manifest.json'
FROZEN_LEDGER = 'reports/full-coverage/ledger35-frozen-source-only-v1.json'
OUT = 'reports/full-coverage/checkpoint35-finalization-v1.json'
EXCLUDED = {
    'verification/lean/SafeLearning/CompleteAppliedBinaryTemperaturePrecision.lean',
    'verification/lean/SafeLearning/CompleteAppliedBinaryVariationalPrecision.lean',
    'verification/lean/SafeLearning/CompleteAppliedConformalCalibrationOnly.lean'}


def linked(name, data):
    fingerprint = __import__('hashlib').sha256(data).hexdigest()
    object_name = 'reports/full-coverage/source-objects/' + fingerprint[:2] + '/' + fingerprint
    put(object_name, data)
    path(object_name).chmod(0o444)
    destination = path(name)
    destination.parent.mkdir(parents=True, exist_ok=True)
    if not destination.exists():
        os.link(path(object_name), destination)
    assert sha(name) == fingerprint, name


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--audit-receipt', required=True)
    parser.add_argument('--audit-receipt-sha256', required=True)
    parser.add_argument('--owner-installation', required=True)
    parser.add_argument('--owner-installation-sha256', required=True)
    parser.add_argument('--ledger', required=True)
    parser.add_argument('--ledger-sha256', required=True)
    args = parser.parse_args()
    for name, fingerprint in [(args.audit_receipt, args.audit_receipt_sha256),
                              (args.owner_installation, args.owner_installation_sha256),
                              (args.ledger, args.ledger_sha256)]:
        exact({'file': name, 'sha256': fingerprint})
    selection = read(SELECTION)
    preparation = read('reports/full-coverage/checkpoint35-runtime-preparation-v1.json')
    audit = read(ORIGINAL + '/verification.json')
    native = read(args.audit_receipt)
    integration = read(args.owner_installation)
    ledger = read(args.ledger)
    assert native['status'] == 'passed' and native['actual_exit_code'] == 0
    assert native['actual_command'] == ['python3', RUNTIME + '/verification/lean/verify.py',
        '--reuse-kernel-from', str(path('reports/full-coverage/runtime-checkpoint-34-source90-v1')),
        '--resume-kernel']
    assert native['actual_workdir'] == str(ROOT) and sha(native['log']) == native['log_sha256']
    before = native.get('input_sha256_before', native.get('helper_sha256_before'))
    after = native.get('input_sha256_after', native.get('helper_sha256_after'))
    assert before == after and before[RUNTIME + '/verification/lean/verify.py'] == sha('verification/lean/verify.py')
    assert audit['status'] == 'passed' and audit['proof_file_count'] == 1267 and audit['theorem_count'] == 11472
    assert len(audit['declarations']) == len(audit['axiom_dependencies']) == 11472
    assert audit['proof_sha256'] == {n: r['sha256'] for n, r in selection['proof_files'].items()}
    assert len(audit['checks']) == 1270 and all(c['exit_code'] == 0 for c in audit['checks'])
    fresh = [c for c in audit['checks'] if c.get('evidence_mode') == 'fresh_kernel_replay']
    reused = [c for c in audit['checks'] if c.get('reused_from')]
    assert len(fresh) == 3 and len(reused) == 1264
    baseline = read('reports/full-coverage/checkpoint-34-selection.json')
    new_sources = set(selection['proof_files']) - set(baseline['proof_files'])
    assert {c['module'] for c in fresh} == {'SafeLearning.' + Path(n).stem for n in new_sources}
    assert all(c['actual_workdir'] == str(path(RUNTIME + '/verification/lean')) for c in fresh)
    assert all(c['reused_from']['report_sha256'] == selection['baseline_actual_passing_audit']['sha256'] for c in reused)
    assert all(set(a) <= {'propext', 'Classical.choice', 'Quot.sound'} for a in audit['axiom_dependencies'].values())
    assert len(audit['source_sha256']) == 31
    assert preparation['selection'] == ref(SELECTION)
    assert preparation['all31_site_assets_identical_to_checkpoint34'] is True
    generated = 'verification/lean/SafeLearning.lean'
    for table in ['proof_sha256', 'source_sha256', 'project_sha256']:
        for n, h in audit[table].items():
            assert sha(RUNTIME + '/' + n) == preparation['source_hashes'][n] == h
            if n != generated:
                assert sha(n) == h
    assert integration['applied'] is True and integration['coverage_complete'] is False
    for replacement in integration['exact_replacements']:
        exact(replacement['candidate'])
        exact(replacement['preserved_original'])
        exact(replacement['exact_inverse'])
        assert sha(replacement['destination']) == replacement['candidate']['sha256']
    assert ledger['integrity_status'] == 'passed' and ledger['errors'] == []
    assert ledger['mathematical_coverage_complete'] is False
    assert ledger['inventory_sha256'] == sha('book/coverage/inventory.json')
    assert ledger['counts']['exercises'] == 556 and ledger['counts']['material_source_units'] == 12774
    for domain in ledger['domains']:
        assert domain['ledger_sha256'] == sha('book/coverage/' + domain['domain'] + '.json')
    audit_files = sorted(p for p in path(ORIGINAL).iterdir() if p.is_file())
    audit_hashes = {p.name: sha(p.relative_to(ROOT).as_posix()) for p in audit_files}
    for check in audit['checks']:
        if 'log_sha256' in check:
            assert check['output_file'].startswith('reports/lean-verification/')
            name = check['output_file'].removeprefix('reports/lean-verification/')
            assert audit_hashes[name] == check['log_sha256'], name
    for p in audit_files:
        n = 'verification-original.json' if p.name == 'verification.json' else p.name
        linked(EXPORT + '/' + n, p.read_bytes())
    relocated = copy.deepcopy(audit)
    for c in relocated['checks']:
        for table, key in [(c, 'output_file'), (c.get('reused_from', {}), 'report')]:
            if table.get(key, '').startswith('reports/lean-verification/'):
                table[key] = EXPORT + '/' + table[key].removeprefix('reports/lean-verification/')
    relocated['audit_origin'] = {
        'original_report': ref(EXPORT + '/verification-original.json'),
        'actual_workdir': str(path(RUNTIME + '/verification/lean')),
        'actual_execution': ref(args.audit_receipt),
        'scope': 'Exported report paths relocate output only; native commands, cwd, inputs and outcomes remain unchanged.'}
    put(EXPORT + '/verification.json', encode(relocated))
    files = set(audit['proof_sha256']) | set(audit['source_sha256']) | set(audit['project_sha256'])
    files |= {'book/coverage/' + n for n in ['inventory.json', 'material-corrections.json',
        'foundations.json', 'applied.json', 'modules.json', 'core.json',
        'applied-promotions.json', 'validate.py', 'lean_names.py']}
    sys.path.insert(0, str(path('book/coverage')))
    from lean_names import declarations
    public = {d['name'] for n in audit['proof_sha256'] for d in declarations(path(n).read_text())}
    owners, excluded = {}, {}
    for domain in ['foundations', 'applied', 'modules', 'core']:
        owner = owners[domain] = read('book/coverage/' + domain + '.json')
        for n, h in owner.get('chapter_fragment_sha256', {}).items():
            assert sha(n) == h
            files.add(n)
        for claim in owner['material_claims'] + [c for e in owner['exercises'] for c in e['claims']]:
            assert set(claim['lean_declarations']) <= public
        excluded[domain] = sorted(set(owner['proof_files']) - set(audit['proof_sha256']))
        assert set(excluded[domain]) == (EXCLUDED if domain == 'applied' else set())
    inputs = {n: sha(n) for n in sorted(files) if n != generated}
    for n in sorted(files):
        if n == 'book/coverage/applied.json':
            owner = copy.deepcopy(owners['applied'])
            owner['proof_files'] = {k: v for k, v in owner['proof_files'].items() if k not in EXCLUDED}
            if 'proof_sha256' in owner:
                owner['proof_sha256'] = {k: v for k, v in owner['proof_sha256'].items() if k not in EXCLUDED}
            data = (json.dumps(owner, indent=2) + '\n').encode()
        else:
            data = path((RUNTIME + '/' if n == generated else '') + n).read_bytes()
        linked(SNAPSHOT + '/' + n, data)
    spec = importlib.util.spec_from_file_location('checkpoint35_frozen_validator', path('book/coverage/validate.py'))
    validator = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(validator)
    validator.ROOT = path(SNAPSHOT)
    if path(FROZEN_LEDGER).exists():
        frozen_ledger = read(FROZEN_LEDGER)
    else:
        frozen_ledger = validator.validate()
        assert frozen_ledger['integrity_status'] == 'passed' and frozen_ledger['errors'] == []
        put(FROZEN_LEDGER, encode(frozen_ledger))
    assert frozen_ledger['integrity_status'] == 'passed' and frozen_ledger['errors'] == []
    assert frozen_ledger['inventory_sha256'] == sha('book/coverage/inventory.json')
    assert frozen_ledger['counts'] == ledger['counts']
    assert frozen_ledger['mathematical_coverage_complete'] is False
    for domain in frozen_ledger['domains']:
        assert domain['ledger_sha256'] == sha(SNAPSHOT + '/book/coverage/' + domain['domain'] + '.json')
    entries = list(path(SNAPSHOT).rglob('*'))
    assert all(not p.is_symlink() for p in entries)
    frozen = {p.relative_to(path(SNAPSHOT)).as_posix(): sha(p.relative_to(ROOT).as_posix())
              for p in entries if p.is_file()}
    assert set(frozen) == files
    manifest = {
        'status': 'formal_verification_passed_partial_coverage', 'snapshot': SNAPSHOT,
        'selection': SELECTION, 'selection_sha256': sha(SELECTION),
        'proof_files': selection['proof_files'], 'working_inputs_sha256': inputs,
        'frozen_inputs_sha256': frozen, 'source_only_snapshot': True,
        'old_snapshot_or_lake_tree_copied': False, 'coverage_complete': False,
        'owner_integration': ref(args.owner_installation), 'working_ledger_audit': ref(args.ledger),
        'frozen_ledger_audit': ref(FROZEN_LEDGER), 'excluded_unreferenced_ledger_metadata': excluded,
        'successful_verification': {'report': EXPORT + '/verification-original.json',
            'report_sha256': sha(ORIGINAL + '/verification.json'),
            'actual_execution': ref(args.audit_receipt),
            'actual_workdir': str(path(RUNTIME + '/verification/lean')),
            'snapshot_execution_claimed': False, 'proof_files': 1267, 'public_theorems': 11472,
            'fresh_kernel_files': 3, 'exact_prior_kernel_reuses': 1264},
        'limits': ['Mathematical coverage remains partial.',
            'The exact conditional assumptions and expressions carry the Gaussian certificate; printed decimals are approximations.',
            'Independent source review establishes correspondence; compilation establishes only encoded statements.',
            'Only unused Applied metadata is omitted; all claims and historical evidence remain preserved.']}
    put(MANIFEST, encode(manifest))
    assert all(sha(n) == h for n, h in inputs.items())
    assert all(sha(ORIGINAL + '/' + n) == h for n, h in audit_hashes.items())
    result = {'status': 'passed_checkpoint35_actual_audit_export_and_source_only_freeze',
        'manifest': ref(MANIFEST), 'selection': ref(SELECTION),
        'audit': ref(EXPORT + '/verification-original.json'),
        'native_execution': ref(args.audit_receipt), 'owner_integration': ref(args.owner_installation),
        'working_ledger': ref(args.ledger), 'frozen_ledger': ref(FROZEN_LEDGER),
        'proof_files': 1267, 'public_theorems': 11472, 'coverage_complete': False,
        'counts': ledger['counts'], 'snapshot_file_count': len(frozen)}
    put(OUT, encode(result))
    print(json.dumps({'status': result['status'], 'proof_files': 1267,
                      'public_theorems': 11472, 'record': ref(OUT)}))


if __name__ == '__main__':
    main()
