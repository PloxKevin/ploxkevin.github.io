"""Check, export and freeze the genuine checkpoint34 audit with resumable stages.

No compiler success is inferred from copying files. Completed stages retain
their original receipts and all source bytes are verified before reuse.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import copy
import importlib.util
import json
import sys

sys.dont_write_bytecode = True
from install_owners34 import ROOT, path, sha, ref, read, exact, atomic, encode

RUNTIME = 'reports/full-coverage/runtime-checkpoint-34-source90-v1'
ORIGINAL = RUNTIME + '/reports/lean-verification'
EXPORT = 'reports/full-coverage/lean-checkpoint-34-source90-v1'
SNAPSHOT = 'reports/full-coverage/checkpoint-34'
MANIFEST = 'reports/full-coverage/checkpoint-34-manifest.json'
SELECTION = 'reports/full-coverage/checkpoint-34-selection.json'
PREPARATION = 'reports/full-coverage/checkpoint34-runtime-source90-preparation-v1.json'
INTEGRATION = 'reports/full-coverage/owner34-integration-v1.json'
LEDGER = 'reports/full-coverage/ledger34-working-v1.json'
NATIVE = 'reports/full-coverage/verify-runtime34-execution-v1.json'
FROZEN_LEDGER = 'reports/full-coverage/ledger34-frozen-source-only-v1.json'
READINESS = 'book/coverage/checks/checkpoint34-preparation-root/three-future34-paired-packets-v1.json'
PEER = 'book/coverage/checks/checkpoint34-review/independent-four-owner34-candidates-review-v3.json'
UNSELECTED_METADATA = {
    'verification/lean/SafeLearning/CompleteAppliedBinaryTemperaturePrecision.lean',
    'verification/lean/SafeLearning/CompleteAppliedBinaryVariationalPrecision.lean',
    'verification/lean/SafeLearning/CompleteAppliedConformalCalibrationOnly.lean',
}
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def put_exact(name, data):
    if path(name).exists():
        assert path(name).read_bytes() == data, name
    else:
        atomic(name, data)


def verify_inputs(args):
    for name, expected in args.inputs.items():
        assert sha(name) == expected, name
    selection, preparation = read(SELECTION), read(PREPARATION)
    audit, native = read(ORIGINAL + '/verification.json'), read(NATIVE)
    integration, ledger, peer = read(INTEGRATION), read(LEDGER), read(PEER)
    assert selection['proof_file_count'] == len(selection['proof_files']) == 1264
    assert selection['new_file_count'] == 3
    assert selection['expected_public_theorem_count_pending_actual_aggregate'] == 11459
    baseline = json.loads(exact(selection['baseline_selection']).read_bytes())
    prior_audit = json.loads(exact(selection['baseline_actual_passing_audit']).read_bytes())
    assert len(baseline['proof_files']) == prior_audit['proof_file_count'] == 1261
    assert prior_audit['status'] == 'passed' and prior_audit['theorem_count'] == 11345
    assert prior_audit['proof_sha256'] == {n: r['sha256'] for n, r in baseline['proof_files'].items()}
    assert all(selection['proof_files'][n]['sha256'] == r['sha256'] for n, r in baseline['proof_files'].items())
    additions = json.loads(exact(selection['additions_plan']).read_bytes())
    assert additions['status'] == 'passed_reviewed_compiled_additions_ready_for_selection'
    assert additions['new_file_count'] == len(additions['sources']) == 3
    assert additions['new_public_theorem_count'] == 114
    readiness = json.loads(exact(additions['readiness']).read_bytes())
    assert additions['readiness'] == ref(READINESS)
    assert readiness['errors'] == [] and readiness['new_source_count'] == 3
    assert readiness['new_theorem_count'] == 114 and readiness['actual_compiler_command_count'] == 6
    new_sources = set(selection['proof_files']) - set(baseline['proof_files'])
    assert new_sources == {r['canonical_source']['file'] for r in readiness['sources']}
    for source in readiness['sources']:
        canonical = exact(source['canonical_source'])
        assert selection['proof_files'][source['canonical_source']['file']]['sha256'] == source['canonical_source']['sha256']
        for pair in source['actual_paired_records']:
            receipt = json.loads(exact(pair['actual_record']).read_bytes())
            assert receipt['actual_exit_code'] == pair['actual_exit_code'] == 0
            assert canonical.read_bytes() == exact(pair['source_snapshot']).read_bytes()
            exact(pair['raw_log'])
    for key in ['independent_actual_source_application_review', 'independent_cumulative_qualifier_review', 'independent_whole_prospective_correspondence']:
        review = json.loads(exact(additions[key]).read_bytes())
        assert review['status'].startswith(('passed', 'approved')) and review.get('errors', []) == []
    assert preparation['selection'] == ref(SELECTION) and preparation['runtime'] == RUNTIME
    assert preparation['selected_source_count'] == 1264 and preparation['new_sources'] == 3 and preparation['new_theorems'] == 114
    assert preparation['copied_lake_build_artifact_count'] == preparation['copied_earlier_snapshot_tree_count'] == 0
    assert preparation['inventory'] == ref('book/coverage/inventory.json')
    application = json.loads(exact(preparation['source_application']).read_bytes())
    assert [r['correction_id'] for r in application['applications']] == [89, 90]
    assert application['final_inventory'] == preparation['inventory']
    assert set(preparation['changed_site_pages_reviewed_source90']) == set(application['source_pages']) == {
        'SafeLearning/nn-in-the-loop.html', 'SafeLearning/primer-probability.html'}
    assert preparation['unchanged_site_assets_from_actual_checkpoint33'] == 29
    assert audit['status'] == 'passed' and audit['proof_file_count'] == len(audit['proof_sha256']) == 1264
    assert audit['theorem_count'] == len(audit['declarations']) == len(audit['axiom_dependencies']) == 11459
    assert audit['proof_sha256'] == {n: r['sha256'] for n, r in selection['proof_files'].items()}
    assert len(audit['checks']) == 1267 and all(type(c['exit_code']) is int and c['exit_code'] == 0 for c in audit['checks'])
    fresh = [c for c in audit['checks'] if c.get('evidence_mode') == 'fresh_kernel_replay']
    reused = [c for c in audit['checks'] if c.get('reused_from')]
    assert len(fresh) == 3 and len(reused) == 1261
    assert {c['module'] for c in fresh} == {'SafeLearning.' + Path(n).stem for n in new_sources}
    assert all(c['actual_workdir'] == str(path(RUNTIME + '/verification/lean')) for c in fresh)
    assert all(c['reused_from']['report_sha256'] == selection['baseline_actual_passing_audit']['sha256'] for c in reused)
    assert set(audit['allowed_standard_axioms']) == ALLOWED
    assert all(set(a) <= ALLOWED for a in audit['axiom_dependencies'].values())
    assert len(audit['source_sha256']) == 31
    generated = 'verification/lean/SafeLearning.lean'
    for table in ['proof_sha256', 'source_sha256', 'project_sha256']:
        for name, fingerprint in audit[table].items():
            assert sha(RUNTIME + '/' + name) == preparation['source_hashes'][name] == fingerprint, name
            if name != generated:
                assert sha(name) == fingerprint, name
    aggregate = '\n'.join('import SafeLearning.' + Path(n).stem for n in sorted(selection['proof_files'])) + '\n'
    assert path(RUNTIME + '/' + generated).read_text() == aggregate
    assert native['status'] == 'passed' and native['actual_exit_code'] == 0
    assert native['actual_command'] == ['python3', RUNTIME + '/verification/lean/verify.py', '--reuse-kernel-from',
        str(path('reports/full-coverage/runtime-checkpoint-33-source88-v1'))]
    assert native['actual_workdir'] == str(ROOT) and sha(native['log']) == native['log_sha256']
    assert native['helper_sha256_before'] == native['helper_sha256_after']
    assert native['helper_sha256_before'][RUNTIME + '/verification/lean/verify.py'] == sha(RUNTIME + '/verification/lean/verify.py')
    assert peer['errors'] == [] and peer['new_whole_material_promotions'] == 7
    assert integration['applied'] is True and integration['coverage_complete'] is False
    assert integration['independent_peer'] == ref(PEER)
    assert integration['whole_material_units_completed'] == 7 and integration['exercises_completed'] == 2
    assert len(integration['exact_replacements']) == 4
    for replacement in integration['exact_replacements']:
        exact(replacement['candidate']); exact(replacement['preserved_original']); exact(replacement['exact_inverse'])
        assert sha(replacement['destination']) == replacement['candidate']['sha256']
    assert ledger['integrity_status'] == 'passed' and ledger['errors'] == [] and ledger['mathematical_coverage_complete'] is False
    assert ledger['counts']['exercises'] == 556 and ledger['counts']['material_source_units'] == 12774
    assert ledger['counts']['material_review_statuses'] == peer['material_counts'] == {'reviewed': 4858, 'pending': 7916}
    for name, count in peer['exercise_counts'].items():
        assert ledger['counts']['statuses'][name] == count
    assert ledger['inventory_sha256'] == sha('book/coverage/inventory.json')
    for domain in ledger['domains']:
        assert domain['ledger_sha256'] == sha('book/coverage/' + domain['domain'] + '.json')
    return selection, preparation, audit, integration, ledger


def export_audit(audit):
    original = path(ORIGINAL)
    files = sorted(p for p in original.rglob('*') if p.is_file())
    assert files and all(not p.is_symlink() for p in original.rglob('*'))
    hashes = {p.relative_to(original).as_posix(): sha(p.relative_to(ROOT).as_posix()) for p in files}
    for check in audit['checks']:
        if 'log_sha256' in check:
            assert check['output_file'].startswith('reports/lean-verification/')
            assert hashes[check['output_file'].removeprefix('reports/lean-verification/')] == check['log_sha256']

    def relocate(check):
        for table, key in [(check, 'output_file'), (check.get('reused_from', {}), 'report')]:
            value = table.get(key)
            if isinstance(value, str) and value.startswith('reports/lean-verification/'):
                table[key] = EXPORT + '/' + value.removeprefix('reports/lean-verification/')

    for source in files:
        name = source.relative_to(original).as_posix()
        target = EXPORT + '/' + ('verification-original.json' if name == 'verification.json' else name)
        if name == 'kernel-progress.json':
            data = json.loads(source.read_bytes())
            for check in data['checks'].values():
                relocate(check)
            put_exact(target, encode(data))
        else:
            put_exact(target, source.read_bytes())
    relocated = copy.deepcopy(audit)
    for check in relocated['checks']:
        relocate(check)
    relocated['audit_origin'] = dict(original_report=EXPORT + '/verification-original.json',
        original_report_sha256=sha(ORIGINAL + '/verification.json'), actual_workdir=str(path(RUNTIME + '/verification/lean')),
        actual_Root_execution=ref(NATIVE), source_only_runtime_preparation=ref(PREPARATION),
        scope='Only exported output/report locations change. Original commands, cwd, times and source hashes are retained. The snapshot records the actual runtime audit.')
    put_exact(EXPORT + '/verification.json', encode(relocated))
    assert all(sha(ORIGINAL + '/' + n) == h for n, h in hashes.items())


def freeze(selection, preparation, audit, integration, ledger):
    assert sha(EXPORT + '/verification-original.json') == sha(ORIGINAL + '/verification.json')
    if path(MANIFEST).exists():
        manifest = read(MANIFEST)
        assert manifest['selection_sha256'] == sha(SELECTION)
        assert manifest['owner_integration'] == ref(INTEGRATION)
        assert manifest['successful_verification']['report_sha256'] == sha(ORIGINAL + '/verification.json')
        assert manifest['working_ledger_audit'] == ref(LEDGER)
        assert manifest['frozen_ledger_audit'] == ref(FROZEN_LEDGER)
        for name, fingerprint in manifest['frozen_inputs_sha256'].items():
            assert sha(SNAPSHOT + '/' + name) == fingerprint, name
        return manifest
    files = set(audit['proof_sha256']) | set(audit['source_sha256']) | set(audit['project_sha256'])
    files |= {'book/coverage/' + n for n in ['inventory.json', 'material-corrections.json', 'core.json', 'foundations.json',
        'applied.json', 'modules.json', 'applied-promotions.json', 'validate.py', 'lean_names.py']}
    owners, excluded = {}, {}
    sys.path.insert(0, str(path('book/coverage')))
    from lean_names import declarations
    public = {d['name'] for n in audit['proof_sha256'] for d in declarations(path(n).read_text())}
    for domain in ['core', 'foundations', 'applied', 'modules']:
        owner = owners[domain] = read('book/coverage/' + domain + '.json')
        for n, h in owner.get('chapter_fragment_sha256', {}).items():
            assert n.startswith('book/chapters/') and sha(n) == h
            files.add(n)
        for claim in owner['material_claims'] + [c for e in owner['exercises'] for c in e['claims']]:
            assert set(claim['lean_declarations']) <= public
        excluded[domain] = sorted(set(owner['proof_files']) - set(audit['proof_sha256']))
        assert set(excluded[domain]) == (UNSELECTED_METADATA if domain == 'applied' else set())
    generated = 'verification/lean/SafeLearning.lean'
    inputs = {n: sha(n) for n in sorted(files) if n != generated}
    for name in sorted(files):
        if name == 'book/coverage/applied.json':
            owner = copy.deepcopy(owners['applied'])
            owner['proof_files'] = {n: r for n, r in owner['proof_files'].items() if n not in UNSELECTED_METADATA}
            if 'proof_sha256' in owner:
                owner['proof_sha256'] = {n: h for n, h in owner['proof_sha256'].items() if n not in UNSELECTED_METADATA}
            assert owner['exercises'] == owners['applied']['exercises'] and owner['material_claims'] == owners['applied']['material_claims']
            data = (json.dumps(owner, indent=2) + '\n').encode()
        else:
            data = path((RUNTIME + '/' if name == generated else '') + name).read_bytes()
        put_exact(SNAPSHOT + '/' + name, data)
    spec = importlib.util.spec_from_file_location('checkpoint34_frozen_validator', path('book/coverage/validate.py'))
    validator = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(validator)
    validator.ROOT = path(SNAPSHOT)
    if path(FROZEN_LEDGER).exists():
        frozen_audit = read(FROZEN_LEDGER)
    else:
        frozen_audit = validator.validate()
        assert frozen_audit['integrity_status'] == 'passed' and frozen_audit['errors'] == []
        assert frozen_audit['counts'] == ledger['counts'] and frozen_audit['mathematical_coverage_complete'] is False
        atomic(FROZEN_LEDGER, encode(frozen_audit))
    assert frozen_audit['integrity_status'] == 'passed' and frozen_audit['counts'] == ledger['counts']
    assert frozen_audit['inventory_sha256'] == sha('book/coverage/inventory.json')
    for domain in frozen_audit['domains']:
        assert domain['ledger_sha256'] == sha(SNAPSHOT + '/book/coverage/' + domain['domain'] + '.json')
    assert all(sha(n) == h for n, h in inputs.items())
    entries = list(path(SNAPSHOT).rglob('*'))
    assert all(not p.is_symlink() for p in entries)
    frozen = {p.relative_to(path(SNAPSHOT)).as_posix(): sha(p.relative_to(ROOT).as_posix()) for p in entries if p.is_file()}
    assert set(frozen) == files and not any({'.lake', '.git', '__pycache__'}.intersection(Path(n).parts) for n in frozen)
    assert all(frozen[n] == h for table in ['proof_sha256', 'source_sha256', 'project_sha256'] for n, h in audit[table].items())
    manifest = dict(status='formal_verification_passed_partial_coverage', created_at_utc=datetime.now(timezone.utc).isoformat(),
        snapshot=SNAPSHOT, selection=SELECTION, selection_sha256=sha(SELECTION), proof_files=selection['proof_files'],
        working_inputs_sha256=inputs, frozen_inputs_sha256=frozen, inventory_sha256=sha('book/coverage/inventory.json'),
        audited_runtime_source_input_sha256=__import__('hashlib').sha256(json.dumps(preparation['source_hashes'], sort_keys=True, separators=(',', ':')).encode()).hexdigest(),
        source_input_sha256_encoding='sha256(JSON source_hashes sorted keys, compact separators, UTF-8)',
        coverage_complete=False, source_only_snapshot=True, old_snapshot_or_lake_tree_copied=False,
        new_whole_material_units=7, exercises_completed=2, material_review_statuses=ledger['counts']['material_review_statuses'],
        excluded_unreferenced_ledger_metadata=excluded, owner_integration=ref(INTEGRATION),
        working_ledger_audit=ref(LEDGER), frozen_ledger_audit=ref(FROZEN_LEDGER),
        successful_verification=dict(report=EXPORT + '/verification-original.json', report_sha256=sha(ORIGINAL + '/verification.json'),
            actual_Root_execution=ref(NATIVE), actual_workdir=str(path(RUNTIME + '/verification/lean')),
            snapshot_execution_claimed=False, proof_files=1264, public_theorems=11459, fresh_kernel_replays=3, exact_reused_kernel_checks=1261),
        historical_provenance_not_recopied=dict(baseline_selection=selection['baseline_selection'],
            baseline_actual_audit=selection['baseline_actual_passing_audit'], scope='Original evidence retains its paths, hashes and times. No earlier snapshot or build tree is copied.'),
        limits=['Exercise and material coverage remain partial.', 'Source correspondence is independently reviewed; Lean verifies the encoded statements.',
            'Only three unused Applied proof metadata entries are omitted; every claim is retained.',
            'Finite floating scalar trajectories are observations, not an all-time formal proof or an audit of the 2D explorer.'])
    atomic(MANIFEST, (json.dumps(manifest, separators=(',', ':'), ensure_ascii=False) + '\n').encode())
    return manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--inputs', required=True, help='Exact JSON mapping from every finalized gate path to SHA256.')
    parser.add_argument('--stage', choices=['check', 'all', 'export', 'freeze'], default='check')
    args = parser.parse_args()
    args.inputs = json.loads(args.inputs)
    required = {SELECTION, PREPARATION, ORIGINAL + '/verification.json', NATIVE, INTEGRATION, LEDGER, READINESS, PEER, 'book/coverage/inventory.json'}
    assert set(args.inputs) == required
    selection, preparation, audit, integration, ledger = verify_inputs(args)
    if args.stage in ['all', 'export']:
        export_audit(audit)
    manifest = freeze(selection, preparation, audit, integration, ledger) if args.stage in ['all', 'freeze'] else None
    print(json.dumps(dict(status='passed_checkpoint34_' + args.stage, proof_files=1264, public_theorems=11459,
        fresh_kernel_replays=3, exact_reused_kernel_checks=1261,
        manifest=ref(MANIFEST) if manifest else None, coverage_complete=False)))


if __name__ == '__main__':
    main()
