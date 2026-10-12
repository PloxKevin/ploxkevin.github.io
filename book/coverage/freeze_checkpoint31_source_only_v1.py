"""Freeze exact audited sources and reviewed ledgers without copying archives.

The actual Lean audit ran in runtime-checkpoint-31. This snapshot mirrors its
source bytes; it does not claim that a compiler ran in the snapshot directory.
Historical compiler records remain at their original paths and in Git history.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, json, shutil

ROOT = Path(__file__).resolve().parents[2]
SNAPSHOT = 'reports/full-coverage/checkpoint-31'
MANIFEST = 'reports/full-coverage/checkpoint-31-manifest.json'
SELECTION = 'reports/full-coverage/checkpoint-31-selection.json'
SELECTION_SHA = 'cfe49bb94bf13fe8e464df60213a6639ffb99e63383f2f9300b93ef8a21d33da'
AUDIT = 'reports/full-coverage/lean-checkpoint-31-source81-v1/verification-original.json'
INTEGRATION = 'reports/full-coverage/owner31-reviewed-candidate-integration-v4.json'
RUNTIME = ROOT / 'reports/full-coverage/runtime-checkpoint-31-source81-v1'
UNSELECTED_METADATA = {
    'verification/lean/SafeLearning/CompleteAppliedBinaryTemperaturePrecision.lean',
    'verification/lean/SafeLearning/CompleteAppliedBinaryVariationalPrecision.lean',
    'verification/lean/SafeLearning/CompleteAppliedConformalCalibrationOnly.lean',
}


def path(n):
    assert type(n) is str and n and Path(n).as_posix() == n
    assert not Path(n).is_absolute() and '..' not in Path(n).parts
    assert not any(c in n for c in '\0\n\r')
    p = ROOT / n
    assert p.resolve().is_relative_to(ROOT) and not p.is_symlink()
    assert all(not q.is_symlink() for q in p.parents if q.is_relative_to(ROOT))
    return p


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def read(n, expected=None):
    p = path(n)
    if expected is not None:
        assert sha(p) == expected, n
    return json.loads(p.read_bytes())


def reference(n):
    return {'file': n, 'sha256': sha(path(n))}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--actual-audit-sha256', required=True)
    ap.add_argument('--ledger', required=True)
    ap.add_argument('--ledger-sha256', required=True)
    args = ap.parse_args()
    audit_sha = args.actual_audit_sha256
    assert not path(SNAPSHOT).exists() and not path(MANIFEST).exists()
    selection = read(SELECTION, SELECTION_SHA)
    audit = read(AUDIT, audit_sha)
    integration = read(INTEGRATION)
    ledger = read(args.ledger, args.ledger_sha256)
    assert integration['applied'] is True and integration['coverage_complete'] is False
    assert integration['new_canonical_files'] == 6 and integration['new_public_theorems'] == 104
    assert ledger['integrity_status'] == 'passed' and ledger['errors'] == []
    assert ledger['mathematical_coverage_complete'] is False
    assert ledger['counts']['exercises'] == 556 and ledger['counts']['material_source_units'] == 12774
    assert len(audit['proof_sha256']) == len(selection['proof_files']) == audit['proof_file_count'] == 1248
    assert audit['proof_sha256'] == {n: r['sha256'] for n, r in selection['proof_files'].items()}
    assert audit['status'] == 'passed' and audit['theorem_count'] == 11184
    assert len(audit['checks']) == 1251 and all(c['exit_code'] == 0 for c in audit['checks'])
    assert all(set(a) <= {'Classical.choice', 'propext', 'Quot.sound'} for a in audit['axiom_dependencies'].values())
    assert len(audit['source_sha256']) == 31
    for r in integration['exact_replacements']:
        assert sha(path(r['destination'])) == r['candidate']['sha256']
    assert ledger['inventory_sha256'] == sha(path('book/coverage/inventory.json'))
    for d in ledger['domains']:
        assert d['ledger_sha256'] == sha(path('book/coverage/' + d['domain'] + '.json'))
    native = read('reports/full-coverage/verify-runtime-checkpoint31-source81-execution-v1.json')
    assert native['status'] == 'passed' and native['actual_exit_code'] == 0
    assert native['actual_command'][1] == 'reports/full-coverage/runtime-checkpoint-31-source81-v1/verification/lean/verify.py'
    assert sha(path(native['log'])) == native['log_sha256']
    files = set(audit['proof_sha256']) | set(audit['source_sha256']) | set(audit['project_sha256'])
    files |= {'book/coverage/' + n for n in [
        'inventory.json', 'material-corrections.json', 'core.json', 'foundations.json',
        'applied.json', 'modules.json', 'applied-promotions.json', 'validate.py', 'lean_names.py']}
    for domain in ['core', 'foundations', 'applied', 'modules']:
        owner = read('book/coverage/' + domain + '.json')
        fragments = owner.get('chapter_fragment_sha256', {})
        for n, h in fragments.items():
            assert n.startswith('book/chapters/') and sha(path(n)) == h
            files.add(n)
    from lean_names import declarations
    public = {r['name'] for n in audit['proof_sha256'] for r in declarations(path(n).read_text())}
    excluded = {}
    for domain in ['core', 'foundations', 'applied', 'modules']:
        owner = read('book/coverage/' + domain + '.json')
        for claim in owner.get('material_claims', []) + [c for e in owner['exercises'] for c in e['claims']]:
            assert set(claim['lean_declarations']) <= public
        excluded[domain] = sorted(set(owner['proof_files']) - set(audit['proof_sha256']))
        assert set(excluded[domain]) == (UNSELECTED_METADATA if domain == 'applied' else set())
    generated = 'verification/lean/SafeLearning.lean'
    inputs = {n: sha(path(n)) for n in sorted(files) if n != generated}
    protections = {**inputs, SELECTION: SELECTION_SHA, AUDIT: audit_sha,
                   INTEGRATION: sha(path(INTEGRATION)), args.ledger: args.ledger_sha256}
    for table in ['proof_sha256', 'source_sha256', 'project_sha256']:
        for n, h in audit[table].items():
            assert sha(RUNTIME / n) == h
            assert n == generated or inputs[n] == h
    snapshot = path(SNAPSHOT)
    snapshot.mkdir()
    for n in sorted(files):
        source = RUNTIME / n if n == generated else path(n)
        target = snapshot / n
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
        assert sha(target) == (audit['project_sha256'][n] if n == generated else inputs[n])
    owner_path = snapshot / 'book/coverage/applied.json'
    applied = json.loads(owner_path.read_bytes())
    assert isinstance(applied['proof_files'], dict)
    applied['proof_files'] = {n: r for n, r in applied['proof_files'].items() if n not in UNSELECTED_METADATA}
    if 'proof_sha256' in applied:
        applied['proof_sha256'] = {n: h for n, h in applied['proof_sha256'].items() if n not in UNSELECTED_METADATA}
    owner_path.write_text(json.dumps(applied, indent=2) + '\n')
    assert protections == {n: sha(path(n)) for n in protections}
    frozen = {p.relative_to(snapshot).as_posix(): sha(p) for p in snapshot.rglob('*') if p.is_file()}
    assert not any('.lake' in Path(n).parts or 'checkpoint-' in n for n in frozen)
    assert all(frozen[n] == h for table in ['proof_sha256', 'source_sha256', 'project_sha256'] for n, h in audit[table].items())
    manifest = {
        'status': 'formal_verification_passed_partial_coverage',
        'created_at_utc': datetime.now(timezone.utc).isoformat(),
        'snapshot': SNAPSHOT, 'selection': SELECTION, 'selection_sha256': SELECTION_SHA,
        'proof_files': selection['proof_files'], 'working_inputs_sha256': inputs,
        'frozen_inputs_sha256': frozen, 'coverage_complete': False,
        'source_only_snapshot': True,
        'baseline_checkpoint30_actual_audit': {'file': 'reports/full-coverage/lean-checkpoint-30-final-css-v1/verification-original.json', 'sha256': '78915d21ec383430a5abea1c4b3cc9753dcfd5b2f94adb4834471459a3e2b00c'}, 'old_snapshot_or_lake_tree_copied': False,
        'excluded_unreferenced_ledger_metadata': excluded,
        'owner_integration': reference(INTEGRATION),
        'working_ledger_audit': {'file': args.ledger, 'sha256': args.ledger_sha256},
        'successful_verification': {'report': AUDIT, 'report_sha256': audit_sha,
            'actual_Root_execution': reference('reports/full-coverage/verify-runtime-checkpoint31-source81-execution-v1.json'),
            'actual_workdir': str(RUNTIME / 'verification/lean'),
            'snapshot_execution_claimed': False, 'proof_files': 1248, 'public_theorems': 11184},
        'historical_provenance_not_recopied': {
            'baseline_selection': selection['baseline_selection'],
            'publication_commit_before_checkpoint31': '676db1f7d13ddbf65c2f0253d1fab79c44948a7e',
            'scope': 'Earlier original bodies and native records remain at their original Root/Git paths, identified by original hashes and JSON pointers. This source-only freeze is not a recursive evidence archive.'},
        'limits': ['Exercise and material coverage remain partial.',
                   'Lean checked the encoded statements; independent reviews establish source correspondence.',
                   'The same exact Lean/site/project bytes were audited in runtime-checkpoint-31-source81-v1 before this source-only copy.',
                   'Only three unused Applied proof metadata entries are omitted from the frozen ledger; all claims and historical bodies are retained.']}
    with path(MANIFEST).open('x') as f:
        f.write(json.dumps(manifest, separators=(',', ':')) + '\n')
    print(json.dumps({'status': manifest['status'], 'source_only': True,
                      'snapshot_files': len(frozen), 'snapshot_bytes': sum(p.stat().st_size for p in snapshot.rglob('*') if p.is_file()),
                      'proof_files': 1248, 'public_theorems': 11184, 'coverage_complete': False,
                      'manifest': reference(MANIFEST)}))


if __name__ == '__main__':
    main()
