"""Preflight and install five exact reviewed Source81 owner candidates.

Only the named owner files change. Actual Lean pairs and independent full
mapping approvals are prerequisites; aggregate verification remains separate.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, importlib.util, json, re, sys, tempfile
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[3]
SELF = 'book/coverage/checks/root_integrate_owner31_candidates_v4.py'
CONTEXT = Path('/tmp/root_tmp_lean_current81_historical_owner30_context_v1.json')
CONTEXT_SHA = 'f9490760c85e8be1392f271bdf65e193e5a5e4cfc2ba29b5f7e4d32c682a7af9'
SELECTION = 'reports/full-coverage/checkpoint-31-selection.json'
SELECTION_SHA = 'cfe49bb94bf13fe8e464df60213a6639ffb99e63383f2f9300b93ef8a21d33da'
READINESS = 'book/coverage/checks/future31-core/current81-canonical-pairs6-v1/actual-reviewed31-canonical-paired-readiness-v1.json'
READINESS_SHA = 'c18752bbf4b29ef8218cb28d990aad7edfcf0220babe2bacbafb3101bde43520'
NATIVE = 'reports/full-coverage/current81-canonical31-six-paired-application-execution-v1.json'
INVENTORY_SHA = 'b1e914086b3b3ab104bbfff6a647ad5488f6797b2a6f3e4f6aa7ffcb5aa74ef5'
ARCHIVE = 'reports/full-coverage/owner30-originals-before-owner31-integration-v4'
RESULT = 'reports/full-coverage/owner31-reviewed-candidate-integration-v4.json'
OWNERS = ['core', 'foundations', 'applied', 'modules', 'applied-promotions']
NEW_OWNERS = {
 'verification/lean/SafeLearning/CompleteFoundationsSpectralInductionSketch31.lean': 'foundations',
 'verification/lean/SafeLearning/CompleteFoundationsLogCubeCrossover31.lean': 'foundations',
 'verification/lean/SafeLearning/CompleteFoundationsGrowthExamplesLogDetTaylor31.lean': 'foundations',
 'verification/lean/SafeLearning/CompleteFoundationsExplorerCaptionModels31.lean': 'foundations',
 'verification/lean/SafeLearning/CompleteModulesIntegralTrackingWhole31.lean': 'modules',
 'verification/lean/SafeLearning/CompleteCoreFilippovEulerConstruction31.lean': 'core',
}

def path(n, exists=True):
    assert isinstance(n, str) and n and not Path(n).is_absolute() and '..' not in Path(n).parts
    assert not any(c in n for c in '\0\n\r')
    p = ROOT/n; assert p.resolve().is_relative_to(ROOT) and not p.is_symlink()
    assert all(not q.is_symlink() for q in p.parents if q.is_relative_to(ROOT))
    if exists: assert p.is_file()
    return p
def sha(n): return hashlib.sha256(path(n).read_bytes()).hexdigest()
def read(n): return json.loads(path(n).read_bytes())
def ref(n): return {'file': n, 'sha256': sha(n), 'bytes': path(n).stat().st_size}
def checked(r, parse=True):
    assert isinstance(r, dict) and {'file', 'sha256'} <= set(r) <= {'file', 'sha256', 'bytes'}
    assert re.fullmatch('[0-9a-f]{64}', r['sha256']) and sha(r['file']) == r['sha256']
    if 'bytes' in r: assert path(r['file']).stat().st_size == r['bytes']
    return read(r['file']) if parse else path(r['file'])
def new(n, data):
    p = path(n, False); assert not p.exists(); p.parent.mkdir(parents=True, exist_ok=True)
    with p.open('xb') as f: f.write(data)
def encode(d): return (json.dumps(d, indent=2, ensure_ascii=False)+'\n').encode()
def pointer(data, keys):
    assert isinstance(keys, list) and keys
    for key in keys: data = data[key]
    return data
def proof_hashes(data):
    if isinstance(data['proof_files'], dict):
        return {n: r['sha256'] if isinstance(r, dict) else r for n, r in data['proof_files'].items()}
    assert isinstance(data['proof_files'], list)
    assert set(data['proof_files']) == set(data['proof_sha256'])
    return data['proof_sha256']
def zero(d):
    codes = [d[k] for k in ['actual_exit_code', 'exit_code', 'actual_runner_exit_code'] if k in d]
    assert codes and all(type(c) is int and c == 0 for c in codes)
    assert d.get('protection_errors', []) == []
def normalize_alias(original_name, alias):
    if 'file' in alias and 'sha256' in alias:
        row = alias
    else:
        original = alias['original']; assert original['file'] == original_name
        choices = [alias[k] for k in ['original_byte_copy', 'already_durable_exact_reference'] if k in alias]
        assert len(choices) == 1
        row = choices[0]; assert row['sha256'] == original['sha256']
        if 'bytes' in original: assert path(row['file']).stat().st_size == original['bytes']
    checked(row, False)
    return {'file': row['file'], 'sha256': row['sha256'], 'bytes': path(row['file']).stat().st_size}
def success_native(r, aliases):
    data = checked(r); zero(data); assert data['status'].startswith('passed')
    assert data['helper_sha256_before'] == data['helper_sha256_after']
    log = data.get('raw_log', data.get('log')); digest = data.get('raw_log_sha256', data.get('log_sha256'))
    if isinstance(log, dict): checked(log, False)
    elif Path(log).is_absolute():
        alias = aliases[log]
        if 'sha256' in alias and 'file' in alias:
            row = alias
        else:
            original = alias['original']
            assert original['file'] == log and original['sha256'] == digest
            choices = [alias[k] for k in ['original_byte_copy', 'already_durable_exact_reference'] if k in alias]
            assert len(choices) == 1
            row = choices[0]
            if 'bytes' in original: assert row.get('bytes', path(row['file']).stat().st_size) == original['bytes']
        assert row['sha256'] == digest; checked(row, False)
    else: assert sha(log) == digest
    return data

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--binding', required=True); parser.add_argument('--binding-sha256', required=True)
    parser.add_argument('--code-peer', required=True); parser.add_argument('--code-peer-sha256', required=True)
    parser.add_argument('--preflight-output', required=True); parser.add_argument('--apply', action='store_true')
    args = parser.parse_args()
    assert Path(__file__).resolve() == ROOT/SELF
    assert hashlib.sha256(CONTEXT.read_bytes()).hexdigest() == CONTEXT_SHA
    context = json.loads(CONTEXT.read_bytes()); held = {**context['pins_sha256'], **context['held_current_source_sha256']}
    baseline_owners = context['owners_sha256']
    assert len(baseline_owners) == 5 and sha(SELECTION) == SELECTION_SHA and sha(READINESS) == READINESS_SHA
    assert sha('book/coverage/inventory.json') == INVENTORY_SHA
    selection, readiness, native = read(SELECTION), read(READINESS), read(NATIVE)
    assert selection['proof_file_count'] == 1248 and readiness['source_count'] == 6 and readiness['public_theorem_count'] == 104
    assert set(NEW_OWNERS) == {r['canonical_source'] for r in readiness['sources']}
    zero(native); assert native['status'] == 'passed' and sha(native['log']) == native['log_sha256']
    for n, row in selection['proof_files'].items(): held[n] = row['sha256']
    binding_ref = {'file': args.binding, 'sha256': args.binding_sha256}; binding = checked(binding_ref)
    assert binding['status'] == 'exact_source81_five_owner31_reviewed_candidate_byte_bindings_only'
    code_ref = {'file': args.code_peer, 'sha256': args.code_peer_sha256}; code = checked(code_ref)
    assert code['status'].startswith('passed') and code['errors'] == [] and code['full_code_read'] is True and code['reviewed_helper'] == ref(SELF)
    immutable = {SELF: sha(SELF), args.binding: args.binding_sha256, args.code_peer: args.code_peer_sha256, SELECTION: SELECTION_SHA, READINESS: READINESS_SHA, NATIVE: sha(NATIVE), 'book/coverage/validate.py': sha('book/coverage/validate.py')}
    replacements = binding['replacements']; assert len(replacements) == 5
    assert {r['destination'] for r in replacements} == {f'book/coverage/{o}.json' for o in OWNERS}
    for row in replacements:
        dest = row['destination']; owner = Path(dest).stem
        assert row['before_sha256'] == baseline_owners[dest] == sha(dest)
        candidate = checked(row['candidate']); approval = checked(row['independent_mapping_peer'])
        assert approval['status'] == row['expected_peer_status'] and approval['errors'] == []
        assert pointer(approval, row['peer_candidate_pointer']) == row['candidate']
        assert row['required_true_peer_fields'] and all(pointer(approval, keys) is True for keys in row['required_true_peer_fields'])
        aliases = {}
        for key in ['all_original_byte_aliases', 'actual_reader_original_byte_aliases', 'actual_finalizer_original_byte_aliases']:
            table = approval.get(key, {}); assert isinstance(table, dict)
            for original, alias in table.items():
                normalized = normalize_alias(original, alias)
                if original in aliases:
                    assert aliases[original]['sha256'] == normalized['sha256'] and aliases[original]['bytes'] == normalized['bytes']
                else: aliases[original] = normalized
        success_native(approval['actual_reader'], aliases)
        immutable[row['candidate']['file']] = row['candidate']['sha256']; immutable[row['independent_mapping_peer']['file']] = row['independent_mapping_peer']['sha256']
        if owner != 'applied-promotions':
            old = read(dest); before_proofs, after_proofs = proof_hashes(old), proof_hashes(candidate)
            additions = {n: selection['proof_files'][n]['sha256'] for n, o in NEW_OWNERS.items() if o == owner}
            assert after_proofs == {**before_proofs, **additions}
            if isinstance(old['proof_files'], dict):
                assert all(candidate['proof_files'][n] == r for n, r in old['proof_files'].items())
            else: assert candidate['proof_files'][:len(old['proof_files'])] == old['proof_files']
            for n, h in after_proofs.items(): assert sha(n) == h
    assert not path(ARCHIVE, False).exists() and not path(RESULT, False).exists()
    assert args.preflight_output.startswith('reports/full-coverage/') and args.preflight_output.endswith('.json') and not path(args.preflight_output, False).exists()
    def guard():
        for n, h in {**held, **immutable}.items(): assert sha(n) == h, n
    guard()
    with tempfile.TemporaryDirectory(prefix='owner31-reviewed-candidate-preflight-') as td:
        temporary = Path(td); (temporary/'book/coverage').mkdir(parents=True); (temporary/'verification').mkdir()
        (temporary/'SafeLearning').symlink_to(ROOT/'SafeLearning', target_is_directory=True)
        (temporary/'verification/lean').symlink_to(ROOT/'verification/lean', target_is_directory=True)
        (temporary/'book/coverage/inventory.json').symlink_to(path('book/coverage/inventory.json'))
        for row in replacements: (temporary/row['destination']).symlink_to(path(row['candidate']['file']))
        sys.path.insert(0, str(ROOT/'book/coverage'))
        spec = importlib.util.spec_from_file_location('owner31_isolated_integrity', path('book/coverage/validate.py'))
        validator = importlib.util.module_from_spec(spec); spec.loader.exec_module(validator); validator.ROOT = temporary
        report = validator.validate()
    guard(); new(args.preflight_output, encode(report))
    assert report['integrity_status'] == 'passed' and report['errors'] == [] and report['mathematical_coverage_complete'] is False
    assert report['counts']['exercises'] == 556 and report['counts']['material_source_units'] == 12774
    if 'expected_counts' in binding: assert report['counts'] == binding['expected_counts']
    if not args.apply:
        print(json.dumps({'status': 'passed_actual_source81_owner31_isolated_preflight_no_raw_writes', 'preflight': ref(args.preflight_output), 'counts': report['counts'], 'coverage_complete': False})); return
    for n, h in baseline_owners.items(): assert sha(n) == h
    for row in replacements:
        target = ARCHIVE+'/'+Path(row['destination']).name
        new(target, path(row['destination']).read_bytes()); row['original30_byte_copy'] = ref(target)
    guard()
    for row in replacements:
        assert sha(row['destination']) == row['before_sha256']
        path(row['destination']).write_bytes(path(row['candidate']['file']).read_bytes())
        assert sha(row['destination']) == row['candidate']['sha256']
    guard()
    result = {'status': 'five_exact_reviewed_source81_owner31_candidates_installed_pending_fresh_global_and_combined_audit', 'applied': True, 'installed_at_utc': datetime.now(timezone.utc).isoformat(), 'actual_helper': ref(SELF), 'binding': binding_ref, 'code_peer': code_ref, 'inventory_sha256': INVENTORY_SHA, 'selection31': ref(SELECTION), 'actual_six_source_twelve_command_readiness': ref(READINESS), 'actual_primary_execution': ref(NATIVE), 'exact_replacements': replacements, 'actual_isolated_preflight': ref(args.preflight_output), 'counts': report['counts'], 'new_canonical_files': 6, 'new_public_theorems': 104, 'coverage_complete': False, 'aggregate_kernel_axiom_freeze_or_publication_success_claimed': False, 'old_snapshot_or_lake_tree_copied': False}
    new(RESULT, encode(result)); print(json.dumps({'status': result['status'], 'result': ref(RESULT), 'counts': report['counts'], 'coverage_complete': False}))

if __name__ == '__main__': main()
