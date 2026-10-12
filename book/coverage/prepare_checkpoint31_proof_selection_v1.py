"""Select six genuinely compiled additions without copying prior proof metadata."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json

ROOT = Path(__file__).resolve().parents[2]
BASE = 'reports/full-coverage/checkpoint-30-selection.json'
BASE_SHA = '21c101dece9c614941e28174a5ff5ad6ead0fb271479f0c65cb732d10acdd196'
AUDIT = 'reports/full-coverage/lean-checkpoint-30-final-css-v1/verification-original.json'
AUDIT_SHA = '78915d21ec383430a5abea1c4b3cc9753dcfd5b2f94adb4834471459a3e2b00c'
READY = 'book/coverage/checks/future31-core/current81-canonical-pairs6-v1/actual-reviewed31-canonical-paired-readiness-v1.json'
READY_SHA = 'c18752bbf4b29ef8218cb28d990aad7edfcf0220babe2bacbafb3101bde43520'
NATIVE = 'reports/full-coverage/current81-canonical31-six-paired-application-execution-v1.json'
INV = 'book/coverage/inventory-after-correction81.json'
INV_SHA = 'b1e914086b3b3ab104bbfff6a647ad5488f6797b2a6f3e4f6aa7ffcb5aa74ef5'
OUT = ROOT/'reports/full-coverage/checkpoint-31-selection.json'

def sha(n): return hashlib.sha256((ROOT/n).read_bytes()).hexdigest()
def ref(n): return {'file': n, 'sha256': sha(n)}
def read(n): return json.loads((ROOT/n).read_bytes())
def exact(r):
    assert not Path(r['file']).is_absolute() and '..' not in Path(r['file']).parts
    assert sha(r['file']) == r['sha256']

assert not OUT.exists()
for n, h in [(BASE, BASE_SHA), (AUDIT, AUDIT_SHA), (READY, READY_SHA), (INV, INV_SHA)]: assert sha(n) == h
assert sha('book/coverage/inventory.json') == INV_SHA
base, audit, ready, native = [read(n) for n in [BASE, AUDIT, READY, NATIVE]]
assert base['proof_file_count'] == len(base['proof_files']) == audit['proof_file_count'] == 1242
assert audit['status'] == 'passed' and audit['theorem_count'] == 11080
assert audit['proof_sha256'] == {n: r['sha256'] for n, r in base['proof_files'].items()}
assert ready['status'] == 'passed_actual_reviewed31_canonical_standalone_and_named_pairs_unselected' and ready['errors'] == []
assert ready['source_count'] == 6 and ready['public_theorem_count'] == 104 and ready['actual_compiler_command_count'] == 12
assert native['status'] == 'passed' and native['actual_exit_code'] == 0 and native['helper_sha256_before'] == native['helper_sha256_after']
assert sha(native['log']) == native['log_sha256']
selected = {}
for n, row in base['proof_files'].items():
    assert sha(n) == row['sha256']
    selected[n] = {'sha256': row['sha256'], 'original_checkpoint30_metadata': {'file': BASE, 'sha256': BASE_SHA, 'JSON_pointer': ['proof_files', n]}, 'original_actual_passing_audit': ref(AUDIT), 'evidence_scope': 'Exact previously selected and kernel-verified Source30 bytes; all original metadata remains in the immutable selection30 file.'}
for row in ready['sources']:
    n = row['canonical_source']; assert n not in selected and sha(n) == row['original_tmp_source']['sha256']
    pairs = [p for p in ready['actual_paired_records'] if p['source']['file'] == n]
    assert len(pairs) == 2 and {p['kind'] for p in pairs} == {'standalone', 'named'}
    evidence = {}
    for pair in pairs:
        assert pair['actual_exit_code'] == 0 and pair['source']['sha256'] == sha(n)
        for k in ['actual_record', 'raw_log', 'source_snapshot']:
            r = pair[k]; exact(r); evidence[r['file']] = r['sha256']
        actual = read(pair['actual_record']['file'])
        assert actual['exit_code'] == 0 and actual['source_sha256_before'] == actual['source_sha256_after'] == sha(n)
    selected[n] = {'sha256': sha(n), 'actual_pair': pairs, 'evidence_sha256': evidence, 'public_theorem_count': row['public_theorem_count'], 'independent_source_peers': row['independent_source_peers'], 'evidence_scope': 'Two genuine Source81 local compiler commands passed. Whole-source correspondence and the new combined kernel/axiom audit remain separately recorded.'}
assert len(selected) == 1248
result = {'status': 'actual_source81_compiled_proof_selection_owner_mapping_and_aggregate_separate', 'created_at_utc': datetime.now(timezone.utc).isoformat(), 'baseline_selection': ref(BASE), 'baseline_original_metadata_is_preserved_by_exact_file_hash_and_JSON_pointer': True, 'actual_passing_baseline_audit': ref(AUDIT), 'current_inventory': ref(INV), 'actual_new6_compiler_pairs': ref(READY), 'actual_new6_compiler_execution': ref(NATIVE), 'proof_files': selected, 'proof_file_count': 1248, 'new_file_count': 6, 'expected_public_theorem_count_pending_actual_aggregate': 11184, 'historical_extra_inputs_not_recopied_into_new_snapshot': True, 'coverage_complete': False, 'owner_identity_rebase_or_whole_promotion_claimed': False, 'aggregate_or_kernel_or_axiom_audit_claimed': False}
with OUT.open('x') as f: f.write(json.dumps(result, indent=2)+'\n')
print(json.dumps({'status': result['status'], 'selection': ref(str(OUT.relative_to(ROOT))), 'proof_files': 1248, 'new_files': 6, 'expected_theorems_pending_actual_aggregate': 11184, 'coverage_complete': False}))
