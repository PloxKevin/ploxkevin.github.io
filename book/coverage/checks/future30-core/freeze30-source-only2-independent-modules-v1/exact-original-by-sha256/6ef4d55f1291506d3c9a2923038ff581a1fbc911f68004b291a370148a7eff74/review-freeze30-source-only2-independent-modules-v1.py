from pathlib import Path
from datetime import datetime, timezone
import ast, hashlib, json

ROOT = Path('/home/oxrexkevin/SafetyBased')
OUT = Path('/tmp/freeze30-source-only2-independent-modules-findings-v1.json')
PINS = {
    'book/coverage/freeze_checkpoint30_source_only_v2.py': 'b0019000f105ef923861437bbbe4ee6ae359cc42276351fdd7664d0164bed757',
    'book/coverage/freeze_checkpoint30_source_only_v1.py': '959ccba967210a9193c585b08418b07020a62a740b1d69d3f10704b1a76e3844',
    'book/coverage/lean_names.py': '9e00c114c57a2bb05939a21bee09679188aa97c855a8d10e61b160f31e10f07d',
    'verification/lean/verify.py': '4f39878e69cda33c5a04030c2c5bd8870dea32b7a798cdbf2a9aa23e372513a1',
    'reports/full-coverage/checkpoint-30-selection.json': '21c101dece9c614941e28174a5ff5ad6ead0fb271479f0c65cb732d10acdd196',
    'reports/full-coverage/lean-checkpoint-30/verification-original.json': '202ad21aa4a9f8e87a9dcebfdcec7a1a0ba415cf23eb37d794e65eef67a25a4c',
}

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(n): return {'file': n, 'sha256': sha(ROOT/n), 'bytes': (ROOT/n).stat().st_size}

assert not OUT.exists()
assert all(sha(ROOT/n) == h for n,h in PINS.items())
source = (ROOT/'book/coverage/freeze_checkpoint30_source_only_v2.py').read_text()
tree = ast.parse(source)
constants = {n.targets[0].id: ast.literal_eval(n.value) for n in tree.body
             if isinstance(n, ast.Assign) and isinstance(n.targets[0], ast.Name)
             and n.targets[0].id in {'SNAPSHOT','MANIFEST','SELECTION','SELECTION_SHA','AUDIT','INTEGRATION','UNSELECTED_METADATA'}}
assert constants['SELECTION_SHA'] == PINS['reports/full-coverage/checkpoint-30-selection.json']
assert constants['AUDIT'] == 'reports/full-coverage/lean-checkpoint-30-final-css-v1/verification-original.json'
assert constants['UNSELECTED_METADATA'] == {
    'verification/lean/SafeLearning/CompleteAppliedBinaryTemperaturePrecision.lean',
    'verification/lean/SafeLearning/CompleteAppliedBinaryVariationalPrecision.lean',
    'verification/lean/SafeLearning/CompleteAppliedConformalCalibrationOnly.lean'}
assert {n.name for n in tree.body if isinstance(n, ast.FunctionDef)} == {'path','sha','read','reference','main'}
selection = json.loads((ROOT/'reports/full-coverage/checkpoint-30-selection.json').read_bytes())
original = json.loads((ROOT/'reports/full-coverage/lean-checkpoint-30/verification-original.json').read_bytes())
assert original['proof_sha256'] == {n:r['sha256'] for n,r in selection['proof_files'].items()}
assert len(original['proof_sha256']) == original['proof_file_count'] == 1242
assert original['theorem_count'] == len(original['declarations']) == len(original['axiom_dependencies']) == 11080
assert len(original['checks']) == 1245 and all(c['exit_code'] == 0 for c in original['checks'])
assert len(original['source_sha256']) == 31 and len(original['project_sha256']) == 5
assert set(original['allowed_standard_axioms']) == {'Classical.choice','propext','Quot.sound'}
assert all(set(a) <= set(original['allowed_standard_axioms']) for a in original['axiom_dependencies'].values())
assert sum(c.get('evidence_mode') == 'fresh_kernel_replay' for c in original['checks']) == 45
assert sum(bool(c.get('reused_from')) for c in original['checks']) == 1197
for table in ['proof_sha256','source_sha256','project_sha256']:
    for n in original[table]:
        p = Path(n)
        assert p.as_posix() == n and not p.is_absolute() and '..' not in p.parts
        assert '.lake' not in p.parts and not any(part.startswith('checkpoint-') for part in p.parts)
assert all(sha(ROOT/n) == h for n,h in PINS.items())
findings = {
    'status': 'passed_independent_checkpoint30_source_only_freezer2_full_code_review',
    'errors': [], 'reviewer': '/root/modules_finish28', 'reviewed_at_utc': datetime.now(timezone.utc).isoformat(),
    'helper': ref('book/coverage/freeze_checkpoint30_source_only_v2.py'),
    'original_unexecuted_freezer1': ref('book/coverage/freeze_checkpoint30_source_only_v1.py'),
    'reviewed_helpers_sha256': {n:h for n,h in PINS.items() if n.endswith('.py')},
    'full_code_read': True, 'exact_v1_to_v2_delta_read': True,
    'auditor_verify_and_ledger_validator_full_code_read': True,
    'immutable_initial45_audit': ref('reports/full-coverage/lean-checkpoint-30/verification-original.json'),
    'actual_selection': ref('reports/full-coverage/checkpoint-30-selection.json'),
    'bounded_source_only_copy_protocol_approved': True,
    'physical_Root_path_and_no_symlink_ancestors_guards_read': True,
    'current_claim_declarations_must_all_exist_in_selected_source_public_names': True,
    'three_unused_Applied_metadata_entries_only_no_claim_removal': sorted(constants['UNSELECTED_METADATA']),
    'manifest_preserves_distinct_actual_runtime_and_future_source_only_snapshot_paths': True,
    'initial45_fresh1197_reuse_actual_audit_identity_verified': True,
    'expected_selected_sources':1242, 'expected_public_theorem_and_lemma_names':11080,
    'expected_site_assets':31, 'expected_project_inputs':5,
    'historical_snapshot_cache_or_recursive_evidence_trees_copied': False,
    'code_review_only':True, 'producer_invoked':False, 'compiler_invoked':False,
    'final_css_audit_export_ledger_or_freeze_approved_as_actual_output':False,
    'old79_context_guard_invoked':False,
    'scope': 'Full frozen helper2 code read and immutable selection/initial-audit schema association. Actual execution is conditional on the future final-CSS genuine audit/export, installed candidate integrity and ledger hash CLI prerequisites. This reader does not import or invoke the producer and does not guard mutable assets or owners during the Root transition.',
    'future_prerequisites': [
        'CLI hash must identify the genuine exported final-CSS original audit, whose source/project/proof bytes match both final runtime and live Root before copying.',
        'Installed candidate byte identities and a genuine passing current inventory/ledger integrity report must satisfy all existing assertions.',
        'The snapshot and manifest must be previously absent; source mutations remain Root actions.'],
}
OUT.write_text(json.dumps(findings,indent=2)+'\n')
print(json.dumps({'status':findings['status'],'errors':[],'selected_sources':1242,'public_names':11080,'code_review_only':True,'producer_invoked':False}))
