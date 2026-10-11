"""Independently inspect the Module-authored selector's actual produced bytes."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, sys

ROOT = Path(__file__).resolve().parents[3]
sys.dont_write_bytecode = True
sys.path.insert(0, str(ROOT / 'book/coverage'))
from lean_names import declarations

def safe(name):
    p = Path(name)
    assert not p.is_absolute() and '..' not in p.parts
    assert (ROOT / p).resolve().is_relative_to(ROOT.resolve())
    return ROOT / p
def sha(name): return hashlib.sha256(safe(name).read_bytes()).hexdigest()
def read(name): return json.loads(safe(name).read_text())
def ref(name): return {'file': name, 'sha256': sha(name)}

DEST = 'book/coverage/checks/future24-core/root-checkpoint24-production-output-independent-confirmation-v1.json'
assert not safe(DEST).exists()
selection_name = 'reports/full-coverage/checkpoint-24-selection.json'
selection = read(selection_name)
actual_name = 'reports/full-coverage/prepare-checkpoint24-selection-execution-v1.json'
actual = read(actual_name)
assert actual['actual_exit_code'] == 0 and sha(actual['log']) == actual['log_sha256']
assert actual['actual_command'][1] == 'book/coverage/prepare_checkpoint24_selection_v4.py'
assert actual['helper_sha256_before'] == actual['helper_sha256_after']
for name, digest in actual['helper_sha256_after'].items(): assert sha(name) == digest
assert selection['proof_file_count'] == len(selection['proof_files']) == 1144
assert selection['new_file_count'] == 13 and selection['coverage_complete'] is False
baseline = read('reports/full-coverage/checkpoint-23-selection.json')
manifest = read('reports/full-coverage/checkpoint-23-manifest.json')
assert len(baseline['proof_files']) == 1131 and len(manifest['frozen_inputs_sha256']) == 36910
plan = read(selection['selection_plan'])
assert sha(selection['selection_plan']) == selection['selection_plan_sha256']
authorized = plan['authorized_baseline_owner_evidence_aliases']['aliases']
integration = read(plan['authorized_baseline_owner_evidence_aliases']['integration_result']['file'])
installed = {r['destination']: r['candidate']['sha256'] for r in integration['exact_replacements']}
historical_rows = 0
for source, old in baseline['proof_files'].items():
    current = selection['proof_files'][source]
    assert current['sha256'] == old['sha256'] == sha(source)
    for key, value in old.items():
        if key != 'evidence_sha256': assert current[key] == value, (source, key)
    used = {n: authorized[n] for n in old['evidence_sha256'] if n in authorized}
    if used:
        historical_rows += 1
        original = current['checkpoint24_original_baseline_owner_evidence']
        assert original['original_row_body'] == old and original['authorized_original_path_aliases'] == used
    for name, digest in old['evidence_sha256'].items():
        if name in used:
            archive = used[name]['immutable_byte_copy']
            assert archive['sha256'] == digest == sha(archive['file'])
            assert current['evidence_sha256'][archive['file']] == digest
            if name in current['evidence_sha256']: assert current['evidence_sha256'][name] == installed[name] == sha(name)
        else: assert current['evidence_sha256'][name] == digest == sha(name)
assert historical_rows == sum(any(n in authorized for n in row['evidence_sha256']) for row in baseline['proof_files'].values()) and len(authorized) == 4
new_sources = set(selection['proof_files']) - set(baseline['proof_files'])
assert len(new_sources) == 13 and new_sources == set(plan['expected_new_proof_sources'])
public = []
for source, row in selection['proof_files'].items():
    assert sha(source) == row['sha256']
    public.extend(d['name'] for d in declarations(safe(source).read_text()) if d['kind'] in {'theorem', 'lemma'})
    for name, digest in row['evidence_sha256'].items(): assert sha(name) == digest, name
assert len(public) == len(set(public)) == 9279
for name, row in selection['extra_frozen_inputs'].items(): assert sha(name) == row['sha256']
binding_ref = selection['previous_frozen_input_content_binding']
assert sha(binding_ref['file']) == binding_ref['sha256']
bindings = read(binding_ref['file'])['input_bindings']
assert {r['original_frozen_path']: r['sha256'] for r in bindings} == manifest['frozen_inputs_sha256']
for row in bindings:
    assert sha(manifest['snapshot'] + '/' + row['original_frozen_path']) == row['sha256'] == sha(row['retained_input'])
global_report = read(selection['global_integrity'])
assert global_report['integrity_status'] == 'passed' and global_report['errors'] == []
for owner, row in plan['owners'].items(): assert sha(row['ledger']['file']) == row['ledger']['sha256']
out = {'status': 'passed_independent_root_actual_selection24_output_review', 'reviewed_at_utc': datetime.now(timezone.utc).isoformat(), 'reviewer': '/root', 'actual_checker': ref(str(Path(__file__).relative_to(ROOT))), 'selection': ref(selection_name), 'selection_plan': ref(selection['selection_plan']), 'original_actual_selection_execution': ref(actual_name), 'selected_proof_sources': 1144, 'public_theorems': 9279, 'new_sources': 13, 'all1131_baseline_proof_sources_and_non_evidence_fields_exact': True, 'four_original_owner_evidence_paths_preserved_with_entire_baseline_row_and_actual_archive_bytes': True, 'all36910_original_frozen_paths_and_bytes_retained': True, 'global_integrity': ref(selection['global_integrity']), 'errors': [], 'coverage_complete': False, 'scope': 'Independent byte and mapping review of the Module-authored selector output. No new Lean compilation, mathematical semantic decision, fresh historical kernel run or full coverage is inferred.'}
with safe(DEST).open('x') as f: f.write(json.dumps(out, indent=2) + '\n')
print(json.dumps({'status': 'passed', 'selection': ref(selection_name), 'sources': 1144, 'theorems': 9279}))
