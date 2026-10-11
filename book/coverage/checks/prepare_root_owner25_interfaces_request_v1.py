"""Prepare post-integration25 inputs and preserve exact closed report bytes."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json

ROOT = Path(__file__).resolve().parents[3]
BASE = 'book/coverage/checks/future25-core'
DEST = BASE + '/checkpoint25-live-owner-interface-preparation-request-v1.json'
BINDING = 'book/coverage/checks/root-owner25-reviewed-candidate-bindings-v2.json'

def sha(name):
    path = Path(name)
    assert not path.is_absolute() and '..' not in path.parts
    return hashlib.sha256((ROOT / path).read_bytes()).hexdigest()

def read(name): return json.loads((ROOT / name).read_text())
def ref(name): return {'file': name, 'sha256': sha(name)}

assert not (ROOT / DEST).exists()
execution_name = 'reports/full-coverage/owner25-integration-apply-execution-v1.json'
execution = read(execution_name)
assert type(execution['actual_exit_code']) is int and execution['actual_exit_code'] == 0
assert execution['actual_command'] == ['python3', 'book/coverage/checks/root_integrate_owner25_candidates_v3.py', BINDING, '--apply']
assert sha(execution['log']) == execution['log_sha256']
result_name = 'reports/full-coverage/owner25-reviewed-candidate-integration-v1.json'
result = read(result_name)
assert result['applied'] is True and result['binding_manifest_sha256'] == sha(BINDING)
global_name = 'reports/full-coverage/root-source52-final-owner-integration25-v1.json'
global_audit = read(global_name)
assert global_audit['integrity_status'] == 'passed' and global_audit['errors'] == []
binding = read(BINDING)
assert len(result['exact_replacements']) == 5 and binding['new_proof_sources'] == 12
report_hashes = {}
book_hashes = {}
for replaced in result['exact_replacements']:
    name = replaced['original24_byte_copy']
    assert name.startswith('reports/full-coverage/owner24-originals-before-owner25-integration-v1/')
    assert sha(name) == replaced['before_sha256']
    report_hashes[name] = replaced['before_sha256']
    assert sha(replaced['destination']) == replaced['candidate']['sha256']
for row in binding['owners'].values():
    refs = row['additional_exact_provenance'] + row['original_full_source_semantic_reviews'] + [row['reviewed_final_offer'], row['independent_candidate_mapping_peer'], row['actual_candidate_builder'], row['candidate_ledger']]
    for evidence in refs:
        assert sha(evidence['file']) == evidence['sha256']
        (book_hashes if evidence['file'].startswith('book/coverage/') else report_hashes)[evidence['file']] = evidence['sha256']
for prefix in ('owner25-', 'prepare-owner25-', 'root-core25-'):
    for path in (ROOT / 'reports/full-coverage').glob(prefix + '*'):
        if path.is_file() and path.suffix in {'.json', '.log'}:
            name = path.relative_to(ROOT).as_posix(); report_hashes[name] = sha(name)
for name in (global_name, 'reports/full-coverage/prepare-checkpoint24-selection-execution-v1.json', 'reports/full-coverage/prepare-checkpoint24-selection-execution-v1.log'):
    report_hashes[name] = sha(name)
alias_dir = ROOT / BASE / 'root-closed-report-original-bytes25-v1'
assert not alias_dir.exists(); alias_dir.mkdir()
aliases = []
for name, digest in sorted(report_hashes.items()):
    assert sha(name) == digest
    target = alias_dir / (digest + Path(name).suffix)
    if target.exists(): assert hashlib.sha256(target.read_bytes()).hexdigest() == digest
    else:
        with target.open('xb') as stream: stream.write((ROOT / name).read_bytes())
    canonical = target.relative_to(ROOT).as_posix(); book_hashes[canonical] = digest
    aliases.append({'original': ref(name), 'canonical_original_byte_copy': ref(canonical)})
alias_name = BASE + '/root-closed-report-original-byte-aliases25-v1.json'
with (ROOT / alias_name).open('x') as stream:
    stream.write(json.dumps({'status': 'completed_original_report_bytes_copied_exactly_without_rewriting_commands_times_or_status', 'aliases': aliases, 'scope': 'Original failures, successful builds and copy executions retain their actual bodies and times. These exact byte aliases do not imply new compiler or mathematical execution.'}, indent=2) + '\n')
book_hashes[alias_name] = sha(alias_name)
for folder in ('future25-core', 'foundations-future25', 'applied-future25', 'modules-future25'):
    for path in (ROOT / 'book/coverage/checks' / folder).rglob('*'):
        if path.is_file() and '__pycache__' not in path.parts and path.suffix in {'.json', '.log', '.py', '.lean', '.txt', '.cjs', '.md'}:
            name = path.relative_to(ROOT).as_posix(); book_hashes[name] = sha(name)
for evidence in (binding['helper'], binding['independent_helper_review'], binding['preparation_helper'], binding['current_future_code_update_authorization']):
    assert sha(evidence['file']) == evidence['sha256']; book_hashes[evidence['file']] = evidence['sha256']
book_hashes[BINDING] = sha(BINDING)
for folder in ('book/coverage', 'book/coverage/checks'):
    for path in (ROOT / folder).glob('*25*.py'):
        name = path.relative_to(ROOT).as_posix(); book_hashes[name] = sha(name)
old_selection_name = 'reports/full-coverage/checkpoint-24-selection.json'
old_selection = read(old_selection_name)
old_plan = read(old_selection['selection_plan'])
assert len(old_selection['proof_files']) == 1144
additional = {name: {'sha256': digest, 'scope': 'immutable_audit_or_local_source_evidence'} for name, digest in sorted(book_hashes.items())}
excluded = old_plan['excluded_full_external_reference_sha256']
for name, row in additional.items():
    assert sha(name) == row['sha256'] and row['sha256'] not in set(excluded)
dry_names = ('owner25-integration-dry-execution-v1.json', 'owner25-integration-dry-execution-v1.log', 'owner25-integration-dry-execution-v2.json', 'owner25-integration-dry-execution-v2.log', 'owner25-integration-guard-dry-run-v2.json')
prior = {
    'baseline_successful_selector_actual': ref('reports/full-coverage/prepare-checkpoint24-selection-execution-v1.json'),
    'baseline_successful_selector_raw_log': ref('reports/full-coverage/prepare-checkpoint24-selection-execution-v1.log'),
    'baseline_alias_preparation_helper': old_plan['baseline_owner_evidence_alias_plan_preparation_helper'],
    'baseline_selection_plan': ref(old_selection['selection_plan'])
}
out = {
    'status': 'root_authorized_postintegration_owner25_interface_preparation',
    'prepared_at_utc': datetime.now(timezone.utc).isoformat(),
    'inventory': ref('book/coverage/inventory-after-correction52.json'),
    'integration_binding': ref(BINDING), 'actual_integration_execution': ref(execution_name),
    'actual_integration_raw_log': ref(execution['log']), 'integration_result': ref(result_name),
    'live_offer_destinations': {owner: BASE + '/root25-live-' + owner + '-offer-v1.json' for owner in binding['owners']},
    'interface_manifest_destination': BASE + '/root25-live-owner-interface-manifest-v1.json',
    'production_plan_destination': BASE + '/checkpoint25-installed-owner-selection-plan-v1.json',
    'selection_helper': ref('book/coverage/prepare_checkpoint25_selection_v3.py'),
    'content_retainer': ref('book/coverage/retain_baseline_inputs25_v3.py'),
    'live_interface_helper': ref('book/coverage/prepare_checkpoint25_live_owner_interfaces_v3.py'),
    'additional_frozen_inputs': additional, 'excluded_full_external_reference_sha256': excluded,
    'historical_dry_run_evidence_sha256': {'reports/full-coverage/' + name: sha('reports/full-coverage/' + name) for name in dry_names},
    'closed_report_original_byte_aliases': ref(alias_name),
    'actual_source52_apply': ref('reports/full-coverage/source52-apply-execution-v1.json'),
    'actual_source52_postwrite': ref('book/coverage/checks/root-source-batch52/postwrite-source-integrity-v1.json'),
    'prior_checkpoint24_selection_provenance': prior,
    'scope': 'Only the post-integration request and original-byte aliases are prepared. Source52 and all31 assets remain identical to the completed24 snapshot. Prior full mathematical reviews and failed/passing executions retain their original hypotheses, bodies and times. Fresh aggregate25 verification remains required.'
}
for name in list(out['live_offer_destinations'].values()) + [out['interface_manifest_destination'], out['production_plan_destination']]:
    assert not (ROOT / name).exists()
with (ROOT / DEST).open('x') as stream: stream.write(json.dumps(out, ensure_ascii=False, indent=2) + '\n')
print(json.dumps({'request': ref(DEST), 'additional_inputs': len(additional), 'original_report_aliases': len(aliases)}))
