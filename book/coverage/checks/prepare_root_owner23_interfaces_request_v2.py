"""Prepare post-integration inputs and exact aliases of closed report evidence."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, shutil

ROOT = Path(__file__).resolve().parents[3]
BASE = 'book/coverage/checks/future23-core'
DEST = BASE + '/checkpoint23-live-owner-interface-preparation-request-v1.json'
BINDING = 'book/coverage/checks/root-owner23-reviewed-candidate-bindings-v1.json'

def sha(name): return hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
def read(name): return json.loads((ROOT / name).read_text())
def ref(name): return {'file': name, 'sha256': sha(name)}

assert not (ROOT / DEST).exists()
execution_name = 'reports/full-coverage/owner23-integration-apply-execution-v1.json'
execution = read(execution_name)
assert execution['actual_exit_code'] == 0
result_name = 'reports/full-coverage/owner23-reviewed-candidate-integration-v1.json'
result = read(result_name)
assert result['applied'] is True
binding = read(BINDING)
report_hashes = {}
book_hashes = {}
for row in binding['owners'].values():
    for r in row['additional_exact_provenance'] + row['original_full_source_semantic_reviews'] + [row['reviewed_final_offer'], row['independent_candidate_mapping_peer'], row['actual_candidate_builder'], row['candidate_ledger']]:
        assert sha(r['file']) == r['sha256']
        (book_hashes if r['file'].startswith('book/coverage/') else report_hashes)[r['file']] = r['sha256']

for prefix in ('owner23-', 'source49-', 'source50-', 'source51-', 'core23-', 'static-checkpoint23-', 'browser-checkpoint23-', 'browser-source51-23-'):
    for p in (ROOT / 'reports/full-coverage').glob(prefix + '*'):
        if p.is_file() and p.suffix in {'.json', '.log'}:
            name = str(p.relative_to(ROOT)); report_hashes[name] = sha(name)
for name in ('reports/full-coverage/integration-23.json', 'reports/full-coverage/browser-checkpoint-23.json', 'reports/full-coverage/browser-corrections-23.json', 'reports/full-coverage/browser-corrections-23.log', 'reports/full-coverage/browser-corrections-23-inputs.json'):
    report_hashes[name] = sha(name)
# Browser PNGs are preserved by the explicit post-audit publication stage.
# The allowed extra-input schema freezes textual audit evidence only.
for folder in ('browser-artifacts-23',):
    for p in (ROOT / 'reports/full-coverage' / folder).glob('*'):
        if p.is_file() and p.suffix in {'.json', '.log', '.html', '.txt'}:
            name = str(p.relative_to(ROOT)); report_hashes[name] = sha(name)

alias_dir = ROOT / BASE / 'root-closed-report-original-bytes23-v1'
assert not alias_dir.exists(); alias_dir.mkdir()
aliases = []
for name, digest in sorted(report_hashes.items()):
    assert sha(name) == digest
    suffix = Path(name).suffix
    target = alias_dir / (digest + suffix)
    if target.exists(): assert hashlib.sha256(target.read_bytes()).hexdigest() == digest
    else:
        with target.open('xb') as f: f.write((ROOT / name).read_bytes())
    canonical = str(target.relative_to(ROOT)); book_hashes[canonical] = digest
    aliases.append({'original': {'file': name, 'sha256': digest}, 'canonical_original_byte_copy': {'file': canonical, 'sha256': digest}})
alias_name = BASE + '/root-closed-report-original-byte-aliases23-v1.json'
with (ROOT / alias_name).open('x') as f:
    f.write(json.dumps({'status': 'completed_original_report_bytes_copied_exactly_without_rewriting_commands_times_or_status', 'aliases': aliases, 'scope': 'Original actual failures and passes retain their bodies. These are canonical byte aliases for reproducibility; no new mathematical or compiler execution is inferred.'}, indent=2) + '\n')
book_hashes[alias_name] = sha(alias_name)

folders = ('future23-core', 'future23-monitoring', 'future23-scenario-source50', 'future23-monitoring-source51', 'foundations-future23', 'applied-future23', 'modules-future23', 'root-source-batch49', 'root-source-batch50', 'root-source-batch51')
for folder in folders:
    for p in (ROOT / 'book/coverage/checks' / folder).rglob('*'):
        if p.is_file() and '__pycache__' not in p.parts:
            name = str(p.relative_to(ROOT)); book_hashes[name] = sha(name)
for r in (binding['helper'], binding['independent_helper_review'], binding['preparation_helper']): book_hashes[r['file']] = r['sha256']
book_hashes[BINDING] = sha(BINDING)
for p in (ROOT / 'book/coverage/checks').glob('*23*.py'):
    name = str(p.relative_to(ROOT)); book_hashes[name] = sha(name)
for p in (ROOT / 'book/coverage').glob('*23*.py'):
    name = str(p.relative_to(ROOT)); book_hashes[name] = sha(name)
for folder in ('approved-monitoring-correction49-20261011', 'approved-scenario-correction50-20261011', 'approved-monitoring-relative-interior-correction51-20261011'):
    for p in (ROOT / 'reports/full-coverage/source-history' / folder).rglob('*'):
        if p.is_file():
            name = str(p.relative_to(ROOT)); book_hashes[name] = sha(name)

old_selection = read('reports/full-coverage/checkpoint-22-selection.json')
old_plan = read(old_selection['selection_plan'])
additional = {name: {'sha256': digest, 'scope': 'immutable_audit_or_local_source_evidence'} for name, digest in sorted(book_hashes.items())}
assert not (set(book_hashes.values()) & set(old_plan['excluded_full_external_reference_sha256']))
for name, row in additional.items(): assert sha(name) == row['sha256']
dry_names = ('owner23-integration-dry-execution-v1.json', 'owner23-integration-dry-execution-v1.log', 'owner23-integration-guard-dry-run-v1.json')
out = {'status': 'root_authorized_postintegration_owner23_interface_preparation', 'prepared_at_utc': datetime.now(timezone.utc).isoformat(), 'inventory': ref('book/coverage/inventory-after-correction51.json'), 'integration_binding': ref(BINDING), 'actual_integration_execution': ref(execution_name), 'actual_integration_raw_log': ref(execution['log']), 'integration_result': ref(result_name), 'live_offer_destinations': {owner: BASE + '/root23-live-' + owner + '-offer-v1.json' for owner in binding['owners']}, 'interface_manifest_destination': BASE + '/root23-live-owner-interface-manifest-v1.json', 'production_plan_destination': BASE + '/checkpoint23-installed-owner-selection-plan-v1.json', 'selection_helper': ref('book/coverage/prepare_checkpoint23_selection_v1.py'), 'content_retainer': ref('book/coverage/retain_baseline_inputs23.py'), 'live_interface_helper': ref('book/coverage/prepare_checkpoint23_live_owner_interfaces_v2.py'), 'additional_frozen_inputs': additional, 'excluded_full_external_reference_sha256': old_plan['excluded_full_external_reference_sha256'], 'historical_dry_run_evidence_sha256': {'reports/full-coverage/' + n: sha('reports/full-coverage/' + n) for n in dry_names}, 'closed_report_original_byte_aliases': ref(alias_name), 'scope': 'Only post-integration request and immutable original-byte aliases are prepared. Exact completed original mathematical reviews, failed/passing executions, hypotheses and times remain historical. Whole-parent completeness is not inferred.'}
with (ROOT / DEST).open('x') as f: f.write(json.dumps(out, ensure_ascii=False, indent=2) + '\n')
print(json.dumps({'request': ref(DEST), 'additional_inputs': len(additional), 'original_report_aliases': len(aliases)}))
