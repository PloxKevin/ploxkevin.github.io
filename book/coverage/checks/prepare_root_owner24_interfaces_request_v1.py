"""Prepare post-integration inputs and exact aliases of closed report evidence."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, shutil

ROOT = Path(__file__).resolve().parents[3]
BASE = 'book/coverage/checks/future24-core'
DEST = BASE + '/checkpoint24-live-owner-interface-preparation-request-v1.json'
BINDING = 'book/coverage/checks/root-owner24-reviewed-candidate-bindings-v1.json'

def sha(name): return hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
def read(name): return json.loads((ROOT / name).read_text())
def ref(name): return {'file': name, 'sha256': sha(name)}

assert not (ROOT / DEST).exists()
for fixed in ('reports/full-coverage/integration-24.json','reports/full-coverage/root-source52-final-owner-integration24-v1.json',
    'reports/full-coverage/browser-checkpoint-24.json','reports/full-coverage/browser-corrections-24.json',
    'reports/full-coverage/browser-corrections-24.log','reports/full-coverage/browser-corrections-24-inputs.json',
    'reports/full-coverage/browser-source52-24-v1-execution.json','reports/full-coverage/browser-source52-24-v1-execution.log',
    'reports/full-coverage/browser-source52-24-v1-inputs.json','reports/full-coverage/browser-source52-24-v1.json',
    'reports/full-coverage/source52-corrected-paragraphs24-capture-v1.json',
    'reports/full-coverage/prepare-checkpoint23-selection-execution-v2.json','reports/full-coverage/prepare-checkpoint23-selection-execution-v2.log'):
    assert (ROOT/fixed).is_file(),fixed
for name in ['root24-live-'+owner+'-offer-v1.json' for owner in ('core','foundations','applied','modules')]+[
    'root24-live-owner-interface-manifest-v1.json','checkpoint24-installed-owner-selection-plan-v1.json']:
    assert not (ROOT/BASE/name).exists(),name
execution_name = 'reports/full-coverage/owner24-integration-apply-execution-v1.json'
execution = read(execution_name)
assert execution['actual_exit_code'] == 0
result_name = 'reports/full-coverage/owner24-reviewed-candidate-integration-v1.json'
result = read(result_name)
assert result['applied'] is True
binding = read(BINDING)
report_hashes = {}
book_hashes = {}
assert len(result['exact_replacements']) == 5
for replaced in result['exact_replacements']:
    original_name = replaced['original23_byte_copy']
    assert original_name.startswith('reports/full-coverage/owner23-originals-before-owner24-integration-v1/')
    assert sha(original_name) == replaced['before_sha256']
    report_hashes[original_name] = replaced['before_sha256']
for row in binding['owners'].values():
    for r in row['additional_exact_provenance'] + row['original_full_source_semantic_reviews'] + [row['reviewed_final_offer'], row['independent_candidate_mapping_peer'], row['actual_candidate_builder'], row['candidate_ledger']]:
        assert sha(r['file']) == r['sha256']
        (book_hashes if r['file'].startswith('book/coverage/') else report_hashes)[r['file']] = r['sha256']

for prefix in ('owner24-', 'source52-', 'root-core24-', 'static-checkpoint24-', 'browser-checkpoint24-', 'browser-source52-24-', 'source52-corrected-paragraphs24-'):
    for p in (ROOT / 'reports/full-coverage').glob(prefix + '*'):
        if p.is_file() and p.suffix in {'.json', '.log'}:
            name = str(p.relative_to(ROOT)); report_hashes[name] = sha(name)
for name in ('reports/full-coverage/integration-24.json','reports/full-coverage/root-source52-final-owner-integration24-v1.json', 'reports/full-coverage/browser-checkpoint-24.json', 'reports/full-coverage/browser-corrections-24.json', 'reports/full-coverage/browser-corrections-24.log', 'reports/full-coverage/browser-corrections-24-inputs.json'):
    report_hashes[name] = sha(name)
# Browser PNGs are preserved by the explicit post-audit publication stage.
# The allowed extra-input schema freezes textual audit evidence only.
for folder in ('browser-artifacts-24',):
    for p in (ROOT / 'reports/full-coverage' / folder).glob('*'):
        if p.is_file() and p.suffix in {'.json', '.log', '.html', '.txt'}:
            name = str(p.relative_to(ROOT)); report_hashes[name] = sha(name)

for name in ('book/coverage/checks/root_source_batch52_v1.py','book/coverage/checks/root_source_batch52_v2.py','book/coverage/checks/root_source_batch52_v3.py'):
    book_hashes[name]=sha(name)
for name in ('reports/full-coverage/browser-source52-24-v1-execution.json','reports/full-coverage/browser-source52-24-v1-execution.log','reports/full-coverage/browser-source52-24-v1-inputs.json','reports/full-coverage/browser-source52-24-v1.json','reports/full-coverage/source52-corrected-paragraphs24-capture-v1.json'):
    report_hashes[name]=sha(name)

alias_dir = ROOT / BASE / 'root-closed-report-original-bytes24-v1'
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
alias_name = BASE + '/root-closed-report-original-byte-aliases24-v1.json'
with (ROOT / alias_name).open('x') as f:
    f.write(json.dumps({'status': 'completed_original_report_bytes_copied_exactly_without_rewriting_commands_times_or_status', 'aliases': aliases, 'scope': 'Original actual failures and passes retain their bodies. These are canonical byte aliases for reproducibility; no new mathematical or compiler execution is inferred.'}, indent=2) + '\n')
book_hashes[alias_name] = sha(alias_name)

folders = ('future24-core','future24-nn-source52','foundations-future24','applied-future24','modules-future24','root-source-batch52')
for folder in folders:
    for p in (ROOT / 'book/coverage/checks' / folder).rglob('*'):
        if p.is_file() and '__pycache__' not in p.parts:
            name = str(p.relative_to(ROOT)); book_hashes[name] = sha(name)
for r in (binding['helper'], binding['independent_helper_review'], binding['preparation_helper']): book_hashes[r['file']] = r['sha256']
book_hashes[BINDING] = sha(BINDING)
for p in (ROOT / 'book/coverage/checks').glob('*24*.py'):
    name = str(p.relative_to(ROOT)); book_hashes[name] = sha(name)
for p in (ROOT / 'book/coverage').glob('*24*.py'):
    name = str(p.relative_to(ROOT)); book_hashes[name] = sha(name)
for folder in ('approved-neural-offset-precision-scope-correction52-20261011',):
    for p in (ROOT / 'reports/full-coverage/source-history' / folder).rglob('*'):
        if p.is_file():
            name = str(p.relative_to(ROOT)); book_hashes[name] = sha(name)

old_selection = read('reports/full-coverage/checkpoint-23-selection.json')
old_plan = read(old_selection['selection_plan'])
additional = {name: {'sha256': digest, 'scope': 'immutable_audit_or_local_source_evidence'} for name, digest in sorted(book_hashes.items())}
assert not (set(book_hashes.values()) & set(old_plan['excluded_full_external_reference_sha256']))
for name, row in additional.items(): assert sha(name) == row['sha256']
dry_names = ('owner24-integration-dry-execution-v1.json', 'owner24-integration-dry-execution-v1.log', 'owner24-integration-guard-dry-run-v1.json')
prior_history=dict(old_plan['original_failed_selector_v1_provenance'])
prior_history.update(baseline_successful_selector_actual=ref('reports/full-coverage/prepare-checkpoint23-selection-execution-v2.json'),baseline_successful_selector_raw_log=ref('reports/full-coverage/prepare-checkpoint23-selection-execution-v2.log'),baseline_alias_preparation_helper=old_plan['baseline_owner_evidence_alias_plan_preparation_helper'])
out = {'actual_source52_apply':ref('reports/full-coverage/source52-apply-execution-v1.json'),'actual_source52_postwrite':ref('book/coverage/checks/root-source-batch52/postwrite-source-integrity-v1.json'),'prior_checkpoint23_alias_repair_provenance':prior_history,'status': 'root_authorized_postintegration_owner24_interface_preparation', 'prepared_at_utc': datetime.now(timezone.utc).isoformat(), 'inventory': ref('book/coverage/inventory-after-correction52.json'), 'integration_binding': ref(BINDING), 'actual_integration_execution': ref(execution_name), 'actual_integration_raw_log': ref(execution['log']), 'integration_result': ref(result_name), 'live_offer_destinations': {owner: BASE + '/root24-live-' + owner + '-offer-v1.json' for owner in binding['owners']}, 'interface_manifest_destination': BASE + '/root24-live-owner-interface-manifest-v1.json', 'production_plan_destination': BASE + '/checkpoint24-installed-owner-selection-plan-v1.json', 'selection_helper': ref('book/coverage/prepare_checkpoint24_selection_v4.py'), 'content_retainer': ref('book/coverage/retain_baseline_inputs24_v3.py'), 'live_interface_helper': ref('book/coverage/prepare_checkpoint24_live_owner_interfaces_v3.py'), 'additional_frozen_inputs': additional, 'excluded_full_external_reference_sha256': old_plan['excluded_full_external_reference_sha256'], 'historical_dry_run_evidence_sha256': {'reports/full-coverage/' + n: sha('reports/full-coverage/' + n) for n in dry_names}, 'closed_report_original_byte_aliases': ref(alias_name), 'scope': 'Only post-integration request and immutable original-byte aliases are prepared. Exact completed original mathematical reviews, failed/passing executions, hypotheses and times remain historical. Whole-parent completeness is not inferred.'}
with (ROOT / DEST).open('x') as f: f.write(json.dumps(out, ensure_ascii=False, indent=2) + '\n')
print(json.dumps({'request': ref(DEST), 'additional_inputs': len(additional), 'original_report_aliases': len(aliases)}))
