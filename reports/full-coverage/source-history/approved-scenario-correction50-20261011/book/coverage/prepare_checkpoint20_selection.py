"""Select exact current47 mappings and genuine compiler evidence for a fresh audit."""
from pathlib import Path
from datetime import datetime, timezone
import copy
import hashlib
import json
import re
from lean_names import declarations

ROOT = Path(__file__).resolve().parents[2]
def read(name):
    return json.loads((ROOT/name).read_text())
def sha(name):
    return hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
def exact(mapping):
    for name, digest in mapping.items():
        assert sha(name) == digest, name
def actual_zero(source, digest, evidence):
    exact(evidence)
    for name in evidence:
        if not name.endswith('.json'):
            continue
        record = read(name)
        if not isinstance(record, dict) or record.get('source') != source or record.get('exit_code') != 0:
            continue
        assert record['source_sha256_before'] == record['source_sha256_after'] == digest
        assert record['source_unchanged'] is True
        command = record.get('command', record.get('actual_command'))
        assert command == ['lake', 'env', 'lean', str(Path(source).relative_to('verification/lean'))]
        assert Path(record['actual_workdir']).resolve() == (ROOT/'verification/lean').resolve()
        assert any(name.endswith('.log') and expected == record['log_sha256'] for name, expected in evidence.items())
        return name
    raise AssertionError('No exact actual standalone success: ' + source)

baseline_name = 'reports/full-coverage/checkpoint-19-selection.json'
audit_name = 'reports/full-coverage/lean-checkpoint-19/verification-original.json'
manifest_name = 'reports/full-coverage/checkpoint-19-manifest.json'
baseline, audit, manifest = read(baseline_name), read(audit_name), read(manifest_name)
assert audit['status'] == 'passed' and len(baseline['proof_files']) == 1055
assert audit['proof_sha256'] == {name: record['sha256'] for name, record in baseline['proof_files'].items()}
assert manifest['status'] == 'formal_verification_passed_partial_coverage' and len(manifest['frozen_inputs_sha256']) == 14101
selection = copy.deepcopy(baseline['proof_files'])
for name, record in selection.items():
    assert sha(name) == record['sha256']
    exact(record['evidence_sha256'])
    record['evidence_sha256'][audit_name] = sha(audit_name)
first = selection[sorted(selection)[0]]
for name, digest in manifest['frozen_inputs_sha256'].items():
    historical = manifest['snapshot'] + '/' + name
    assert sha(historical) == digest
    first['evidence_sha256'][historical] = digest
first['evidence_sha256'].update({baseline_name: sha(baseline_name), manifest_name: sha(manifest_name)})
for path in (ROOT/'reports/full-coverage/lean-checkpoint-19').rglob('*'):
    if path.is_file():
        name = str(path.relative_to(ROOT))
        first['evidence_sha256'][name] = sha(name)
first['inherited_snapshot_provenance_scope'] = 'Exact original frozen19 inputs and actual audit outputs retained as historical provenance, without asserting new executions.'

offers = {
    'foundations': 'book/coverage/foundations-audit20-source47-additions-v1.json',
    'applied': 'book/coverage/applied-audit20-source47-additions-v1.json',
    'modules': 'book/coverage/checks/modules-audit20-source47-additions-v1.json',
    'core': 'book/coverage/core-audit20-source47-additions-v1.json',
}
documents = {owner: read(name) for owner, name in offers.items()}
inventory_name = 'book/coverage/inventory-after-correction47.json'
inventory_hash = sha(inventory_name)
assert sha('book/coverage/inventory.json') == inventory_hash == 'ab2b27355004f545180b00ca1c1d5243aeb88683100d6ca747e3054987bbf0c2'
for owner, offer in documents.items():
    ledger_name = 'book/coverage/' + owner + '.json'
    pointer = offer.get('mapped_ledger', offer.get('module_ledger'))
    assert pointer == ledger_name
    expected = offer.get('mapped_ledger_sha256', offer.get('module_ledger_sha256'))
    assert sha(ledger_name) == expected
    assert offer.get('current_inventory_sha256', offer.get('inventory_sha256')) == inventory_hash
    exact(offer['source_sha256'])
    for field in ('builder_sha256', 'current_owner_builder_sha256', 'review_sha256', 'exact_source_reviews_sha256', 'source_reviews', 'source_correction_provenance', 'independent_source_reviews'):
        values = offer.get(field)
        if isinstance(values, dict) and all(isinstance(v, str) for v in values.values()):
            exact(values)
for field in ('module_builder', 'binding_validator'):
    assert sha(documents['modules'][field]) == documents['modules'][field+'_sha256']
for field in ('current_identity_binding_validation', 'actual_builder', 'review_mapping', 'canonical_dependency_manifest'):
    row = documents['modules'][field]
    assert sha(row['file']) == row['sha256']
assert read(documents['modules']['actual_builder']['file'])['actual_exit_code'] == 0
assert read(documents['core']['actual_builder'])['actual_exit_code'] == 0
assert sha(documents['core']['actual_builder']) == documents['core']['actual_builder_sha256']
assert sha(documents['applied']['source47_builder']) == documents['applied']['source47_builder_sha256']
assert read(documents['applied']['source47_actual_builder_record'])['actual_exit_code'] == 0
assert sha('book/coverage/applied-promotions.json') == documents['applied']['mapped_promotions_sha256']
assert not documents['applied']['new_proof_sources_for_checkpoint20']
new_sources = set()
for owner in ('foundations', 'modules', 'core'):
    for source, record in documents[owner].get('proof_files', {}).items():
        digest = record['sha256']
        assert sha(source) == digest
        evidence = record['evidence_sha256']
        exact(evidence)
        if source in selection:
            assert selection[source]['sha256'] == digest
            selection[source]['evidence_sha256'].update(evidence)
        else:
            original = actual_zero(source, digest, evidence)
            selected = copy.deepcopy(record)
            selected['original_actual_zero_record'] = original
            selection[source] = selected
            new_sources.add(source)
assert len(new_sources) == 13 and len(selection) == 1068
exact(documents['modules']['required_external_import_dependencies'])
assert set(documents['modules']['required_external_import_dependencies']) <= set(selection)
global_name = 'book/coverage/checks/root-source47-final-owner-integration20-v3.json'
global_audit = read(global_name)
assert global_audit['integrity_status'] == 'passed' and not global_audit['errors'] and global_audit['inventory_sha256'] == inventory_hash
for domain in global_audit['domains']:
    assert sha('book/coverage/' + domain['domain'] + '.json') == domain['ledger_sha256']
names = {d['name'] for source in selection for d in declarations((ROOT/source).read_text())}
for owner in offers:
    ledger = read('book/coverage/' + owner + '.json')
    for claim in ledger['material_claims'] + [c for e in ledger['exercises'] for c in e['claims']]:
        assert set(claim['lean_declarations']) <= names, (owner, claim['id'])
for source in selection:
    for line in re.findall(r'^import[^\n]*', (ROOT/source).read_text(), re.M):
        for dependency in line.split()[1:]:
            if dependency.startswith('SafeLearning.'):
                assert 'verification/lean/' + dependency.replace('.', '/') + '.lean' in selection, (source, dependency)
extras = copy.deepcopy(baseline['extra_frozen_inputs'])
for name, record in extras.items():
    assert sha(name) == record['sha256']
old_dependency = read('book/coverage/checks/modules-source44-canonical-dependency-manifest19-v1.json')
external_hashes = {r['sha256'] for r in old_dependency['artifacts'] if r['type'] == 'external_primary_paper_reference'}
dependency = read(documents['modules']['canonical_dependency_manifest']['file'])
external_hashes.update(row['sha256'] for row in dependency['primary_references'])
for name, row in dependency['artifacts'].items():
    assert sha(name) == row['sha256']
    if row['required_for_audit'] and Path(name).suffix in {'.txt', '.cjs'}:
        extras[name] = dict(sha256=row['sha256'], scope='immutable_audit_or_local_source_evidence')
for path in (ROOT/'reports/full-coverage/source-history').rglob('*'):
    if path.is_file() and path.suffix in {'.py', '.json', '.md', '.log', '.html', '.lean', '.js', '.cjs', '.txt'}:
        name = str(path.relative_to(ROOT))
        digest = sha(name)
        if digest not in external_hashes:
            extras[name] = dict(sha256=digest, scope='immutable_audit_or_local_source_evidence')
result = dict(status='explicit_current47_source_matched_selection_requires_fresh_aggregate_audit', created_at_utc=datetime.now(timezone.utc).isoformat(), baseline_selection=baseline_name, baseline_selection_sha256=sha(baseline_name), actual_passing_baseline_audit=audit_name, actual_passing_baseline_audit_sha256=sha(audit_name), current_inventory=inventory_name, current_inventory_sha256=inventory_hash, offers_sha256={name: sha(name) for name in offers.values()}, global_integrity=global_name, global_integrity_sha256=sha(global_name), proof_files=dict(sorted(selection.items())), proof_file_count=len(selection), new_file_count=len(new_sources), extra_frozen_inputs=extras, deliberate_baseline_source_revisions={}, coverage_complete=False, limits=['All1055 baseline sources and original evidence stay exact. Thirteen actual source-matched additions require a fresh frozen aggregate build, kernel and all-theorem axiom audit.', 'Unselected future21 work adds no verified coverage. Exact previous frozen inputs remain provenance, not new executions.', 'Located primary passages are preserved; full external papers remain separately attributed references.'])
destination = ROOT/'reports/full-coverage/checkpoint-20-selection.json'
assert not destination.exists()
destination.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(dict(proofs=len(selection), new=len(new_sources), selection_sha256=sha(str(destination.relative_to(ROOT))), extra_inputs=len(extras))))
