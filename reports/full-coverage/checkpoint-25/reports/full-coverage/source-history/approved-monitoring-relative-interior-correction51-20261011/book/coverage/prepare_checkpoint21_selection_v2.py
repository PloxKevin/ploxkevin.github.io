"""Select exact current48 mappings and genuine compiler evidence for a fresh audit."""
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
        assert record.get('source_unchanged', True) is True  # Missing flag is derived only after the exact before/after hashes above.
        command = record.get('command', record.get('actual_command'))
        assert command == ['lake', 'env', 'lean', str(Path(source).relative_to('verification/lean'))]
        assert Path(record['actual_workdir']).resolve() == (ROOT/'verification/lean').resolve()
        assert any(name.endswith('.log') and expected == record['log_sha256'] for name, expected in evidence.items())
        return name
    raise AssertionError('No exact actual standalone success: ' + source)

baseline_name = 'reports/full-coverage/checkpoint-20-selection.json'
audit_name = 'reports/full-coverage/lean-checkpoint-20/verification-original.json'
manifest_name = 'reports/full-coverage/checkpoint-20-manifest.json'
baseline, audit, manifest = read(baseline_name), read(audit_name), read(manifest_name)
assert audit['status'] == 'passed' and len(baseline['proof_files']) == 1068
assert audit['proof_sha256'] == {name: record['sha256'] for name, record in baseline['proof_files'].items()}
assert manifest['status'] == 'formal_verification_passed_partial_coverage' and len(manifest['frozen_inputs_sha256']) == 30207
selection = copy.deepcopy(baseline['proof_files'])
for name, record in selection.items():
    assert sha(name) == record['sha256']
    exact(record['evidence_sha256'])
    record['evidence_sha256'][audit_name] = sha(audit_name)
first = selection[sorted(selection)[0]]
first['evidence_sha256'].update({baseline_name: sha(baseline_name), manifest_name: sha(manifest_name), 'book/coverage/checks/future21-core/modules-retain-baseline-inputs21-independent-helper-confirmation-v1.json':sha('book/coverage/checks/future21-core/modules-retain-baseline-inputs21-independent-helper-confirmation-v1.json')})
for path in (ROOT/'reports/full-coverage/lean-checkpoint-20').rglob('*'):
    if path.is_file():
        name = str(path.relative_to(ROOT))
        first['evidence_sha256'][name] = sha(name)
first['inherited_snapshot_provenance_scope'] = 'Every frozen20 input is retained by the separate exact original path/content binding map; identical byte sequences share immutable selected inputs. Original actual executions remain historical.'

offers = {
    'foundations': 'book/coverage/foundations-audit21-source48-additions-v1.json',
    'applied': 'book/coverage/applied-audit21-source48-additions-v1.json',
    'modules': 'book/coverage/checks/modules-audit21-source48-additions-v1.json',
    'core': 'book/coverage/core-audit21-source48-additions-v1.json',
}
documents = {owner: read(name) for owner, name in offers.items()}
inventory_name = 'book/coverage/inventory-after-correction48.json'
inventory_hash = sha(inventory_name)
assert sha('book/coverage/inventory.json') == inventory_hash == '2daa285ff1cbc2ad0db045e00e1271b6cb58ce809f5a8328120286748250c108'
for owner, offer in documents.items():
    ledger_name = 'book/coverage/' + owner + '.json'
    pointer = offer.get('mapped_ledger', offer.get('module_ledger'))
    assert pointer == ledger_name
    expected = offer.get('mapped_ledger_sha256', offer.get('module_ledger_sha256'))
    assert sha(ledger_name) == expected
    assert offer.get('current_inventory_sha256', offer.get('inventory_sha256')) == inventory_hash
    exact(offer['source_sha256'])
    for field in ('builder_sha256', 'current_owner_builder_sha256', 'review_sha256', 'exact_source_reviews_sha256', 'source_reviews', 'source_correction_provenance', 'independent_source_reviews', 'current21_helpers_sha256'):
        values = offer.get(field)
        if isinstance(values, dict) and all(isinstance(v, str) for v in values.values()):
            exact(values)
foundation = documents['foundations']
for field in ('current_owner_builder','actual_builder_record','loader_integration','cross_owner_lipsdp_readiness_manifest','source48_unchanged_identity_manifest','material21_exact_interface_binding','independent_identity_interface_and_seeded_adapter_confirmation'):
    assert sha(foundation[field]) == foundation[field+'_sha256']
foundation_actual = read(foundation['actual_builder_record'])
assert foundation_actual.get('actual_exit_code',foundation_actual.get('exit_code')) == 0
assert set(foundation['new_proof_sources_for_checkpoint21']) == set(foundation['proof_files'])
assert len(foundation['proof_files']) == 7 and foundation['new_theorem_or_lemma_count'] == 55
for field in ('module_builder', 'binding_validator'):
    assert sha(documents['modules'][field]) == documents['modules'][field+'_sha256']
for field in ('current_identity_binding_validation', 'actual_builder', 'review_mapping', 'canonical_dependency_manifest'):
    row = documents['modules'][field]
    assert sha(row['file']) == row['sha256']
assert read(documents['modules']['actual_builder']['file'])['actual_exit_code'] == 0
assert read(documents['core']['actual_builder'])['actual_exit_code'] == 0
assert sha(documents['core']['actual_builder']) == documents['core']['actual_builder_sha256']
assert sha(documents['applied']['source48_builder']) == documents['applied']['source48_builder_sha256']
applied_actual = read(documents['applied']['source48_actual_builder_record'])
assert applied_actual.get('actual_exit_code',applied_actual.get('exit_code')) == 0
assert sha(documents['applied']['source48_actual_builder_record']) == documents['applied']['source48_actual_builder_record_sha256']
assert sha('book/coverage/applied-promotions.json') == documents['applied']['mapped_promotions_sha256']
assert not documents['applied']['new_proof_sources_for_checkpoint20']
assert set(documents['applied']['new_proof_sources_for_checkpoint21']) == set(documents['applied']['proof_files'])
peers = {
 'foundations': ('book/coverage/checks/foundations-future21/foundations-source48-final-mapping-independent-modules-confirmation21-v3.json', 'c60ef410d8a4d02a796ffaf6142a2887a12741bc53f9933b897bddb950e29254'),
 'modules': ('book/coverage/checks/future21-core/modules21-final-mapping-independent-applied-confirmation-v1.json', '72cc68efbcf37b7daf10c34984cb1de292666b5c6cdaad3db59ae0e9ab8f27bc'),
 'applied': ('book/coverage/checks/applied-future21/applied-source48-final-mapping-independent-foundations-confirmation21-v1.json', '5c58cfcbc055c36864e4d8b1855bbf649044a1cc91c321319e2de4be3b71b645'),
 'core': ('book/coverage/checks/future21-core/modules-core-source48-final-mapping-independent-confirmation21-v1.json', '9f1df437a2c357785c009504540669e2d434e020a63365d2b4d5438ca9e2860c'),
}
for owner, (name, digest) in peers.items():
 assert sha(name)==digest
 first['evidence_sha256'][name]=digest
new_sources = set()
for owner in offers:
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
assert new_sources and len(selection) == 1068 + len(new_sources)
exact(documents['modules']['required_external_import_dependencies'])
assert set(documents['modules']['required_external_import_dependencies']) <= set(selection)
global_name = 'book/coverage/checks/root-source48-final-owner-integration21-v1.json'
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
from retain_baseline_inputs21 import retain
provenance = retain(ROOT, baseline_name, manifest_name, selection, extras, 'book/coverage/checks/frozen20-input-content-bindings21-v1.json')
result = dict(previous_frozen_input_content_binding=provenance, status='explicit_current48_source_matched_selection_requires_fresh_aggregate_audit', created_at_utc=datetime.now(timezone.utc).isoformat(), baseline_selection=baseline_name, baseline_selection_sha256=sha(baseline_name), actual_passing_baseline_audit=audit_name, actual_passing_baseline_audit_sha256=sha(audit_name), current_inventory=inventory_name, current_inventory_sha256=inventory_hash, offers_sha256={name: sha(name) for name in offers.values()}, global_integrity=global_name, global_integrity_sha256=sha(global_name), proof_files=dict(sorted(selection.items())), proof_file_count=len(selection), new_file_count=len(new_sources), extra_frozen_inputs=extras, deliberate_baseline_source_revisions={}, coverage_complete=False, limits=['All1068 baseline sources and original evidence stay exact. The actual source-matched additions require a fresh frozen aggregate build, kernel and all-theorem axiom audit.', 'Unselected future22 work adds no verified coverage. Exact previous frozen inputs remain provenance, not new executions.', 'Located primary passages are preserved; full external papers remain separately attributed references.'])
destination = ROOT/'reports/full-coverage/checkpoint-21-selection.json'
assert not destination.exists()
destination.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(dict(proofs=len(selection), new=len(new_sources), selection_sha256=sha(str(destination.relative_to(ROOT))), extra_inputs=len(extras))))
