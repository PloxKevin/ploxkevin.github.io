#!/usr/bin/env python3
"""Prepare the current44 selection from genuine execution and exact review evidence."""
from pathlib import Path
from datetime import datetime, timezone
import copy
import hashlib
import json
import re
from lean_names import declarations

ROOT = Path(__file__).resolve().parents[2]

def read(name):
    return json.loads((ROOT / name).read_text())

def sha(name):
    return hashlib.sha256((ROOT / name).read_bytes()).hexdigest()

def exact(mapping):
    for name, expected in mapping.items():
        assert sha(name) == expected, name

baseline_name = 'reports/full-coverage/checkpoint-18-selection.json'
baseline = read(baseline_name)
audit_name = 'reports/full-coverage/lean-checkpoint-18/verification-original.json'
audit = read(audit_name)
assert audit['status'] == 'passed' and len(baseline['proof_files']) == 490
assert {n:r['sha256'] for n,r in baseline['proof_files'].items()} == audit['proof_sha256']
selection = copy.deepcopy(baseline['proof_files'])
origins = {name:['checkpoint18'] for name in selection}
for name, record in selection.items():
    assert sha(name) == record['sha256']
    exact(record['evidence_sha256'])
    record['evidence_sha256'][audit_name] = sha(audit_name)

# Preserve the old immutable snapshot used by the identity guards, alongside
# the actual passing audit. These bytes are provenance, not new executions.
manifest_name = 'reports/full-coverage/checkpoint-18-manifest.json'
manifest = read(manifest_name)
assert manifest['status'] == 'formal_verification_passed_partial_coverage'
assert len(manifest['frozen_inputs_sha256']) == 2431
first = selection[sorted(selection)[0]]
for name, expected in manifest['frozen_inputs_sha256'].items():
    path = manifest['snapshot'] + '/' + name
    assert sha(path) == expected
    first['evidence_sha256'][path] = expected
first['evidence_sha256'].update({manifest_name:sha(manifest_name),baseline_name:sha(baseline_name)})
first['inherited_snapshot_provenance_scope'] = (
    'Byte-exact prior frozen inputs retained for original review bodies and baseline identity guards; '
    'this preservation asserts no fresh compilation.')

def actual_zero(source, digest, evidence):
    """Check an original actual zero record; preserve its original pointers."""
    for name in evidence:
        if not name.endswith('.json'):
            continue
        document = read(name)
        rows = document.get('files', [document]) if isinstance(document, dict) else []
        for row in rows:
            if not isinstance(row, dict) or row.get('exit_code') != 0:
                continue
            if row.get('source', row.get('file')) != source:
                continue
            after = row.get('source_sha256_after', row.get('sha256_after',
                    row.get('source_sha256', row.get('sha256'))))
            before = row.get('source_sha256_before', row.get('sha256_before', after))
            if before != digest or after != digest or not row.get('source_unchanged', True):
                continue
            command = row.get('command', row.get('actual_command', document.get('actual_command')))
            assert command and Path(command[0]).name == 'lake', (source, command)
            assert command[1:3] in [['env','lean'], ['build','SafeLearning.'+Path(source).stem]], (source, command)
            assert row.get('actual_workdir', row.get('workdir', document.get('actual_workdir', document.get('workdir')))), source
            assert row['log_sha256'] in evidence.values(), (source, row['log'])
            return name
    raise AssertionError('No exact original actual-zero source record: ' + source)

def merge(source, record, origin):
    value = record['sha256']
    assert sha(source) == value
    exact(record['evidence_sha256'])
    raw = actual_zero(source, value, record['evidence_sha256'])
    if source in selection:
        assert selection[source]['sha256'] == value
        selection[source]['evidence_sha256'].update(record['evidence_sha256'])
    else:
        selection[source] = copy.deepcopy(record)
    selection[source]['original_actual_zero_record'] = raw
    origins.setdefault(source, []).append(origin)

offers = {
    'foundations':'book/coverage/foundations-audit19-source44-additions-v1.json',
    'applied':'book/coverage/applied-audit19-source44-additions-v1.json',
    'modules':'book/coverage/checks/modules-audit19-source44-additions-v1.json',
    'core':'book/coverage/core-audit19-source44-additions-v1.json',
}
foundation = read(offers['foundations'])
assert sha(foundation['mapped_ledger']) == foundation['mapped_ledger_sha256']
exact(foundation['current_owner_builder_sha256'])
exact(foundation['exact_source_reviews_sha256'])
exact(foundation['independent_source33_and44_binding_and_mapping_confirmations_sha256'])
for source, record in foundation['proof_files'].items():
    merge(source, record, 'foundations44')

applied = read(offers['applied'])
assert sha(applied['mapped_ledger']) == applied['mapped_ledger_sha256']
assert sha('book/coverage/applied-promotions.json') == applied['mapped_promotions_sha256']
exact(applied['independent_source_reviews'])
for row in applied['modules']:
    source = row['source']
    assert row['exit_code'] == 0 and row['sha256_before'] == row['sha256_after']
    provenance = row.get('original_execution_provenance', {})
    raw = provenance.get('canonical_byte_identical_original_record', row.get('standalone_evidence'))
    raw_digest = provenance.get('canonical_original_record_sha256', row.get('standalone_evidence_sha256'))
    merge(source, dict(sha256=row['sha256_after'], evidence_sha256={raw:raw_digest, row['log']:row['log_sha256']},
          evidence_scope='Original actual source-matched compiler and exact raw log bytes.'), 'applied44')

module = read(offers['modules'])
assert sha(module['module_ledger']) == module['module_ledger_sha256']
for field in ['module_builder','binding_validator','review_mapping_helper']:
    assert sha(module[field]) == module[field+'_sha256']
exact(module['source_reviews'])
binding = module['current_identity_binding_validation']
assert sha(binding['file']) == binding['sha256']
assert read(binding['file'])['status'] == 'exact_current44_unchanged_literal_fresh_review_and_actual_execution_bindings_passed'
for source, record in module['proof_files'].items():
    merge(source, record, 'modules44')

core = read(offers['core'])
assert sha(core['mapped_ledger']) == core['mapped_ledger_sha256']
exact(core['builder_sha256'])
exact(core['review_sha256'])
exact(core['source_correction_provenance'])
for source, record in core['proof_files'].items():
    merge(source, record, 'core44')

inventory_name = 'book/coverage/inventory-after-correction44.json'
inventory_hash = sha(inventory_name)
assert sha('book/coverage/inventory.json') == inventory_hash
for offer in [foundation,module,core]:
    assert offer['current_inventory_sha256'] == inventory_hash
    exact(offer['source_sha256'])
assert applied['inventory_sha256'] == inventory_hash
exact(applied['source_sha256'])
global_name = 'book/coverage/checks/root-source44-final-owner-integration19-v2.json'
global_audit = read(global_name)
assert global_audit['integrity_status'] == 'passed' and not global_audit['errors']
assert global_audit['inventory_sha256'] == inventory_hash
for domain in global_audit['domains']:
    assert sha('book/coverage/'+domain['domain']+'.json') == domain['ledger_sha256']

all_names = {d['name'] for source in selection for d in declarations((ROOT/source).read_text())}
for domain in offers:
    ledger = read('book/coverage/'+domain+'.json')
    for claim in ledger['material_claims'] + [c for e in ledger['exercises'] for c in e['claims']]:
        assert not set(claim['lean_declarations']) - all_names, (domain,claim['id'])
for source in selection:
    for line in re.findall(r'^import[^\n]*', (ROOT/source).read_text(), re.M):
        for dependency in line.split()[1:]:
            if dependency.startswith('SafeLearning.'):
                path = 'verification/lean/'+dependency.replace('.','/')+'.lean'
                assert path in selection, (source,path)

extras = {}
dependency_name = module['canonical_dependency_manifest']['file']
assert sha(dependency_name) == module['canonical_dependency_manifest']['sha256']
dependency = read(dependency_name)
external_reference_hashes = {row['sha256'] for row in dependency['artifacts'] if row['type'] == 'external_primary_paper_reference'}
for row in dependency['artifacts']:
    if row['type'] == 'external_primary_paper_reference':
        assert not row['required_for_execution_or_immutable_provenance_freeze']
        continue
    if row['required_for_execution_or_immutable_provenance_freeze'] and Path(row['path']).suffix in {'.txt','.cjs'}:
        assert sha(row['path']) == row['sha256']
        extras[row['path']] = dict(sha256=row['sha256'],scope='immutable_audit_or_local_source_evidence')
assert len(extras) == 49
for path in (ROOT/'reports/full-coverage/source-history').rglob('*'):
    if path.is_file() and path.suffix in {'.py','.json','.md','.log','.html','.lean','.js','.cjs','.txt'}:
        digest = sha(str(path.relative_to(ROOT)))
        if digest not in external_reference_hashes:
            extras[str(path.relative_to(ROOT))] = dict(sha256=digest,scope='immutable_audit_or_local_source_evidence')

result = dict(status='explicit_current44_source_matched_selection_requires_fresh_aggregate_audit',
    created_at_utc=datetime.now(timezone.utc).isoformat(), baseline_selection=baseline_name,
    baseline_selection_sha256=sha(baseline_name), actual_passing_baseline_audit=audit_name,
    actual_passing_baseline_audit_sha256=sha(audit_name), current_inventory=inventory_name,
    current_inventory_sha256=inventory_hash, offers_sha256={n:sha(n) for n in offers.values()},
    global_integrity=global_name,global_integrity_sha256=sha(global_name),
    proof_files=dict(sorted(selection.items())),proof_file_count=len(selection),
    new_file_count=len(set(selection)-set(baseline['proof_files'])),origins=origins,
    extra_frozen_inputs=extras,
    independent_current44_confirmations_sha256={name:sha(name) for name in [
        'book/coverage/checks/foundations-source44-final-mapping-independent-modules-confirmation-v1.json',
        'book/coverage/checks/applied-source44-reviewed19-integration-independent-foundations-confirmation-v1.json',
        'book/coverage/checks/root-future19-peer-confirmations/modules-final44-mappings-offer-independent-applied-confirmation19-v1.json',
        'book/coverage/checks/modules-browser-layout-settle19-independent-review44-v1.json',
        'book/coverage/checks/modules-freezer-reader-qa19-independent-review44-v1.json']},
    deliberate_baseline_source_revisions={},coverage_complete=False,
    limits=['Original actual compiler/hash/log evidence and current literal reviews are bound separately.',
            'The full original snapshot is retained as provenance; preservation creates no new execution.',
            'Only located excerpts and replay harnesses are required; full external papers remain external references.',
            'Future20 drafts are not mapped or selected. Aggregate build, kernel replay and all-theorem axiom audit must still pass.'])
destination = ROOT/'reports/full-coverage/checkpoint-19-selection.json'
assert not destination.exists()
destination.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'proofs':len(selection),'new':result['new_file_count'],'explicit_extra_inputs':len(extras),'selection_sha256':sha(str(destination.relative_to(ROOT)))}))
