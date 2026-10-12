#!/usr/bin/env python3
"""Prepare explicit checkpoint12 inputs; this does not execute its Lean audit."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[2]


def read(name):
    return json.loads((ROOT / name).read_text())


def sha(name):
    return hashlib.sha256((ROOT / name).read_bytes()).hexdigest()


baseline = 'reports/full-coverage/checkpoint-11-selection.json'
report = 'reports/full-coverage/lean-checkpoint-11/verification-original.json'
assert read(report)['status'] == 'passed'
old = read(baseline)['proof_files']
selection = {}
changed = {}
for source, record in old.items():
    current = sha(source)
    if current != record['sha256']:
        assert source == 'verification/lean/SafeLearning/CompleteFoundationsConstrainedModels.lean'
        changed[source] = {'old_sha256': record['sha256'], 'new_sha256': current}
        continue
    selection[source] = dict(
        sha256=current, evidence_sha256={report: sha(report)},
        evidence_scope='Actual passing checkpoint11 aggregate build/kernel/axiom audit for identical source; a fresh aggregate audit is required.')
    if 'deliberate_source_revision' in record:
        selection[source]['deliberate_source_revision'] = record['deliberate_source_revision']


def add(source, metadata, companion=None):
    document = read(metadata)
    record = document
    if 'files' in document:
        assert document['status'] == 'passed' and document['all_sources_still_match']
        record = next(r for r in document['files'] if r['file'] == source)
        assert record['source_unchanged']
    assert record['exit_code'] == 0, metadata
    value = sha(source)
    before = record.get('source_sha256_before', record.get('sha256_before',
             record.get('source_sha256', record.get('sha256'))))
    after = record.get('source_sha256_after', record.get('sha256_after',
            record.get('source_sha256', record.get('sha256'))))
    assert before == after == value, (source, before, after, value)
    assert record.get('source', record.get('file')) == source
    log = record['log']
    assert sha(log) == record['log_sha256']
    command = record.get('command') or (companion or {}).get('actual_command')
    assert command == ['lake', 'env', 'lean', source.removeprefix('verification/lean/')]
    if companion:
        assert companion['actual_exit_code'] == 0
        assert companion['compiler_manifest_sha256'] == sha(metadata)
        assert companion['raw_log_sha256'] == sha(log)
        assert companion['sha256'] == value
    selection[source] = dict(
        sha256=value, evidence_sha256={metadata: sha(metadata), log: sha(log)},
        evidence_scope='Actual source-matched standalone compiler exit0, unchanged source and exact raw log; fresh aggregate/kernel/axiom verification remains required.')


foundations = read('book/coverage/foundations-audit12-additions.json')
for source, record in foundations['proof_files'].items():
    metadata = next(p for p in record['evidence_sha256'] if p.endswith('.json'))
    for name, expected in record['evidence_sha256'].items():
        assert sha(name) == expected
    add(source, metadata)

modules = read('book/coverage/checks/modules-audit12-additions.json')
for source, record in modules['proof_files'].items():
    add(source, record['compiler_manifest'], record)

applied = read('book/coverage/applied-audit12-additions.json')
for record in applied['modules']:
    assert sha(record['standalone_evidence']) == record['standalone_evidence_sha256']
    add(record['source'], record['standalone_evidence'])

for label in ['PolicyTrustStep', 'PolicyDiskStep', 'AlternatingCMDP',
              'AlternatingCMDPReturns', 'AlternatingCMDPGeometry', 'StudyGuideModels']:
    add('verification/lean/SafeLearning/Complete' + label + '.lean',
        'book/coverage/checks/Complete' + label + '-standalone.json')

revision = foundations['authorized_existing_proof_revision']
assert revision['source'] in changed
assert revision['old_sha256'] == changed[revision['source']]['old_sha256']
assert revision['new_sha256'] == changed[revision['source']]['new_sha256']
for name, expected in [(revision['preserved_history_provenance'], revision['preserved_history_provenance_sha256']),
                       (revision['revision_review'], revision['revision_review_sha256']),
                       (revision['independent_confirmation'], revision['independent_confirmation_sha256'])]:
    assert sha(name) == expected
    selection[revision['source']]['evidence_sha256'][name] = expected
selection[revision['source']]['deliberate_source_revision'] = {
    'proof': revision['source'], 'historical_source_sha256': revision['old_sha256'],
    'current_source_sha256': revision['new_sha256'],
    'preserved_history': revision['preserved_history_provenance'],
    'preserved_history_sha256': revision['preserved_history_provenance_sha256'],
    'new_review': revision['revision_review'], 'new_review_sha256': revision['revision_review_sha256'],
    'independent_confirmation': revision['independent_confirmation'],
    'independent_confirmation_sha256': revision['independent_confirmation_sha256'],
    'exact_change': revision['exact_change']}

for source in selection:
    for dependency in re.findall(r'^import\s+(SafeLearning\.\S+)',
                                 (ROOT / source).read_text(), re.M):
        assert 'verification/lean/' + dependency.replace('.', '/') + '.lean' in selection

result = dict(
    status='explicit_source_matched_stable_requires_fresh_aggregate_audit',
    created_at_utc=datetime.now(timezone.utc).isoformat(), basis=report,
    baseline_selection=baseline, baseline_selection_sha256=sha(baseline),
    proof_files=dict(sorted(selection.items())), proof_file_count=len(selection),
    new_file_count=len(set(selection) - set(old)), deliberate_baseline_source_revisions=changed,
    coverage_complete=False,
    limits=['This selection prepares audited inputs and records actual standalone/prior evidence; it does not claim the new aggregate audit has run.'])
destination = ROOT / 'reports/full-coverage/checkpoint-12-selection.json'
destination.write_text(json.dumps(result, indent=2) + '\n')
print(f'Prepared {len(selection)} source-matched files; {result["new_file_count"]} new and '
      f'{len(changed)} explicit baseline revision. Actual evidence and import closure checked.')
