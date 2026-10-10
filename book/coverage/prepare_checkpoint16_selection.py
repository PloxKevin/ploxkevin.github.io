#!/usr/bin/env python3
"""Prepare exact checkpoint16 inputs, without claiming a fresh Lean audit."""
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


baseline = 'reports/full-coverage/checkpoint-15-selection.json'
report = 'reports/full-coverage/lean-checkpoint-15/verification-original.json'
assert read(report)['status'] == 'passed'
old = read(baseline)['proof_files']
modules = read('book/coverage/checks/modules-audit16-additions.json')
revisions = modules.get('deliberate_baseline_source_revisions', {})
assert set(revisions) == {'verification/lean/SafeLearning/CompleteModulesLinearProgram.lean'}
for source, revision in revisions.items():
    assert revision['historical_source_sha256'] == old[source]['sha256']
    assert revision['current_source_sha256'] == sha(source)
    assert sha(revision['preserved_history']) == revision['preserved_history_sha256']
    history = read(revision['preserved_history'])
    for preserved in history['preserved_files']:
        assert sha(preserved['preserved']) == preserved['sha256']
    historical = next(p for p in history['preserved_files'] if p['original'] == source)
    historical_bytes = (ROOT/historical['preserved']).read_bytes()
    assert historical_bytes == (ROOT/'reports/full-coverage/checkpoint-15'/source).read_bytes()
    lines = historical_bytes.splitlines(keepends=True)
    changes = []
    for index in (37, 53):
        assert lines[index].endswith(b' \n')
        lines[index] = lines[index][:-2] + b'\n'
        changes.append(index + 1)
    assert b''.join(lines) == (ROOT/source).read_bytes(), ('Unexpected mathematical change', source)
    for field in ('new_review','independent_confirmation','compiler_manifest','named_build'):
        assert sha(revision[field]) == revision[field+'_sha256']
    confirmation = read(revision['independent_confirmation'])
    assert confirmation['status'] == 'independent_exact_source_review_identity_rebase_confirmation_passed'
    assert confirmation['historical_source_sha256'] == old[source]['sha256']
    assert confirmation['current_source_sha256'] == sha(source)
    assert confirmation['only_two_trailing_spaces_removed']
    assert confirmation['every_other_source_byte_and_mathematical_token_identical']
    assert confirmation['all_eight_permanent_history_artifacts_exact']
    assert confirmation['semantic_review_body_original_time_reviewer_decisions_hypotheses_gaps_limits_exactly_preserved']
    assert confirmation['fresh_current_actual_standalone_exit_code'] == 0
    assert confirmation['fresh_named_build_actual_exit_code'] == 0
    named = read(revision['named_build'])
    assert named['actual_exit_code'] == 0 and named['source_unchanged']
    assert named['source_sha256_before'] == named['source_sha256_after'] == sha(source)
    assert sha(named['raw_log']) == named['raw_log_sha256']
# The earlier339 proof sources have no revision exception in this checkpoint.
for source, record in read('reports/full-coverage/checkpoint-14-selection.json')['proof_files'].items():
    assert sha(source) == record['sha256'], ('Earlier immutable source changed', source)
selection = {}
for source, record in old.items():
    if source in revisions:
        continue
    assert sha(source) == record['sha256'], ('Baseline source changed', source)
    selection[source] = dict(
        sha256=record['sha256'], evidence_sha256={report: sha(report)},
        evidence_scope='Actual passing checkpoint15 aggregate/kernel/axiom audit for identical source; a fresh aggregate audit is required.')
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
    command = record.get('command') or document.get('actual_command') or (companion or {}).get('actual_command')
    assert command == ['lake', 'env', 'lean', source.removeprefix('verification/lean/')]
    if companion:
        assert companion['actual_exit_code'] == 0
        assert companion['compiler_manifest_sha256'] == sha(metadata)
        assert companion['raw_log_sha256'] == sha(log)
        assert companion['sha256'] == value
    assert source not in selection, ('Duplicate selection', source)
    selection[source] = dict(
        sha256=value, evidence_sha256={metadata: sha(metadata), log: sha(log)},
        evidence_scope='Actual source-matched standalone compiler exit0 and exact raw log; fresh aggregate/kernel/axiom verification remains required.')


foundations = read('book/coverage/foundations-audit16-additions.json')
assert sha(foundations['mapped_ledger']) == foundations['mapped_ledger_sha256']
assert sha(foundations['current_inventory']) == foundations['current_inventory_sha256']
assert sha(foundations['current_consolidated_manifest']) == foundations['current_consolidated_manifest_sha256']
for name, expected in foundations['current_owner_builder_sha256'].items():
    assert sha(name) == expected
for name, expected in foundations['exact_source_reviews_sha256'].items():
    assert sha(name) == expected
for name, expected in foundations['source_sha256'].items():
    assert sha(name) == expected
for source, record in foundations['proof_files'].items():
    for name, expected in record['evidence_sha256'].items():
        assert sha(name) == expected
    add(source, next(p for p in record['evidence_sha256'] if p.endswith('.json')))

assert sha(modules['module_ledger']) == modules['module_ledger_sha256']
assert sha(modules['module_builder']) == modules['module_builder_sha256']
for name, expected in modules['source_reviews'].items():
    assert sha(name) == expected
for field in ['empirical_execution_evidence', 'source_correction_provenance']:
    for name, expected in modules.get(field, {}).items():
        assert sha(name) == expected
for name, expected in modules.get('source_correspondence_inputs', {}).items():
    assert sha(name) == expected
for source, record in modules['proof_files'].items():
    add(source, record['compiler_manifest'], record)
for source, revision in revisions.items():
    add(source, revision['compiler_manifest'])
    selection[source]['deliberate_source_revision'] = revision
    for field in ('preserved_history','new_review','independent_confirmation','named_build'):
        selection[source]['evidence_sha256'][revision[field]] = sha(revision[field])

applied = read('book/coverage/applied-audit16-additions.json')
assert sha(applied['mapped_ledger']) == applied['mapped_ledger_sha256']
assert sha('book/coverage/applied-promotions.json') == applied['mapped_promotions_sha256']
assert sha('book/coverage/inventory.json') == applied['inventory_sha256']
assert sha(applied['integrity_check']) == applied['integrity_check_sha256']
assert sha(applied['actual_passing_base_aggregate']) == applied['actual_passing_base_aggregate_sha256']
for name, expected in applied['source_sha256'].items():
    assert sha(name) == expected
for name, record in applied['import_closure'].items():
    assert sha(name) == record['source_sha256']
for name, expected in applied['independent_source_reviews'].items():
    assert sha(name) == expected
for record in applied['modules']:
    assert sha(record['standalone_evidence']) == record['standalone_evidence_sha256']
    add(record['source'], record['standalone_evidence'])

core = read('book/coverage/core-audit16-additions.json')
for name, expected in core['review_sha256'].items():
    assert sha(name) == expected
assert sha(core['mapped_ledger']) == core['mapped_ledger_sha256']
assert sha('book/coverage/inventory.json') == core['current_inventory_sha256']
builder_hashes = core['builder_sha256']
if isinstance(builder_hashes, str):
    builder_hashes = {'book/coverage/build_core.py': builder_hashes}
for name, expected in builder_hashes.items():
    assert sha(name) == expected
for name, expected in core.get('source_correction_provenance', {}).items():
    assert sha(name) == expected
for source, record in core['proof_files'].items():
    assert sha(record['compiler_manifest']) == record['compiler_manifest_sha256']
    add(source, record['compiler_manifest'])

for source in selection:
    for dependency in re.findall(r'^import\s+(SafeLearning\.\S+)',
                                 (ROOT / source).read_text(), re.M):
        assert 'verification/lean/' + dependency.replace('.', '/') + '.lean' in selection

result = dict(
    status='explicit_source_matched_stable_requires_fresh_aggregate_audit',
    created_at_utc=datetime.now(timezone.utc).isoformat(), basis=report,
    baseline_selection=baseline, baseline_selection_sha256=sha(baseline),
    proof_files=dict(sorted(selection.items())), proof_file_count=len(selection),
    new_file_count=len(set(selection) - set(old)), deliberate_baseline_source_revisions=revisions,
    coverage_complete=False,
    limits=['Preparation checks actual evidence and import closure; it does not claim the fresh aggregate audit has run.'])
destination = ROOT / 'reports/full-coverage/checkpoint-16-selection.json'
destination.write_text(json.dumps(result, indent=2) + '\n')
print(f'Prepared {len(selection)} source-matched files; {result["new_file_count"]} new. Actual evidence and import closure checked.')
