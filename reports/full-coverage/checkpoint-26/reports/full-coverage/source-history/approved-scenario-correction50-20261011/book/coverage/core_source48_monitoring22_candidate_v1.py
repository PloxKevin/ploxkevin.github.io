#!/usr/bin/env python3
"""Build an isolated, incremental Core22 candidate from original reviewed bytes.

This helper never writes the current ledger, HTML, inventory, or prior evidence.
Its packet contains independently reviewed exact source records and paired actual
compiler evidence. Aggregate verification remains a separate subsequent action.
"""
from pathlib import Path
from collections import Counter
from datetime import datetime, timezone
import copy
import hashlib
import json
from lean_names import declarations

ROOT = Path(__file__).resolve().parents[2]
PACKET = 'book/coverage/checks/future22-monitoring/core22-reviewed-source-packet-v1.json'
OUT = 'book/coverage/checks/future22-monitoring/core-source48-candidate-ledger22-v1.json'
INTEGRITY = 'book/coverage/checks/future22-monitoring/core-source48-candidate-integrity22-v1.json'
BASE = 'reports/full-coverage/checkpoint-21/book/coverage/core.json'
BASE_SHA = 'dc2dd0b0d061cec76dc21e2698d08a5311ca83b1477f784e1426ee99f092dc7a'
INV_SHA = '2daa285ff1cbc2ad0db045e00e1271b6cb58ce809f5a8328120286748250c108'

def sha(name):
    return hashlib.sha256((ROOT / name).read_bytes()).hexdigest()

def read(name):
    return json.loads((ROOT / name).read_text())

def write_new(name, value):
    with (ROOT / name).open('x') as f:
        f.write(json.dumps(value, indent=2) + '\n')

assert not (ROOT / OUT).exists() and not (ROOT / INTEGRITY).exists()
assert sha(BASE) == sha('book/coverage/core.json') == BASE_SHA
assert sha('book/coverage/inventory.json') == sha('book/coverage/inventory-after-correction48.json') == INV_SHA
inv = read('book/coverage/inventory.json')
source_before = {n: sha(n) for n in inv['source_sha256']}
assert source_before == inv['source_sha256']
packet = read(PACKET)
assert packet['status'] == 'independently_reviewed_exact_source_packet_actual_paired_compilers_requires_fresh_aggregate'
assert packet['baseline_ledger_sha256'] == BASE_SHA
assert packet['inventory_sha256'] == INV_SHA
for n, h in packet['protected_sha256'].items():
    assert sha(n) == h, n
baseline = read(BASE)
candidate = copy.deepcopy(baseline)
units = {u['key']: u for u in inv['material_source_units']}
exercise = next(e for e in candidate['exercises'] if e['inventory_key'] == 'cmdp.html::exercise-21')
original_exercise = copy.deepcopy(exercise)
assert exercise['status'] == 'pending' and all(c['status'] == 'pending' for c in exercise['claims'])

exported = set()
new_proof_theorems = {}
for n, p in packet['proof_files'].items():
    assert n not in baseline['proof_files'] and sha(n) == p['sha256'], n
    ds = declarations((ROOT / n).read_text())
    exported.update(d['name'] for d in ds)
    new_proof_theorems[n] = sum(d['kind'] in ('theorem', 'lemma') for d in ds)
    for e, h in p['evidence_sha256'].items():
        assert sha(e) == h, e
    pairs = p['actual_paired_records']
    assert len(pairs) == 2
    for pair in pairs:
        rec = pair['actual_record']
        log = pair['raw_log']
        assert sha(rec['file']) == rec['sha256']
        assert sha(log['file']) == log['sha256']
        actual = read(rec['file'])
        assert actual.get('exit_code', actual.get('actual_exit_code')) == 0
        assert actual['source_unchanged'] is True
        assert actual['source'] == n
        assert actual['source_sha256_before'] == actual['source_sha256_after'] == p['sha256']
        assert actual['log_sha256'] == log['sha256']
        assert actual['actual_workdir'] == str(ROOT / 'verification/lean')
        expected_command = (['lake', 'env', 'lean', str(Path(n).relative_to('verification/lean'))]
                            if pairs.index(pair) == 0 else
                            ['lake', 'build', 'SafeLearning.' + Path(n).stem])
        assert actual['command'] == expected_command
        assert pair['source_snapshot']['sha256'] == p['sha256']
        assert sha(pair['source_snapshot']['file']) == p['sha256']
    candidate['proof_files'][n] = p['sha256']

# Dependencies can be named by a review only if their selected original bytes
# remain identical. Public definitions are referenceable but do not inflate the
# public theorem count.
for n, h in baseline['proof_files'].items():
    expected = h if isinstance(h, str) else h['sha256']
    assert sha(n) == expected, n
    exported.update(d['name'] for d in declarations((ROOT / n).read_text()))

def component_reason(c):
    reason = c.get('per_component_reason', c.get('reason', c.get('scope_and_reason')))
    assert isinstance(reason, str) and reason.strip(), c
    return reason

def component_claim(c, claim_id, review, hypotheses):
    names = c['lean_declarations']
    assert names and set(names) <= exported
    reason = component_reason(c)
    return dict(id=claim_id, kind='independently_reviewed_precise_source_components',
                status='proved', statement_in_prose=c.get('clause', c.get('component', reason)),
                lean_declarations=names, hypotheses=c.get('hypotheses', hypotheses),
                correspondence=reason, remaining_gaps=[],
                independent_review=review, original_review_component=copy.deepcopy(c))

whole_units = {}
new_material = []
review_bindings = {}
for index, binding in enumerate(packet['independent_reviews']):
    path = binding['file']
    assert sha(path) == binding['sha256']
    review = read(path)
    assert not review.get('errors')
    assert review['inventory_sha256'] == INV_SHA
    assert review['source_sha256'] == inv['source_sha256']['SafeLearning/cmdp.html']
    review_bindings[path] = binding['sha256']
    ref = dict(source=path, sha256=binding['sha256'],
               original_review_time=review.get('reviewed_at_utc'))
    for record in review.get('records', []):
        assert record['exercise_key'] == exercise['inventory_key']
        assert record['exercise_text_sha256'] == exercise['text_sha256']
        assert record['source_text'] == exercise['source_text']
        assert record['whole_exercise_approved'] is False
        for j, c in enumerate(record['reviewed_components']):
            exercise['claims'].append(component_claim(c,
                f"{exercise['inventory_key']}::monitoring22-review{index}-component{j}",
                ref, record.get('hypotheses', [])))
    for record in review.get('material_units', []):
        key = record['source_unit_key']
        u = units[key]
        assert record['source'] == u['source']
        assert record['source_sha256'] == u['source_sha256']
        assert record['unit_text_sha256'] == u['text_sha256']
        assert record['source_text'] == u['source_text']
        if record.get('whole_unit_approved'):
            assert record['material_status'] == 'proved'
            assert record['review_status'] == 'approved_complete_source'
            assert not record['missing_clauses']
            assert record['lean_declarations'] and set(record['lean_declarations']) <= exported
            assert key not in whole_units
            whole_units[key] = (record, ref)
        else:
            assert record['material_status'] == 'pending'
            for j, c in enumerate(record['reviewed_components']):
                claim = component_claim(c, f'{key}::monitoring22-review{index}-component{j}',
                                        ref, record.get('hypotheses', []))
                claim.update(source_unit_keys=[key], source=u['source'],
                    source_sha256=u['source_sha256'], text_sha256=u['text_sha256'],
                    source_text=u['source_text'], parent_remaining_gaps=record['missing_clauses'])
                new_material.append(claim)

assert set(whole_units) == set(packet['approved_whole_material_units'])
changed_material_ids = []
for claim in candidate['material_claims']:
    covered = set(claim['source_unit_keys']) & set(whole_units)
    if not covered:
        continue
    assert len(claim['source_unit_keys']) == 1 and len(covered) == 1
    assert claim['status'] == 'pending'
    record, ref = whole_units[next(iter(covered))]
    claim.update(kind='independently_reviewed_literal_material_unit', status='proved',
        lean_declarations=record['lean_declarations'], hypotheses=record.get('hypotheses', []),
        correspondence=record['per_unit_reason'], remaining_gaps=[], independent_review=ref,
        original_complete_literal_review_record=copy.deepcopy(record))
    changed_material_ids.append(claim['id'])
assert len(changed_material_ids) == len(whole_units)
# Earlier pending component reports remain exact original evidence. For a newly
# complete physical unit, their proved component claims carry no pending status.
candidate['material_claims'].extend(new_material)
assert packet['remaining_exercise_gaps']
for claim in exercise['claims']:
    if claim['status'] == 'pending':
        claim['remaining_gaps'] = packet['remaining_exercise_gaps']
        claim['correspondence'] = 'Exact whole exercise retained; final remaining clauses are explicitly unresolved after the new independent reviews.'
exercise['status'] = 'partial'
candidate['generated_at_utc'] = datetime.now(timezone.utc).isoformat()
candidate['counts']['exercise_statuses'] = dict(sorted(Counter(e['status'] for e in candidate['exercises']).items()))
candidate['counts']['material_claims'] = len(candidate['material_claims'])
candidate['limits'].append('Core22 isolated monitoring candidate adds exact independently reviewed components and complete literal units; the complete exercise remains partial. Fresh aggregate Lean build, kernel and axiom checks are required.')
assert candidate['proof_files'].keys() >= baseline['proof_files'].keys()
assert all(candidate['proof_files'][n] == h for n, h in baseline['proof_files'].items())
assert [e for e in candidate['exercises'] if e['inventory_key'] != exercise['inventory_key']] == [e for e in baseline['exercises'] if e['inventory_key'] != exercise['inventory_key']]
base_unchanged = [c for c in baseline['material_claims'] if c['id'] not in changed_material_ids]
current_unchanged = [c for c in candidate['material_claims'][:len(baseline['material_claims'])] if c['id'] not in changed_material_ids]
assert base_unchanged == current_unchanged
assert sha('book/coverage/core.json') == BASE_SHA
assert {n: sha(n) for n in source_before} == source_before
for n, h in packet['protected_sha256'].items():
    assert sha(n) == h, n
write_new(OUT, candidate)
write_new(INTEGRITY, dict(status='passed', created_at_utc=datetime.now(timezone.utc).isoformat(),
    helper=str(Path(__file__).relative_to(ROOT)), helper_sha256=sha(str(Path(__file__).relative_to(ROOT))),
    packet=PACKET, packet_sha256=sha(PACKET), baseline_ledger=BASE,
    baseline_ledger_sha256=BASE_SHA, candidate_ledger=OUT, candidate_ledger_sha256=sha(OUT),
    original_exercise=original_exercise, changed_exercise_key=exercise['inventory_key'],
    changed_whole_material_units=sorted(whole_units), changed_material_ids=changed_material_ids,
    unchanged_exercise_count=len(candidate['exercises']) - 1,
    unchanged_baseline_material_claim_count=len(base_unchanged),
    unchanged_baseline_proof_rows=len(baseline['proof_files']),
    added_component_material_claims=len(new_material),
    new_proof_files=len(packet['proof_files']), new_public_theorems=sum(new_proof_theorems.values()),
    new_public_theorems_by_source=new_proof_theorems, review_sha256=review_bindings,
    source_sha256_unchanged=source_before, counts=candidate['counts'],
    scope='Isolated exact reviewed candidate. Current ledger unchanged; no aggregate or whole-exercise completion claimed.'))
print(json.dumps(dict(candidate=OUT, sha256=sha(OUT), proof_files=len(packet['proof_files']),
                     public_theorems=sum(new_proof_theorems.values()),
                     whole_material_units=len(whole_units), counts=candidate['counts'])))
