"""Independently replay candidate identities, inverse deltas and receipt links."""
from pathlib import Path
from datetime import datetime, timezone
from collections import Counter
import copy
import hashlib
import importlib.util
import json
import sys
import time

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[4]
BASE = ROOT / 'book/coverage/checks/recovery32-review'
FILES = 'book/coverage/checks/recovery32/'
started = datetime.now(timezone.utc).isoformat()
tick = time.monotonic()


def locate(name):
    return Path(name) if Path(name).is_absolute() else ROOT / name


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def ref(name):
    path = locate(name)
    return {'file': path.relative_to(ROOT).as_posix(), 'sha256': sha(path), 'bytes': path.stat().st_size}


def read(name):
    return json.loads(locate(name).read_bytes())


def checked(value):
    assert sha(locate(value['file'])) == value['sha256'], value['file']
    return locate(value['file'])


mapping = read(FILES + 'five-source-map-v1.json')
readiness = read(FILES + 'five-canonical-readiness-v1.json')
bindings = read(FILES + 'two-owner-candidate-bindings-v1.json')
assert readiness['status'] == 'passed_five_exact_reviewed_Source81_standalone_and_named_pairs_unselected'
assert readiness['errors'] == [] and readiness['actual_compiler_command_count'] == 10
assert readiness['source_map']['sha256'] == sha(ROOT / (FILES + 'five-source-map-v1.json'))
assert bindings['changed_pending_material_count'] == 6 and bindings['exercise_changes'] == 0
inventory = read('book/coverage/inventory.json')
indexed = {row['key']: row for row in inventory['material_source_units']}
spec = importlib.util.spec_from_file_location('independent32_names', ROOT / 'book/coverage/lean_names.py')
names = importlib.util.module_from_spec(spec)
spec.loader.exec_module(names)
protected = mapping['protected_inputs_sha256']
for name, digest in protected.items():
    assert sha(locate(name)) == digest, name

source_reviews = []
peer_literals = {}
canonical_theorems = {}
for row in mapping['sources']:
    canonical = checked(row['canonical_source_ref'])
    assert canonical.read_bytes() == checked(row['original_source']).read_bytes()
    declarations = names.declarations(canonical.read_text())
    assert declarations == row['public_declarations']
    theorem_names = [d['name'] for d in declarations if d['kind'] in ['theorem', 'lemma']]
    assert len(theorem_names) == row['public_theorem_count']
    canonical_theorems[row['family']] = set(theorem_names)
    peer = json.loads(checked(row['independent_peer']).read_bytes())
    assert peer['status'].startswith('passed') and peer['errors'] == []
    assert peer.get('protection_errors', []) == []
    source_ref = peer.get('actual_source', peer.get('entire_source', peer.get('source')))
    assert source_ref['sha256'] == row['canonical_source_ref']['sha256']
    family = row['family']
    if family == 'Frobenius15':
        assert all(d['whole_semantic_approved'] and d['missing_requirements'] == []
                   for d in peer['full_current_literal_decisions'].values())
        literals = peer['entire_current_literals']
    elif family in ['WeightedAngle11', 'MetricExamplesAndCertifiedBalls10']:
        decision = next(iter(peer['whole_unit_decisions'].values()))
        assert decision.get('whole_semantic_approved', decision.get('current_whole_semantic_approved')) is True
        assert decision.get('missing_requirements', decision.get('current_missing_requirements')) == []
        literal = peer['entire_current_literal']
        literals = {literal['key']: literal}
    elif family == 'Convolution13':
        assert peer['whole_current_literal_decision']['approved'] is True
        assert peer['whole_current_literal_decision']['remaining_mathematical_gaps'] == []
        literal = peer['entire_current_literal']
        literals = {literal['key']: literal}
    else:
        assert family == 'StaticRegret20' and peer['mathematical_current_whole359_approved'] is True
        request = json.loads(checked(row['author_request']).read_bytes())
        assert peer['reviewed_request']['sha256'] == row['author_request']['sha256']
        literal = request['current_unit']
        literals = {literal['key']: literal}
    assert set(literals) == set(row['approved_whole_material_keys'])
    for key, literal in literals.items():
        assert literal == indexed[key], key
        peer_literals[key] = literal
    pairs = [p for p in readiness['actual_paired_records'] if p['source']['file'] == row['canonical_source']]
    assert len(pairs) == 2 and {p['kind'] for p in pairs} == {'standalone', 'named'}
    for pair in pairs:
        record = json.loads(checked(pair['actual_record']).read_bytes())
        assert record['status'] == 'passed' and type(record['actual_exit_code']) is int and record['actual_exit_code'] == 0
        assert record['protection_errors'] == [] and pair['actual_exit_code'] == 0
        assert record['source'] == row['canonical_source_ref']
        assert record['source_sha256_before'] == record['source_sha256_after'] == row['canonical_source_ref']['sha256']
        assert checked(record['source_snapshot']).read_bytes() == canonical.read_bytes()
        assert checked(record['raw_log']) == checked(pair['raw_log'])
        expected = ['lake', 'env', 'lean', 'SafeLearning/' + canonical.name] if pair['kind'] == 'standalone' else ['lake', 'build', 'SafeLearning.' + canonical.stem]
        assert record['command'] == expected and record['actual_workdir'] == str(ROOT / 'verification/lean')
        assert datetime.fromisoformat(record['finished_at_utc']) >= datetime.fromisoformat(record['started_at_utc'])
        assert record['elapsed_seconds'] >= 0
    source_reviews.append({'family': family, 'canonical_source': row['canonical_source_ref'],
                           'exact_prior_full_body_peer': row['independent_peer'],
                           'entire_current_literal_keys': row['approved_whole_material_keys'],
                           'fresh_actual_pairs': pairs, 'original_source_bytes_and_namespace_preserved': True})

assert len(peer_literals) == 6
selected31 = read('reports/full-coverage/lean-checkpoint-31-source81-v1/verification-original.json')
geometry_file = 'verification/lean/SafeLearning/CompleteFoundationsGeometry.lean'
assert sha(ROOT / geometry_file) == selected31['proof_sha256'][geometry_file]
geometry_names = {row['name'] for row in names.declarations((ROOT / geometry_file).read_text())}
selected_certificate = 'SafeLearning.CompleteFoundationsGeometry.positive_lipschitz_certified_ball'
assert selected_certificate in geometry_names
owner_reviews = []
changed_keys = set()
for replacement in bindings['replacements']:
    before = json.loads(checked(replacement['before']).read_bytes())
    after = json.loads(checked(replacement['candidate']).read_bytes())
    owner = Path(replacement['destination']).stem
    assert before.get('owner', owner) == owner
    assert owner in ['foundations', 'applied']
    assert after['exercises'] == before['exercises']
    assert len(after['material_claims']) == len(before['material_claims'])
    inverse = copy.deepcopy(after)
    modified = []
    for i, (old, new) in enumerate(zip(before['material_claims'], after['material_claims'])):
        if old == new:
            continue
        assert old['status'] == 'pending' and new['status'] == 'proved' and new['remaining_gaps'] == []
        assert new['original_pending_record'] == old
        assert old['source_unit_keys'] == new['source_unit_keys'] and len(old['source_unit_keys']) == 1
        key = old['source_unit_keys'][0]
        literal = peer_literals[key]
        for field in ['id', 'source_unit_keys', 'source', 'source_sha256', 'source_text', 'text_sha256', 'source_text_sha256', 'locator']:
            if field in old:
                assert new[field] == old[field], (key, field)
        assert new['statement_in_prose'] == literal['source_text']
        assert new['text_sha256'] == literal['text_sha256']
        family = next(row['family'] for row in mapping['sources'] if key in row['approved_whole_material_keys'])
        approved = canonical_theorems[family] | ({selected_certificate} if family == 'MetricExamplesAndCertifiedBalls10' else set())
        assert set(new['lean_declarations']) == approved
        assert set(n for clause in new['all_subclaim_correspondence'] for n in clause['lean_declarations']) == approved
        assert new['hypotheses'] and new['correspondence']
        source_row = next(row for row in mapping['sources'] if row['family'] == family)
        assert new['independent_whole_literal_peer'] == source_row['independent_peer']
        assert new['actual_canonical_pairs'] == ref(FILES + 'five-canonical-readiness-v1.json')
        inverse['material_claims'][i] = copy.deepcopy(old)
        changed_keys.add(key)
        modified.append({'key': key, 'claim_id': new['id'], 'family': family,
                         'unchanged_exact_literal': literal, 'all_subclaim_correspondence': new['all_subclaim_correspondence'],
                         'hypotheses': new['hypotheses'], 'exact_full_peer': new['independent_whole_literal_peer']})
    assert {row['claim_id'] for row in modified} == set(replacement['changed_claim_ids'])
    new_files = [row['canonical_source'] for row in mapping['sources'] if row['owner'] == owner]
    if isinstance(inverse['proof_files'], list):
        assert set(inverse['proof_files']) - set(before['proof_files']) == set(new_files)
        inverse['proof_files'] = [name for name in inverse['proof_files'] if name not in new_files]
        for name in new_files:
            del inverse['proof_sha256'][name]
    else:
        assert set(inverse['proof_files']) - set(before['proof_files']) == set(new_files)
        for name in new_files:
            del inverse['proof_files'][name]
    if 'material_claim_statuses' in after['counts']:
        assert after['counts']['material_claim_statuses'] == dict(Counter(row['status'] for row in after['material_claims']))
        inverse['counts']['material_claim_statuses'] = before['counts']['material_claim_statuses']
    del inverse['recovery32_reviewed_candidate_mapping']
    assert inverse == before, owner
    owner_reviews.append({'owner': owner, 'baseline': replacement['before'], 'candidate': replacement['candidate'],
                          'exact_inverse_to_baseline': True, 'unchanged_all_exercises_and_other_material_claims': True,
                          'reviewed_changed_rows': modified})

assert changed_keys == {'primer-linalg.html::node-131', 'primer-linalg.html::node-202', 'primer-linalg.html::node-315',
                        'primer-linalg.html::node-317', 'primer-rl-nn.html::node-359', 'primer-rl-nn.html::node-1531'}
audit = read(FILES + 'isolated-ledger-audit-v1.json')
assert audit['integrity_status'] == 'passed' and audit['errors'] == [] and audit['mathematical_coverage_complete'] is False
assert audit['counts']['material_review_statuses'] == {'reviewed': 4841, 'pending': 7933}
assert [audit['counts']['statuses'][key] for key in ['exercise:complete_math', 'exercise:partial', 'exercise:pending']] == [536, 8, 12]
execution = read(FILES + 'isolated-validator-execution-v1.json')
assert execution['status'] == 'passed' and execution['actual_exit_code'] == 0
checked(execution['actual_helper']); checked(execution['validator_source']); checked(execution['raw_log']); checked(execution['audit'])
for name, digest in protected.items():
    assert sha(locate(name)) == digest, name

report = {'status': 'passed_independent_exact_six_whole_material_candidate32_mapping_and_native_receipt_review',
          'errors': [], 'started_at_utc': started, 'finished_at_utc': datetime.now(timezone.utc).isoformat(),
          'elapsed_seconds': time.monotonic() - tick, 'actual_reader_helper': ref(Path(__file__)),
          'binding': ref(FILES + 'two-owner-candidate-bindings-v1.json'),
          'source_map': ref(FILES + 'five-source-map-v1.json'), 'actual_readiness': ref(FILES + 'five-canonical-readiness-v1.json'),
          'full_source_correspondence_and_domain_peers_retained': source_reviews, 'owner_candidate_reviews': owner_reviews,
          'changed_whole_material_units': 6, 'new_canonical_theorems': 69, 'fresh_actual_compiler_commands': 10,
          'exact_inverse_all_other_fields_and_all_exercises_preserved': True,
          'counts': audit['counts'], 'protected_inputs_unchanged': True,
          'helper_code_reviews': {
              'runtime_preparation': {'source': ref('book/coverage/checks/recovery32_prepare_runtime.py'),
                  'full_code_read': True, 'status': 'approved_exact_reviewed_plan_only',
                  'reasons': ['Selected31 proof identities agree with the actual passing audit.', 'New sources require exact native standalone/named commands, source/log hashes, disjoint declarations and source-identifying passed full peers.', 'Only selected source files and aggregate are copied; cache symlinks are recorded as runtime-only.']},
              'delivery_closure': {'source': ref('book/coverage/checks/recovery_finish_delivery31.py'),
                  'full_code_read': True, 'status': 'approved_actual_current_receipts_only',
                  'reasons': ['Both commit versions require actual successful same-commit Pages, three jobs and all31 asset SHA matches.', 'Native workdirs and before/after helper hashes are checked against current exact helper bytes.', 'Historical documents are preserved and full mathematical coverage remains explicitly unfinished.']}},
          'scope': 'Independent mapping, identity, exact inverse and genuine receipt association review. Previous full mathematical body reviews remain the proof-to-source authority; no new compiler, aggregate, kernel or publication execution is claimed.',
          'coverage_complete': False}
output = BASE / 'six-whole-material-candidate32-independent-review-v1.json'
with output.open('x') as file:
    file.write(json.dumps(report, indent=2, ensure_ascii=False) + '\n')
print(json.dumps({'status': report['status'], 'report': ref(output), 'changed_material_units': 6,
                  'actual_compiler_receipts_checked': 10, 'exact_inverse': True, 'coverage_complete': False}))
