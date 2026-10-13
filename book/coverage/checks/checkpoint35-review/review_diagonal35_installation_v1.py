"""Independently verify exact owner candidates without installing them."""
from collections import Counter, defaultdict
from datetime import datetime, timezone
from hashlib import sha256
from pathlib import Path
import gc
import json
import re

ROOT = Path(__file__).resolve().parents[4]
FOLDER = ROOT / 'book/coverage/checks/checkpoint35-review'
BINDING = 'book/coverage/checks/checkpoint35-ledgers/owner-candidate-binding-v1.json'
BINDING_SHA = '0f9e6484bf38f7f722ef69943edbe5e86201ba5703d51b3dd27822ba2a18ed52'
DIAGONAL = 'book/coverage/checks/checkpoint35-review/diagonal35-exact-material-mapping-proposal-v1.json'
GAUSSIAN = 'book/coverage/checks/checkpoint35-review/adaptive-gaussian35-proposed-exact-mapping-v1.json'


def digest(file):
    import hashlib
    with (ROOT / file).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def ref(file):
    return {'file': file, 'sha256': digest(file)}


def exact(row):
    assert digest(row['file']) == row['sha256'], row['file']


def read(file):
    return json.loads((ROOT / file).read_bytes())


def encoded_digest(value):
    # Stream the deterministic encoding to avoid another full candidate copy.
    result = sha256()
    for chunk in json.JSONEncoder(indent=2, ensure_ascii=False).iterencode(value):
        result.update(chunk.encode())
    result.update(b'\n')
    return result.hexdigest()


def pointer_parent(value, pointer):
    for part in pointer[:-1]:
        value = value[part]
    return value, pointer[-1]


def exists(parent, key):
    return key < len(parent) if isinstance(parent, list) else key in parent


def undo(value, patches):
    for patch in reversed(patches):
        parent, key = pointer_parent(value, patch['pointer'])
        assert exists(parent, key) and parent[key] == patch['after'], patch['pointer']
        if patch['before_exists']:
            parent[key] = patch['before']
        else:
            del parent[key]


def replay(value, patches):
    for patch in patches:
        parent, key = pointer_parent(value, patch['pointer'])
        assert exists(parent, key) == patch['before_exists'], patch['pointer']
        if patch['before_exists']:
            assert parent[key] == patch['before'], patch['pointer']
            parent[key] = patch['after']
        elif isinstance(parent, list):
            assert key == len(parent), patch['pointer']
            parent.append(patch['after'])
        else:
            parent[key] = patch['after']


def accumulate(owner, counts, materials):
    for exercise in owner['exercises']:
        counts[exercise['status']] += 1
        for claim in exercise['claims']:
            for key in claim.get('source_unit_keys', []):
                materials[key].append(claim['status'])
    for claim in owner['material_claims']:
        for key in claim.get('source_unit_keys', []):
            materials[key].append(claim['status'])
    for key in owner.get('pending_source_units', []):
        if isinstance(key, dict):
            key = key.get('key', key.get('inventory_key'))
        materials[key].append('pending')


assert digest(BINDING) == BINDING_SHA
binding = read(BINDING)
exact(binding['inventory'])
inventory = read(binding['inventory']['file'])
units = {u['key']: u for u in inventory['material_source_units']}
del inventory
documents = {file: read(file) for file in [DIAGONAL, GAUSSIAN]}
for proposal_ref in binding['mapping_proposals']:
    exact(proposal_ref)
    document = documents[proposal_ref['file']]
    assert document['status'].startswith('approved') and not document['errors']
    exact(document['inventory'])
    exact(document['independent_source_review'])

diagonal = documents[DIAGONAL]
assert len(diagonal['material_mappings']) == 16
assert diagonal['counts'] == {
    'new_whole_mathematical_units': 9,
    'literal_topic_citation_labels': 4,
    'refresh_existing_proved_units_no_completion_credit': 3,
    'total_mapping_proposals': 16,
}
diagonal_keys = {m['material_unit_key'] for m in diagonal['material_mappings']}
gaussian_keys = {m['material_unit_key'] for m in documents[GAUSSIAN]['material_mappings']}
assert len(diagonal_keys) == 16 and len(gaussian_keys) == 7 and not diagonal_keys & gaussian_keys
proposal_index = {}
for file, document in documents.items():
    for mapping in document['material_mappings']:
        key = mapping['material_unit_key']
        assert key not in proposal_index
        proposal_index[key] = (file, document, mapping)
        unit = units[key]
        assert unit['text_sha256'] == mapping.get('exact_text_sha256', mapping.get('text_sha256'))
        assert unit['source_sha256'] == mapping['source_sha256'] == digest(unit['source'])

before_exercises, after_exercises = Counter(), Counter()
before_material, after_material = defaultdict(list), defaultdict(list)
checked_owners = []
changed_keys = set()
changed_exercises = []
diagonal_checks = []
unchanged_broad_count = 0
withheld_checks = []
allowed_row_fields = {
    'status', 'lean_declarations', 'hypotheses', 'correspondence', 'remaining_gaps',
    'independent_source_review35', 'exact_source90_mapping_proposal35', 'exact_source90_text_sha256',
}

for replacement in binding['replacements']:
    owner = Path(replacement['destination']).stem
    for field in ['before', 'candidate', 'exact_inverse', 'preserved_original']:
        exact(replacement[field])
    assert replacement['before']['sha256'] == replacement['preserved_original']['sha256']
    assert digest(replacement['destination']) == replacement['before']['sha256']
    baseline = read(replacement['preserved_original']['file'])
    candidate = read(replacement['candidate']['file'])
    inverse = read(replacement['exact_inverse']['file'])
    assert inverse['baseline'] == replacement['before']
    assert inverse['candidate'] == replacement['candidate']
    assert inverse['preserved_original'] == replacement['preserved_original']
    accumulate(baseline, before_exercises, before_material)
    accumulate(candidate, after_exercises, after_material)

    expected_top = {'material_claims', 'proof_files', 'counts', 'current_checkpoint35_identity'}
    if owner == 'modules':
        expected_top |= {'exercises', 'declarations'}
    changed_top = {k for k in set(baseline) | set(candidate) if baseline.get(k) != candidate.get(k)}
    assert changed_top == expected_top
    assert len(baseline['material_claims']) == len(candidate['material_claims'])
    owner_changed = []
    for old, new in zip(baseline['material_claims'], candidate['material_claims']):
        assert old['id'] == new['id']
        if old != new:
            assert len(old.get('source_unit_keys', [])) == 1
            key = old['source_unit_keys'][0]
            assert key in proposal_index and old['id'].endswith(('::claim-review', '::semantic-review'))
            file, document, mapping = proposal_index[key]
            assert mapping.get('owner', 'modules') == owner
            assert set(k for k in set(old) | set(new) if old.get(k) != new.get(k)) <= allowed_row_fields
            for field in ['status', 'lean_declarations', 'hypotheses', 'correspondence', 'remaining_gaps']:
                assert new[field] == mapping[field], (key, field)
            assert new['source_unit_keys'] == [key]
            assert new['independent_source_review35'] == document['independent_source_review']
            assert new['exact_source90_mapping_proposal35'] == ref(file)
            assert new['exact_source90_text_sha256'] == units[key]['text_sha256']
            changed_keys.add(key)
            owner_changed.append(key)
            if key in diagonal_keys:
                diagonal_checks.append({'material_unit_key': key, 'owner': owner,
                                        'before_status': old['status'], 'after_status': new['status'],
                                        'exact_text_sha256': units[key]['text_sha256'],
                                        'all_approved_mapping_fields_exact': True})
        if len(old.get('source_unit_keys', [])) > 1:
            assert old == new
            if old['id'].startswith('modules::proved-material-'):
                unchanged_broad_count += 1

    for withheld in diagonal['overlapping_or_adjacent_whole_units_retained_pending']:
        key = withheld['material_unit_key']
        before_rows = [c for c in baseline['material_claims'] if key in c.get('source_unit_keys', [])]
        after_rows = [c for c in candidate['material_claims'] if key in c.get('source_unit_keys', [])]
        if before_rows:
            assert before_rows == after_rows and any(c['status'] == 'pending' for c in after_rows)
            withheld_checks.append({'material_unit_key': key, 'owner': owner,
                                    'all_rows_unchanged': True, 'pending_whole_row_retained': True})

    assert len(baseline['exercises']) == len(candidate['exercises'])
    for old, new in zip(baseline['exercises'], candidate['exercises']):
        assert old['inventory_key'] == new['inventory_key']
        if old != new:
            assert owner == 'modules' and old['inventory_key'] == 'safe-bo-theory.html#book-m5-b2'
            assert old['status'] == 'partial' and new['status'] == 'complete_math'
            gaussian = documents[GAUSSIAN]
            assert len(old['claims']) == len(new['claims']) == len(gaussian['exercise_claim_mappings'])
            mappings = {m['claim_id']: m for m in gaussian['exercise_claim_mappings']}
            for old_claim, new_claim in zip(old['claims'], new['claims']):
                assert old_claim['id'] == new_claim['id']
                assert old_claim['statement_in_prose'] == new_claim['statement_in_prose']
                mapping = mappings[old_claim['id']]
                for field in ['status', 'lean_declarations', 'hypotheses', 'correspondence', 'remaining_gaps']:
                    assert new_claim[field] == mapping[field]
                assert not new_claim['remaining_gaps'] and new_claim['status'] != 'pending'
            allowed = {'claims', 'status', 'independent_whole_exercise_review35'}
            assert {k for k in set(old) | set(new) if old.get(k) != new.get(k)} == allowed
            changed_exercises.append(old['inventory_key'])

    for file, value in baseline['proof_files'].items():
        assert candidate['proof_files'][file] == value
    added_files = set(candidate['proof_files']) - set(baseline['proof_files'])
    expected_files = {s['file'] for s in diagonal['proof_sources']}
    if owner == 'modules':
        expected_files.add('verification/lean/SafeLearning/CompleteModulesAdaptiveGaussianEnvelope35.lean')
    assert added_files == expected_files
    for file in added_files:
        assert candidate['proof_files'][file] == digest(file)
    new_declarations = []
    if owner == 'modules':
        assert candidate['declarations'][:len(baseline['declarations'])] == baseline['declarations']
        new_declarations = candidate['declarations'][len(baseline['declarations']):]
        assert len(new_declarations) == 13
        parsed = []
        for file in added_files:
            text = (ROOT / file).read_text()
            namespace = re.search(r'^namespace (\S+)', text, re.M)[1]
            for match in re.finditer(r'^(theorem|lemma)\s+(\w+)', text, re.M):
                parsed.append({'name': namespace + '.' + match[2], 'kind': match[1], 'file': file})
        assert sorted(new_declarations, key=lambda d: d['name']) == sorted(parsed, key=lambda d: d['name'])
        assert candidate['counts']['exercise_status'] == dict(Counter(e['status'] for e in candidate['exercises']))
        assert candidate['counts']['exercise_claim_status'] == dict(Counter(c['status'] for e in candidate['exercises'] for c in e['claims']))
        assert candidate['counts']['material_claim_status'] == dict(Counter(c['status'] for c in candidate['material_claims']))
        assert candidate['counts']['new_declarations'] == len(candidate['declarations']) == 4040
    else:
        assert 'declarations' not in baseline and 'declarations' not in candidate
        assert candidate['counts']['proof_files'] == len(candidate['proof_files']) == 190
        assert candidate['counts']['exercise_statuses'] == dict(Counter(e['status'] for e in candidate['exercises']))
    identity = candidate['current_checkpoint35_identity']
    assert identity['baseline_owner'] == replacement['before']
    assert identity['inventory'] == binding['inventory']
    assert identity['mapping_proposals'] == binding['mapping_proposals']
    assert identity['coverage_complete'] is False and identity['unchanged_site_sources'] is True

    # Check every reverse patch against the actual candidate, then the complete
    # restored object and its deterministic bytes against the preserved original.
    undo(candidate, inverse['patches'])
    assert candidate == baseline
    restored_sha = encoded_digest(candidate)
    assert restored_sha == replacement['preserved_original']['sha256']
    replay(candidate, inverse['patches'])
    replayed_sha = encoded_digest(candidate)
    assert replayed_sha == replacement['candidate']['sha256']
    checked_owners.append({
        'owner': owner, 'candidate': replacement['candidate'],
        'exact_inverse': replacement['exact_inverse'],
        'preserved_original': replacement['preserved_original'],
        'reverse_patch_count': len(inverse['patches']),
        'restored_exact_sha256': restored_sha, 'replayed_exact_sha256': replayed_sha,
        'changed_exact_material_keys': sorted(owner_changed),
        'added_proof_sources': [ref(file) for file in sorted(added_files)],
        'appended_theorem_count': len(new_declarations),
        'all_nonpatch_changes_excluded': True,
    })
    del baseline, candidate, inverse
    gc.collect()

for owner in ['foundations', 'applied']:
    file = f'book/coverage/{owner}.json'
    assert digest(file) == binding['protected_input_sha256'][file]
    ledger = read(file)
    accumulate(ledger, before_exercises, before_material)
    accumulate(ledger, after_exercises, after_material)
    del ledger
    gc.collect()

assert changed_keys == diagonal_keys | gaussian_keys
assert changed_exercises == ['safe-bo-theory.html#book-m5-b2']
assert len(diagonal_checks) == 16
assert sum(x['before_status'] == 'pending' for x in diagonal_checks) == 13
assert sum(x['after_status'] == 'not_a_formal_claim' for x in diagonal_checks) == 4
assert sum(x['before_status'] == 'proved' and x['after_status'] == 'proved' for x in diagonal_checks) == 3
assert dict(before_exercises) == {'complete_math': 538, 'pending': 11, 'partial': 7}
assert dict(after_exercises) == binding['exercise_counts'] == {'complete_math': 539, 'pending': 11, 'partial': 6}
before_status = {key: 'pending' if 'pending' in v else 'reviewed' for key, v in before_material.items()}
after_status = {key: 'pending' if 'pending' in v else 'reviewed' for key, v in after_material.items()}
assert set(before_status) == set(after_status) == set(units)
assert dict(Counter(before_status.values())) == {'reviewed': 4858, 'pending': 7916}
assert dict(Counter(after_status.values())) == binding['material_counts'] == {'reviewed': 4878, 'pending': 7896}
actual_newly_closed = {key for key in before_status if before_status[key] != after_status[key]}
assert actual_newly_closed == set(binding['changed_whole_material_units'])
assert len(actual_newly_closed) == 20 and len(actual_newly_closed & diagonal_keys) == 13
assert set(binding['refreshed_material_units']) == {
    m['material_unit_key'] for m in diagonal['material_mappings'] if m['action'].startswith('refresh_')
}
assert binding['whole_material_units_completed'] == 20 and binding['refreshed_existing_material_units'] == 3
assert binding['coverage_complete'] is False and binding['owner_installation_claimed'] is False

for file, expected in binding['protected_input_sha256'].items():
    assert digest(file) == expected, file
for row in diagonal['proof_sources'] + diagonal['source_refs']:
    exact(row)

result = {
    'status': 'approved',
    'reviewer': '/root/review_diagonal35',
    'reviewed_at_utc': datetime.now(timezone.utc).isoformat(),
    'errors': [],
    'owner_candidate_binding': ref(BINDING),
    'inventory': binding['inventory'],
    'approved_mapping_proposals': [DIAGONAL],
    'approved_mapping_proposal_refs': [ref(DIAGONAL)],
    'other_peer_proposal_checked_for_exact_scope_only': ref(GAUSSIAN),
    'independent_source_review': diagonal['independent_source_review'],
    'candidate_inverse_reviews': checked_owners,
    'diagonal_exact_row_checks': sorted(diagonal_checks, key=lambda r: r['material_unit_key']),
    'diagonal_counts': {'exact_changed_rows': 16, 'new_reviewed_units': 13,
                        'new_mathematical_units': 9, 'new_literal_labels': 4,
                        'existing_proved_mapping_refreshes': 3},
    'global_counts_recomputed_independently': {
        'exercises_before': dict(before_exercises), 'exercises_after': dict(after_exercises),
        'materials_before': dict(Counter(before_status.values())),
        'materials_after': dict(Counter(after_status.values())),
        'newly_reviewed_exact_unit_count': len(actual_newly_closed),
    },
    'unchanged_broad_proved_material_component_count': unchanged_broad_count,
    'pending_ancestor_and_adjacent_scope_checks': withheld_checks,
    'only_changed_exercise': changed_exercises,
    'all_other_exercise_rows_unchanged': True,
    'protected_input_hashes_verified_count': len(binding['protected_input_sha256']),
    'source_refs': diagonal['source_refs'],
    'proof_sources': diagonal['proof_sources'],
    'compiler_invoked': False,
    'candidates_canonical_owner_ledgers_source_selection_progress_mutated': False,
    'limits': ['Approves installation of this exact binding only for the enumerated diagonal proposal; the separate Gaussian reviewer supplies the other half of the proposal union.', 'The separate Gaussian material/B2 changes were compared to their approved proposal for exact scope, not independently re-reviewed for mathematical meaning by this agent.', 'Inverse patches restore the complete deterministic bytes of preserved original owners; forward replay reconstructs the exact candidate bytes.', 'No aggregate compiler success, kernel replay, publication, or full coverage completion is inferred.'],
    'coverage_complete': False,
}
file = 'book/coverage/checks/checkpoint35-review/diagonal35-independent-owner-installation-review-v1.json'
(ROOT / file).write_text(json.dumps(result, indent=2, ensure_ascii=False) + '\n')
print(json.dumps({'status': result['status'], 'review': ref(file),
                  'diagonal_counts': result['diagonal_counts'],
                  'global_counts': result['global_counts_recomputed_independently'],
                  'protected_input_hashes_verified_count': result['protected_input_hashes_verified_count']}))
