"""Apply exactly the reviewed 49 literal labels and five supplied Viability proofs.

The immutable working20 ledger is retained byte-exact in baseline20; its narrow
freeze selection normalization is recorded separately. No old mathematical
exercise/material decision, review time or proof execution is recomputed.
"""
from pathlib import Path
import copy
import hashlib
import json
import sys

ROOT = Path(__file__).resolve().parents[2]
BASE = 'book/coverage/checks/applied-future21'
IDENTITY = BASE + '/applied-source48-owner-identity-and-additions21-v1.json'
IDENTITY_SHA = 'b7fe8e2cf29b0939e9bb4b4c86ee552a30cf075645a211d9c94b2be2cd52c3ec'
INVENTORY = 'book/coverage/inventory-after-correction48.json'
INVENTORY_SHA = '2daa285ff1cbc2ad0db045e00e1271b6cb58ce809f5a8328120286748250c108'


def sha(name):
    return hashlib.sha256((ROOT / name).read_bytes()).hexdigest()


def read(name):
    return json.loads((ROOT / name).read_text())


def build():
    assert sha(IDENTITY) == IDENTITY_SHA
    binding = read(IDENTITY)
    assert binding['inventory_sha256'] == sha(INVENTORY) == sha('book/coverage/inventory.json') == INVENTORY_SHA
    inventory = read(INVENTORY)
    pages = set(binding['source_sha256'])
    assert binding['exact_current_owned_exercise_records'] == [e for e in inventory['exercises'] if e['source'] in pages]
    assert binding['exact_current_owned_material_records'] == [u for u in inventory['material_source_units'] if u['source'] in pages]
    for p, h in binding['source_sha256'].items():
        assert sha(p) == h == inventory['source_sha256'][p]
    for p, h in binding['old_proof_source_sha256'].items():
        assert sha(p) == h
    history = binding['preserved_frozen20_metadata']
    for x in history:
        assert sha(x['preserved_history']) == x['sha256']
        assert sha(x['frozen20_original']) == x['frozen20_original_sha256']
    ledger = read(history[0]['preserved_history'])
    promotions = read(history[1]['preserved_history'])
    original_ledger = copy.deepcopy(ledger)
    original_promotions = copy.deepcopy(promotions)
    peer = read(binding['nonformal_review'])
    assert sha(binding['nonformal_review']) == binding['nonformal_review_sha256']
    current_units = {u['key']: u for u in inventory['material_source_units']}
    claims = {k: c for c in ledger['material_claims'] for k in c['source_unit_keys']}
    provenance = {
        'inventory': INVENTORY,
        'inventory_sha256': INVENTORY_SHA,
        'owner_identity_and_exact_additions': IDENTITY,
        'owner_identity_and_exact_additions_sha256': sha(IDENTITY),
        'exact_unchanged_owned_exercises': 128,
        'exact_unchanged_owned_physical_units': 2059,
        'scope': 'All old source44/47 decisions and original review/execution times remain historical. Current48 Applied page bytes and every full owned inventory record are equal to source47.'
    }
    changed = []
    for item in binding['nonformal49_current48_bindings']:
        key = item['source_unit_key']
        reviewed = item['original47_reviewed_row']
        claim = claims[key]
        assert current_units[key] == item['exact_current48_inventory_record'] == reviewed['exact_inventory_record']
        assert claim == reviewed['original_pending_ledger_record']
        assert claim['source_unit_keys'] == [key] and claim['status'] == 'pending'
        assert reviewed['material_status'] == 'not_formalizable'
        assert reviewed['lean_declarations'] == reviewed['missing_clauses'] == []
        assert item['normalized_owner_status'] == 'not_a_formal_claim'
        claim.update({
            'kind': 'individually_reviewed_pedagogical_label_navigation_or_study_instruction',
            'status': 'not_a_formal_claim',
            'lean_declarations': [],
            'hypotheses': copy.deepcopy(reviewed['hypotheses']),
            'correspondence': reviewed['per_unit_reason'],
            'remaining_gaps': [],
            'source_review': {
                'file': binding['nonformal_review'],
                'sha256': binding['nonformal_review_sha256'],
                'reviewer': peer['reviewed_by'],
                'reviewed_at_utc': peer['reviewed_at_utc'],
                'source_unit_key': key,
                'unit_text_sha256': reviewed['unit_text_sha256'],
                'original_review_inventory': peer['inventory'],
                'original_review_inventory_sha256': peer['inventory_sha256'],
                'classification_scope': reviewed['per_unit_reason'],
                'status_normalization': item['normalization_reason'],
                'current48_unchanged_identity': provenance
            }
        })
        promotions['material'][key] = {
            'source_text_sha256': claim['text_sha256'],
            'claim': {k: copy.deepcopy(v) for k, v in claim.items() if k not in ['source', 'source_unit_keys', 'source_sha256', 'text_sha256']},
            'source_review': copy.deepcopy(claim['source_review']),
            'current48_unchanged_source_identity': provenance
        }
        changed.append(key)
    assert len(changed) == len(set(changed)) == 49
    added = []
    for item in binding['new_cross_owner_proof_bindings']:
        p, h = item['source'], item['source_sha256']
        assert p not in ledger['proof_files'] and sha(p) == h
        for execution in item['actual_standalone_and_named_records']:
            assert sha(execution['path']) == execution['sha256']
            actual = read(execution['path'])
            assert actual == execution['actual_record'] and actual['exit_code'] == 0
            assert actual['source_sha256_before'] == actual['source_sha256_after'] == h
            assert sha(actual['log']) == actual['log_sha256']
            if 'source_snapshot' in actual:
                assert sha(actual['source_snapshot']) == h
        ledger['proof_files'][p] = h
        added.append(p)
    assert len(added) == 5
    integration = {
        'inventory': INVENTORY,
        'inventory_sha256': INVENTORY_SHA,
        'identity_and_additions': IDENTITY,
        'identity_and_additions_sha256': sha(IDENTITY),
        'baseline20_ledger': history[0]['preserved_history'],
        'baseline20_ledger_sha256': history[0]['sha256'],
        'baseline20_promotions': history[1]['preserved_history'],
        'baseline20_promotions_sha256': history[1]['sha256'],
        'original49_review': binding['nonformal_review'],
        'original49_review_sha256': binding['nonformal_review_sha256'],
        'original49_review_time_preserved': peer['reviewed_at_utc'],
        'new_nonformal_material_keys': changed,
        'new_explicit_cross_owner_proof_sources': added,
        'cross_owner_mapping': binding['cross_owner_mapping'],
        'scope': 'Only49 exact nonformal units change Applied dispositions. Five genuine new proof rows are supplied for eight Module-owned Viability whole reviews. No Applied exercise claim is changed.'
    }
    ledger['current48_owner_identity'] = provenance
    promotions['current48_owner_identity'] = provenance
    ledger['current21_review_integration'] = integration
    promotions['current21_review_integration'] = integration
    ledger['generated_at_utc'] = binding['prepared_at_utc']
    assert ledger['exercises'] == original_ledger['exercises']
    assert promotions['exercises'] == original_promotions['exercises']
    for old, new in zip(original_ledger['material_claims'], ledger['material_claims']):
        if old['source_unit_keys'][0] not in changed:
            assert old == new
    for key, old in original_promotions['material'].items():
        assert key not in changed and promotions['material'][key] == old
    assert ledger['counts'] == original_ledger['counts']
    # Check every named claim against actual current declaration indices.
    sys.path.insert(0, str(ROOT / 'book/coverage'))
    from lean_names import declarations
    names = set()
    for p in ledger['proof_files']:
        names.update(d['name'] for d in declarations((ROOT / p).read_text()))
    for claim in ledger['material_claims']:
        assert set(claim['lean_declarations']) <= names
    for exercise in ledger['exercises']:
        for claim in exercise['claims']:
            assert set(claim['lean_declarations']) <= names
    current_ledger = read(history[0]['original'])
    current_promotions = read(history[1]['original'])
    assert current_ledger in [original_ledger, ledger]
    assert current_promotions in [original_promotions, promotions]
    for p, data in [(history[0]['original'], ledger), (history[1]['original'], promotions)]:
        (ROOT / p).write_text(json.dumps(data, indent=2, ensure_ascii=False) + '\n')
    status_counts = {}
    for claim in ledger['material_claims']:
        status_counts[claim['status']] = status_counts.get(claim['status'], 0) + 1
    print(json.dumps({'status': 'passed_exact49_nonformal_and_five_cross_owner_proof_additions', 'inventory_sha256': INVENTORY_SHA, 'ledger_sha256': sha(history[0]['original']), 'promotions_sha256': sha(history[1]['original']), 'counts': ledger['counts'], 'material_status_counts': status_counts, 'new_nonformal_rows': len(changed), 'new_proof_sources': len(added)}))


if __name__ == '__main__':
    build()
