"""Prepare a reversible identity-only Module23 candidate after Root source51.

The seven existing whole decisions, all original source50 reviews and proof
evidence stay exact. No live ledger, HTML, inventory or Lean build is written.
Run only after Root supplies the actual immutable source51 inventory hash.
"""
from pathlib import Path
from datetime import datetime, timezone
import copy, hashlib, json, sys

ROOT = Path(__file__).resolve().parents[2]
OLD = 'book/coverage/checks/modules-future23/source50'
NEW = 'book/coverage/checks/modules-future23/source51'
OLD_INVENTORY = 'book/coverage/inventory-after-correction50.json'
OLD_INVENTORY_SHA = 'dec8a34d0313fbc19846489f4d8c2f6e51734a135df6145829993fae0f80d91c'
NEW_INVENTORY = 'book/coverage/inventory-after-correction51.json'
OLD_CANDIDATE = OLD + '/modules23-candidate-source50-identity-v1.json'
OLD_CANDIDATE_SHA = '8cb3ecf6c7f4f82da069c3c0d862297e7bbcbc6468d8550e11b2335ecc1cf8d1'
OLD_OFFER = OLD + '/modules-audit23-candidate-source50-additions-v1-reviewed.json'
OLD_OFFER_SHA = '6877a893c909451b36949f23df5619d538c1cf3fc238d5f90316b8dd5f16f7f7'
OLD_PEER = OLD + '/modules23-source50-identity-independent-applied-confirmation-v2.json'
OLD_PEER_SHA = '01def97eceb62e65e172da12ba8b7d8ab759ddbd8568b514b26ef379ed13c26a'
sha = lambda n: hashlib.sha256((ROOT / n).read_bytes()).hexdigest()
read = lambda n: json.loads((ROOT / n).read_text())
ref = lambda n: {'file': n, 'sha256': sha(n)}
def write(n, body):
    p = ROOT / n
    assert not p.exists(), n
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(body, indent=2, ensure_ascii=False) + '\n')
def atomsha(record):
    return hashlib.sha256(json.dumps(record, sort_keys=True, separators=(',', ':'), ensure_ascii=False).encode()).hexdigest()

def main():
    assert len(sys.argv) == 2 and len(sys.argv[1]) == 64, 'Pass Root actual immutable inventory51 SHA only.'
    new_sha = sys.argv[1]
    assert sha(OLD_INVENTORY) == OLD_INVENTORY_SHA
    assert sha(NEW_INVENTORY) == new_sha == sha('book/coverage/inventory.json')
    assert sha(OLD_CANDIDATE) == OLD_CANDIDATE_SHA
    assert sha(OLD_OFFER) == OLD_OFFER_SHA
    assert sha(OLD_PEER) == OLD_PEER_SHA
    root_apply = 'reports/full-coverage/source51-apply-execution-v1.json'
    root_postwrite = 'book/coverage/checks/root-source-batch51/postwrite-source-integrity-v1.json'
    assert sha(root_apply) == '7a04def00fc4edbdd0459bc56d90e2cc056c08f6cda712e1f09fde75f4faea8f'
    assert sha(root_postwrite) == 'f8c4e5a6b98e170d37aba3cefad14948d79ff544f26cbe66ca2ac4ca0981a03f'
    root_execution, root_integrity = read(root_apply), read(root_postwrite)
    assert root_execution['actual_exit_code'] == root_integrity['actual_exit_code'] == 0
    assert root_integrity['inventory_after'] == NEW_INVENTORY
    assert root_integrity['inventory_after_sha256'] == new_sha
    assert sha(root_execution['log']) == root_execution['log_sha256']
    old_inv, new_inv = read(OLD_INVENTORY), read(NEW_INVENTORY)
    candidate, offer = read(OLD_CANDIDATE), read(OLD_OFFER)
    assert offer['module_ledger'] == OLD_CANDIDATE and offer['module_ledger_sha256'] == OLD_CANDIDATE_SHA
    assert candidate['current_inventory'] == OLD_INVENTORY and candidate['current_inventory_sha256'] == OLD_INVENTORY_SHA
    scope = set(candidate['scope_pages'])
    assert scope == set(candidate['source_sha256']) and len(scope) == 11
    for p, expected in candidate['source_sha256'].items():
        assert sha(p) == expected == old_inv['source_sha256'][p] == new_inv['source_sha256'][p], p
    for p, expected in candidate['chapter_fragment_sha256'].items():
        assert sha(p) == expected, p
    changed = {}
    changed_text = {}
    unchanged_rows = {}
    for kind in ('exercises', 'material_source_units'):
        old_all = {r['key']: r for r in old_inv[kind]}
        new_all = {r['key']: r for r in new_inv[kind]}
        assert old_all.keys() == new_all.keys()
        changed[kind] = [k for k in old_all if old_all[k] != new_all[k]]
        assert all(old_all[k]['source'] == 'SafeLearning/cmdp.html' for k in changed[kind])
        changed_text[kind] = [k for k in old_all if
            {n: v for n, v in old_all[k].items() if n != 'source_sha256'} !=
            {n: v for n, v in new_all[k].items() if n != 'source_sha256'}]
        owned = {k: r for k, r in old_all.items() if r['source'] in scope}
        assert owned == {k: r for k, r in new_all.items() if r['source'] in scope}
        unchanged_rows[kind] = [{'key': k, 'source': r['source'], 'line': r['line'], 'locator': r['locator'],
                                'text_sha256': r['text_sha256'], 'source_sha256': r['source_sha256'],
                                'entire_inventory_record_sha256': atomsha(r)} for k, r in owned.items()]
    assert len(unchanged_rows['exercises']) == 217 and len(unchanged_rows['material_source_units']) == 4977
    assert len(changed_text['exercises']) == 1 and len(changed_text['material_source_units']) == 1
    assert set(changed_text['material_source_units']) == {'cmdp.html::node-1138'}
    protection = {p: sha(p) for p in ['book/coverage/core.json', 'book/coverage/foundations.json',
                                    'book/coverage/applied.json', 'book/coverage/modules.json']}
    assert protection['book/coverage/modules.json'] == offer['baseline22_module_ledger']['sha256']
    baseline22 = read('reports/full-coverage/checkpoint-22-manifest.json')
    for p, row in baseline22['proof_files'].items():
        assert sha(p) == row['sha256'], p
    assert len(baseline22['proof_files']) == 1113
    for p, row in candidate['proof_files'].items():
        assert sha(p) == row['sha256'], p
    for p, expected in offer['required_evidence_artifacts_sha256'].items():
        assert sha(p) == expected, p
    prepared = datetime.now(timezone.utc).isoformat()
    side = NEW + '/unchanged-owned-literal-identity-v1.json'
    write(side, {'status': 'prepared_exact_source50_to50_unchanged_module_owned_literal_identities',
        'prepared_at_utc': prepared, 'prepared_by': '/root/modules_resume',
        'historical_inventory': ref(OLD_INVENTORY), 'current_inventory': ref(NEW_INVENTORY),
        'original_reviewed_candidate': ref(OLD_CANDIDATE), 'original_reviewed_offer': ref(OLD_OFFER),
        'original_independent_candidate_peer': ref(OLD_PEER),
        'owned_source_sha256': candidate['source_sha256'], 'unchanged_owned_literals': unchanged_rows,
        'entire_inventory_record_hash_encoding': 'SHA256 of UTF8 json.dumps(record, sort_keys=True, separators=(comma,colon), ensure_ascii=False)',
        'changed_other_owner_entire_record_keys': changed,
        'changed_other_owner_literal_text_or_structure_keys': changed_text,
        'actual_root_source51_apply': ref(root_apply), 'actual_root_source51_postwrite': ref(root_postwrite),
        'scope': 'All 217 owned exercise records and 4977 owned material records are equal in their entirety. Root Monitoring relative-interior correction changes only another owner page. All original semantic bodies, statuses, review times and proof evidence stay historical source50.'})
    guard_name = NEW + '/candidate-identity-binding-integrity-v1.json'
    guard = {'status': 'exact_current51_unchanged_module_literals_and_source50_candidate_semantics_passed',
        'checked_at_utc': prepared, 'historical_inventory': ref(OLD_INVENTORY), 'current_inventory': ref(NEW_INVENTORY),
        'identity_sidecar': ref(side), 'original_source50_candidate': ref(OLD_CANDIDATE),
        'original_source50_reviewed_offer': ref(OLD_OFFER), 'original_source50_candidate_peer': ref(OLD_PEER),
        'counts': {'owned_entire_exercise_records': 217, 'owned_entire_material_records': 4977,
                   'unchanged_candidate_exercises': len(candidate['exercises']),
                   'unchanged_candidate_material_claims': len(candidate['material_claims']),
                   'unchanged_proof_rows': len(candidate['proof_files']), 'baseline22_proof_hashes': 1113},
        'protected_live22_ledgers_sha256': protection,
        'all_original_semantic_and_proof_rows_preserved': True, 'live_ledger_mutated': False,
        'scope': 'Actual isolated identity-only candidate preparation. No new mathematical review, compilation, live ledger installation, global validation or aggregate23 claimed.'}
    write(guard_name, guard)
    out = copy.deepcopy(candidate)
    out['current_inventory'] = NEW_INVENTORY
    out['current_inventory_sha256'] = new_sha
    identity = ref(side)
    for e in out['exercises']:
        e['source51_unchanged_literal_identity'] = identity
    for c in out['material_claims']:
        c['source51_unchanged_literal_identity'] = identity
    out['current_identity_binding_validation'] = {**ref(guard_name), 'status': guard['status'],
        'validator': str(Path(__file__).relative_to(ROOT)), 'validator_sha256': sha(str(Path(__file__).relative_to(ROOT)))}
    out['inventory_identity_rebase51'] = {'identity_sidecar': identity,
        'original_source50_candidate': ref(OLD_CANDIDATE), 'original_source50_reviewed_offer': ref(OLD_OFFER),
        'original_source50_candidate_peer': ref(OLD_PEER), 'no_changed_owned_literals': True,
        'prepared_at_utc': prepared, 'original_semantic_times_preserved': True}
    reversed_out = copy.deepcopy(out)
    for e in reversed_out['exercises']:
        del e['source51_unchanged_literal_identity']
    for c in reversed_out['material_claims']:
        del c['source51_unchanged_literal_identity']
    for k in ['current_inventory', 'current_inventory_sha256', 'current_identity_binding_validation']:
        reversed_out[k] = copy.deepcopy(candidate[k])
    del reversed_out['inventory_identity_rebase51']
    assert reversed_out == candidate
    target = NEW + '/modules23-candidate-source51-identity-v1.json'
    write(target, out)
    for p, expected in protection.items():
        assert sha(p) == expected, p
    assert sha(OLD_CANDIDATE) == OLD_CANDIDATE_SHA and sha(OLD_OFFER) == OLD_OFFER_SHA
    print(json.dumps({'status': guard['status'], 'candidate': ref(target), 'identity_sidecar': ref(side),
                      'identity_integrity': ref(guard_name), 'unchanged_candidate_counts': out['counts'],
                      'scope': 'NEW isolated identity candidate only; final source51 peer/offer are separate.'}))

if __name__ == '__main__':
    main()
