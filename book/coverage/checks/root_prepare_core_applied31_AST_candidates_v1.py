"""Prepare exact existing-proof/structural-leaf candidates; never install owners."""
from pathlib import Path
from datetime import datetime, timezone
import copy, hashlib, json

ROOT = Path(__file__).resolve().parents[3]
CONTEXT = Path('/tmp/root_tmp_lean_current81_historical_owner30_context_v1.json')
CONTEXT_SHA = 'f9490760c85e8be1392f271bdf65e193e5a5e4cfc2ba29b5f7e4d32c682a7af9'
PEER = 'book/coverage/checks/future31-applied/AST23-child-and35-structural-independent-applied30b-v1/AST23-Applied21-complete-reuses-two-clause-gaps-and35-pure-NF-leaves-independent-applied30b-closed-peer-v1.json'
PEER_SHA = 'bb3c92b97798dd355c1d353bd264701e846804ab22dd1c93ccd379de68dcec49'
OUT = ROOT/'book/coverage/checks/future31-core/Core15NF-Applied21proof1NF-candidates-v1'

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p): return {'file': str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p), 'sha256': sha(p), 'bytes': p.stat().st_size}
def encode(d): return (json.dumps(d, indent=2, ensure_ascii=False)+'\n').encode()
def new(p, data):
    p.parent.mkdir(parents=True, exist_ok=True)
    with p.open('xb') as out: out.write(data)

assert sha(CONTEXT) == CONTEXT_SHA and sha(ROOT/PEER) == PEER_SHA
context = json.loads(CONTEXT.read_bytes()); review = json.loads((ROOT/PEER).read_bytes())
assert review['status'].startswith('passed') and review['errors'] == []
def guard():
    assert sha(CONTEXT) == CONTEXT_SHA and sha(ROOT/PEER) == PEER_SHA
    for n, h in {**context['pins_sha256'], **context['held_current_source_sha256'], **context['owners_sha256']}.items():
        assert sha(ROOT/n) == h, n
guard(); assert not OUT.exists()
inventory_path = ROOT/'book/coverage/inventory-after-correction81.json'
inventory = json.loads(inventory_path.read_bytes()); indexed = {r['key']: r for r in inventory['material_source_units']}
proofs = [(i, r) for i, r in enumerate(review['per_child_decisions']) if r['whole_child_approved']]
assert len(proofs) == 21 and {r['inventory_key'] for r in review['per_child_decisions'] if not r['whole_child_approved']} == {'primer-rl-nn.html::node-1531', 'primer-rl-nn.html::node-359'}
nonformal = [(i, r) for i, r in enumerate(review['per_structural_leaf_decisions']) if r['owner_scope'] in ['core', 'applied']]
assert len(nonformal) == 16 and all(r['whole_selected_leaf_NF_approved'] is True for _, r in nonformal)
assert sum(r['owner_scope'] == 'core' for _, r in nonformal) == 15
outputs = {}; inverses = {}; changed = {}; originals = {}
promo_path = ROOT/'book/coverage/applied-promotions.json'
original_promo = json.loads(promo_path.read_bytes()); promotions = copy.deepcopy(original_promo)
promo_old = {}
for owner in ['core', 'applied']:
    p = ROOT/f'book/coverage/{owner}.json'; old = json.loads(p.read_bytes()); data = copy.deepcopy(old)
    decisions = [(i, r, True, 'per_child_decisions') for i, r in proofs] if owner == 'applied' else []
    decisions += [(i, r, False, 'per_structural_leaf_decisions') for i, r in nonformal if r['owner_scope'] == owner]
    prior_rows = {}; modifications = []
    for index, decision, proved, table in decisions:
        key = decision['inventory_key']; literal = decision['entire_current_material_literal']
        assert indexed[key] == literal, key
        matches = [(i, r) for i, r in enumerate(data['material_claims']) if key in r['source_unit_keys'] and r['status'] == 'pending']
        assert len(matches) == 1 and matches[0][1]['source_unit_keys'] == [key], key
        i, row = matches[0]; prior_rows[str(i)] = copy.deepcopy(row)
        assert row.get('text_sha256', literal['text_sha256']) == literal['text_sha256']
        declarations = decision['exact_support'] if proved else []
        assert not proved or declarations and decision['remaining_gaps'] == []
        row.update(status='proved' if proved else 'not_a_formal_claim',
            kind='independently_reviewed_literal_material_unit', lean_declarations=declarations,
            correspondence=decision['full_clause_correspondence'] if proved else decision['reason'], remaining_gaps=[],
            independent_source_review={'peer': ref(ROOT/PEER), 'decision_JSON_pointer': [table, index], 'exact_current81_inventory': ref(inventory_path), 'whole_individual_leaf_approved': True, 'enclosing_math_or_handler_scope_promoted': False})
        if not proved: row['hypotheses'] = []
        modifications.append({'inventory_key': key, 'row_index': i, 'before_status': 'pending', 'after_status': row['status'], 'declarations': declarations})
        if owner == 'applied':
            promo_old[key] = copy.deepcopy(promotions['material'].get(key))
            promotions['material'][key] = {'source_text_sha256': literal['text_sha256'], 'claim': copy.deepcopy(row), 'current81_independent_exact_literal_reuse': row['independent_source_review']}
    data['current_inventory'] = str(inventory_path.relative_to(ROOT)); data['current_inventory_sha256'] = sha(inventory_path)
    data['future31_source81_AST_reuse_draft_binding'] = {'status': 'candidate_only_existing_selected30_proofs_and_pure_leaf_NF', 'original_raw30': ref(p), 'independent_peer': ref(ROOT/PEER), 'individual_row_changes': modifications, 'current_selected30_reused_audit': context['actual_audit'], 'new_proof_files_added': 0, 'whole_exercise_promotions': 0, 'coverage_complete': False}
    inverse = copy.deepcopy(data)
    for i, row in prior_rows.items(): inverse['material_claims'][int(i)] = row
    inverse.pop('future31_source81_AST_reuse_draft_binding'); inverse['current_inventory'] = old['current_inventory']; inverse['current_inventory_sha256'] = old['current_inventory_sha256']
    assert inverse == old
    outputs[owner] = data; inverses[owner] = prior_rows; changed[owner] = modifications; originals[owner] = ref(p)
inverse_promotions = copy.deepcopy(promotions)
for key, value in promo_old.items():
    if value is None: inverse_promotions['material'].pop(key)
    else: inverse_promotions['material'][key] = value
assert inverse_promotions == original_promo
guard()
OUT.mkdir(parents=True)
for owner, data in outputs.items(): new(OUT/f'{owner}-candidate.json', encode(data))
new(OUT/'applied-promotions-candidate.json', encode(promotions))
inverse_path = OUT/'exact-row-and-metadata-inverse-v1.json'
new(inverse_path, encode({'original_raw_owner30_files': originals, 'original_raw_promotions': ref(promo_path), 'old_rows_by_owner_and_index': inverses, 'old_promotion_entries': promo_old, 'whole_decoded_originals_recovered': True, 'original_raw_bytes_unchanged': True}))
offer = {'status': 'prepared_current81_Core15NF_Applied21proved1NF_candidates_only_no_installation', 'helper': ref(Path(__file__)), 'context': ref(CONTEXT), 'independent_AST_full_semantic_peer': ref(ROOT/PEER), 'inventory': ref(inventory_path), 'candidates': {owner: ref(OUT/f'{owner}-candidate.json') for owner in outputs}, 'promotions': ref(OUT/'applied-promotions-candidate.json'), 'inverse': ref(inverse_path), 'individual_changes': changed, 'current_raw_owner_or_selection_or_canonical_mutation': False, 'new_proof_files_added': 0, 'coverage_complete': False}
new(OUT/'draft-offer-v1.json', encode(offer)); guard()
print(json.dumps({'status': offer['status'], 'offer': ref(OUT/'draft-offer-v1.json'), 'changes': {k: len(v) for k, v in changed.items()}, 'coverage_complete': False}))
