from pathlib import Path
from datetime import datetime, timezone
import copy, hashlib, json, sys

ROOT = Path('/home/oxrexkevin/SafetyBased')
def path(n): return Path(n) if Path(n).is_absolute() else ROOT / n
def sha(n): return hashlib.sha256(path(n).read_bytes()).hexdigest()
def read(n): return json.loads(path(n).read_text())
def ref(n): return {'file': str(n), 'sha256': sha(n)}
def checked(r):
    assert set(r) == {'file', 'sha256'} and sha(r['file']) == r['sha256'], r
    return read(r['file'])
def zero(d, code=0):
    v = [d[k] for k in ['exit_code', 'actual_exit_code'] if k in d]
    assert v and all(type(x) is int and x == code for x in v)

offer_name = 'book/coverage/checks/applied-future26/source52-v2/applied-audit26-candidate-source52-additions-v1.json'
assert sha(offer_name) == '4e41448a66d7f5b970fc1ec296588eff9ec453e70e2836b3a966068ec9c96325'
offer = read(offer_name)
assert offer['coverage_complete'] is False and offer['new_material_keys'] == ['primer-probability.html::node-371']
assert offer['inventory_sha256'] == sha(offer['inventory']) == sha('book/coverage/inventory.json') == '38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
assert sha(offer['mapped_ledger']) == offer['mapped_ledger_sha256']
assert sha(offer['mapped_promotions']) == offer['mapped_promotions_sha256']
assert sha(offer['candidate_builder']['file']) == offer['candidate_builder']['sha256']
binding = checked(offer['original_review_bindings']); alias_doc = checked(offer['canonical_path_aliases'])
old = read('book/coverage/applied.json'); oldprom = read('book/coverage/applied-promotions.json')
candidate = read(offer['mapped_ledger']); promotions = read(offer['mapped_promotions'])
for row in offer['baseline25_owner_assets']:
    assert sha(row['original']['file']) == row['original']['sha256'] == row['exact_byte_copy']['sha256'] == sha(row['exact_byte_copy']['file'])
    assert path(row['original']['file']).read_bytes() == path(row['exact_byte_copy']['file']).read_bytes()
assert binding['baseline25_unpruned_working_history'] == offer['baseline25_owner_assets']
assert len(old['exercises']) == 128 and sum(len(e['claims']) for e in old['exercises']) == 468
assert candidate['exercises'] == old['exercises'] and promotions['exercises'] == oldprom['exercises']
key = offer['new_material_keys'][0]
original = next(c for c in old['material_claims'] if key in c['source_unit_keys'])
claim = next(c for c in candidate['material_claims'] if key in c['source_unit_keys'])
assert original['status'] == 'pending' and claim['status'] == 'proved' and claim['remaining_gaps'] == []
assert claim['approved_components'] == original['approved_components'] and len(claim['approved_components']) == 4
assert claim['preserved_entire_original_partial_claim'] == original
review = checked(binding['original_semantic_peer'])
assert binding['entire_original_semantic_body_and_time'] == review
assert sha(binding['original_semantic_peer']['file']) == sha('/tmp/applied-joint-density371-independent-foundations-full-source-review25-v1.json') == '50033ac5648f23b0cf3298da2019122d8567444085819f759479036ce610ceb4'
unit = review['material_units'][0]
current = next(u for u in read(offer['inventory'])['material_source_units'] if u['key'] == key)
assert unit['entire_inventory_record'] == current and unit['whole_source_unit_approved'] is True and unit['missing_clauses'] == []
assert claim['original_complete_literal_review_record'] == unit
for field, value in [('lean_declarations', unit['lean_declarations']), ('hypotheses', unit['hypotheses']), ('correspondence', unit['per_component_reason'])]: assert claim[field] == value
assert claim['source_review']['original_review_time'] == review['reviewed_at_utc']
assert claim['source_review']['reviewer'] == review['reviewer']
assert claim['source_review']['classification_scope'] == unit['per_component_reason']
assert claim['source_review']['sha256'] == binding['original_semantic_peer']['sha256']
assert binding['material_rows'] == [{'source_unit_key': key, 'entire_inventory_record': current, 'original_complete_reviewed_row': unit, 'original_source_review': claim['source_review'], 'preserved_original_partial_claim': original, 'normalized_exact_ledger_claim': claim}]
expected = copy.deepcopy(original)
for f in ['kind', 'status', 'lean_declarations', 'hypotheses', 'correspondence', 'remaining_gaps', 'source_review', 'original_complete_literal_review_record', 'preserved_entire_original_partial_claim']: expected[f] = copy.deepcopy(claim[f])
assert expected == claim
assert len(candidate['material_claims']) == len(old['material_claims']) == 1954
assert [x for x in candidate['material_claims'] if key not in x['source_unit_keys']] == [x for x in old['material_claims'] if key not in x['source_unit_keys']]
inverse = copy.deepcopy(candidate)
inverse['material_claims'] = copy.deepcopy(old['material_claims'])
assert candidate['current26_material_candidate_integration'] == promotions['current26_material_candidate_integration']
inverse.pop('current26_material_candidate_integration'); inverse['generated_at_utc'] = old['generated_at_utc']
assert set(candidate['proof_files']) == set(old['proof_files']) | set(offer['proof_files'])
inverse['proof_files'] = {n:h for n,h in inverse['proof_files'].items() if n not in offer['proof_files']}
assert inverse == old
pinv = copy.deepcopy(promotions); pinv.pop('current26_material_candidate_integration'); pinv['material'][key] = copy.deepcopy(oldprom['material'][key]); assert pinv == oldprom
assert promotions['material'][key]['claim'] == {k:v for k,v in claim.items() if k not in ['source', 'source_unit_keys', 'source_sha256', 'text_sha256']}
assert promotions['material'][key]['source_review'] == claim['source_review']
assert alias_doc['aliases'] == binding['canonical_original_path_aliases'] and len(alias_doc['aliases']) == 90
for original_path, row in alias_doc['aliases'].items():
    assert Path(original_path).is_absolute() and not Path(row['file']).is_absolute()
    assert path(row['file']).read_bytes() == path(original_path).read_bytes() and sha(row['file']) == row['sha256']

sys.path.insert(0, str(ROOT / 'book/coverage')); from lean_names import declarations
ready_names = ['book/coverage/checks/applied-future26/joint-density371/two-source15-canonical-paired-build-readiness-v1.json', 'book/coverage/checks/applied-future26/cvar-fractional-selector/one-source8-canonical-paired-build-readiness-v1.json']
source_rows = []; paired = []; theorems = []; full_decl_names = []
for rn in ready_names:
    ready = read(rn); assert 'passed' in ready['status'] and ready['coverage_complete'] is False
    prep = checked(ready['canonical_preparation'])
    peer = checked(prep['original_semantic_peer']); assert prep['entire_original_semantic_body_and_time'] == peer
    for row in ready['proof_sources']:
        source = row['source']; src = source['file']; digest = source['sha256']
        assert sha(src) == sha(row['source_snapshot']['file']) == digest
        original_row = next(x for x in prep['proof_sources'] if x['source'] == source)
        assert path(src).read_bytes() == path(original_row['original_source']['file']).read_bytes() == path(original_row['original_source_byte_copy']['file']).read_bytes()
        assert row['original_semantic_peer'] == prep['original_semantic_peer'] and original_row['original_semantic_review_time'] == peer['reviewed_at_utc']
        ds = declarations(path(src).read_text()); names = [x['name'] for x in ds if x['kind'] in ['theorem','lemma']]
        assert names == row['public_theorems'] == original_row['public_theorems'] == offer['proof_files'][src]['public_theorem_names']
        assert offer['proof_files'][src]['mapped_named_declarations'] == [x['name'] for x in ds]
        full_decl_names += [x['name'] for x in ds]; theorems += names
        assert candidate['proof_files'][src] == offer['proof_files'][src]['sha256'] == digest
        for index, pair in enumerate(row['actual_canonical_pair']):
            d = checked(pair['record']); zero(d)
            assert d['source'] == src and d['source_sha256_before'] == d['source_sha256_after'] == digest and d['source_unchanged'] is True
            commands = [d[k] for k in ['command','actual_command'] if k in d]
            wanted = ['lake','env','lean',src.removeprefix('verification/lean/')] if index == 0 else ['lake','build',src.removeprefix('verification/lean/').removesuffix('.lean').replace('/','.')]
            assert commands and all(c == wanted for c in commands) and d['actual_workdir'] == str(ROOT / 'verification/lean')
            logs = [d[k] for k in ['log','raw_log'] if k in d]; hashes = [d[k] for k in ['log_sha256','raw_log_sha256'] if k in d]
            assert logs and hashes and all(x == logs[0] for x in logs) and all(x == hashes[0] for x in hashes) and sha(logs[0]) == hashes[0]
            assert offer['proof_files'][src]['evidence_sha256'][pair['record']['file']] == pair['record']['sha256']
            assert offer['proof_files'][src]['evidence_sha256'][logs[0]] == hashes[0]
            paired.append({'record': pair['record'], 'entire_original_actual_record': d})
        source_rows.append(source)
assert len(source_rows) == 3 and len(theorems) == len(set(theorems)) == 23 and len(paired) == 6
assert paired == offer['new_actual_paired_records'] == binding['actual_paired_records']
for refs in [binding['cvar_component_semantic_peer'], binding['original_landscape15_whole_peer']]: checked(refs)
assert sha(binding['cvar_component_semantic_peer']['file']) == '8d0a85ce07e5c564e76847d5fc9fc96f6d2595d2691b50efcf2a1d9dcd4b7913'
assert sha(binding['original_landscape15_whole_peer']['file']) == 'ad3778c3f5ff5e3b93c04b6d29215f5c302b19c5fbdfb63b09e65ba18e4af66b'
selection = read(offer['base_selection']); assert sha(offer['base_selection']) == offer['base_selection_sha256'] and len(selection['proof_files']) == 1156
selected_names = set()
for n,row in selection['proof_files'].items(): assert sha(n) == row['sha256']; selected_names.update(d['name'] for d in declarations(path(n).read_text()))
assert not set(offer['proof_files']) & set(selection['proof_files'])
assert set(claim['lean_declarations']) <= selected_names | set(full_decl_names)
for n,h in binding['protected_current_inputs_sha256'].items(): assert sha(n) == h,n
current25binding = read('book/coverage/checks/root-owner25-reviewed-candidate-bindings-v2.json')
assets = current25binding['exact_current52_safelearning_assets_sha256']; assert len(assets) == 31
for n,h in assets.items(): assert sha(n) == h,n
inventory = read(offer['inventory'])
assert binding['exact_owned_exercise_records'] == [e for e in inventory['exercises'] if e['source'] in old['scope_pages']]
assert binding['exact_owned_material_records'] == [e for e in inventory['material_source_units'] if e['source'] in old['scope_pages']]
failed = offer['preserved_initial_builder_failure']; assert failed == binding['preserved_initial_builder_failure']
for r in failed: assert sha(r['file']) == r['sha256']
failure = read(failed[2]['file']); zero(failure,1); assert sha(failure['raw_log']) == failure['raw_log_sha256']
execution_name = 'book/coverage/checks/applied-future26/applied26-isolated-joint-density-candidate-actual-v2.json'
execution = read(execution_name); zero(execution)
assert execution['actual_command'] == ['python3', offer['candidate_builder']['file']]
assert execution['working_directory'] == str(ROOT) and execution['helper_sha256'] == offer['candidate_builder']['sha256']
assert sha(execution['raw_log']) == execution['raw_log_sha256']
out = Path('/tmp/applied26-canonical-and-whole371-candidate-independent-foundations-review-v1.json'); assert not out.exists()
report = {'status':'passed_independent_exact_canonical_history_and_whole371_candidate_mechanics_review','errors':[], 'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),
 'reviewer':'Independent Foundations agent; Applied authored canonical packet and isolated mapping', 'candidate_offer':ref(offer_name), 'candidate_ledger':ref(offer['mapped_ledger']), 'candidate_promotions':ref(offer['mapped_promotions']),
 'original_full_semantic_peer':binding['original_semantic_peer'],'original_review_time_unchanged':review['reviewed_at_utc'], 'original_semantic_body_and_every_hypothesis_reason_declaration_and_decision_unchanged':True,
 'exact_old_partial_row_and_four_component_bodies_preserved':True,'whole371_normalization_and_entire_candidate_inverse_passed':True,
 'exact_counts':offer['counts'],'genuine_canonical_sources':source_rows,'genuine_actual_pairs':paired,'actual_isolated_candidate_builder':ref(execution_name), 'original_builder_failure_preserved':failed,
 'source23_public_names_and_named_def_instance_closure_checked_separately':True,'canonical_original_alias_count':90,'selected25_sources_1156_exact':True,'current52_assets31_exact':True,'installed25_live_owners_preserved':True,
 'scope':'Narrow exact original canonical-source/history/actual-evidence bindings and isolated candidate mechanics only. No semantic redecision, fresh Lean execution, live installation, aggregate26, source change, whole156/1351 or fixed25 amendment.',
 'original_checker':ref(Path(__file__))}
with out.open('x') as f: json.dump(report,f,indent=2);f.write('\n')
print(json.dumps({'status':'passed','review':ref(out),'canonical_sources':3,'actual_pairs':6,'public_theorem_and_lemma_exports':23,'fresh_whole_material_units':1}))
