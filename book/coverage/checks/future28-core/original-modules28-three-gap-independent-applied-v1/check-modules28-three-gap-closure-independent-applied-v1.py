from pathlib import Path
from datetime import datetime, timezone
import copy, hashlib, json, re

R=Path('/home/oxrexkevin/SafetyBased')
B=R/'book/coverage/checks/modules-future28/current60-pair-bound-v1'
C=B/'modules28-current60-three-stale-gap-repair-candidate-v2.json'
O=B/'modules28-current60-three-stale-gap-repair-offer-draft-v4.json'
A=B/'modules28-current60-three-stale-gap-completion-associations-v1.json'
OLD=B/'modules28-current60-five-source-pair-bound-candidate-v1.json'
OLD_O=B/'modules28-current60-five-source-final-offer-v2.json'
OUT=Path('/tmp/modules28-three-gap-closure-independent-applied-findings-v1.json')
PINS={C:'1c91d42f7a720cbb486d7ca57778012681875d450b2e1779cd5be47c10aaa4e9',O:'1a9f9de4e5bd876a1606b31c66dc7d2a0e9b0b17eebf209a28a53929266dc868',A:'3eb55077d73f421c1f0ddbcecf361d4fec5fc5356919da497cc929041f094622',OLD:'2f1dd93a7f3d80a93954029d847bf286431d2ef919600828e32ee8eda7e2d715',OLD_O:'8803f86a907dd6ef06bda0eceea50ede1be43110053a9abeee02fdee104408a7'}
def H(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def J(p):return json.loads(Path(p).read_bytes())
def enc(d):return (json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode()
def CH(d):return hashlib.sha256(json.dumps(d,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def ref(p):return {'file':Path(p).relative_to(R).as_posix(),'sha256':H(p)}
def rooted(n):
    p=Path(n);assert not p.is_absolute() and '..'not in p.parts and p.as_posix()==n
    p=R/p;assert p.is_file() and not p.is_symlink() and p.resolve().is_relative_to(R)
    return p
def checked(r):
    assert isinstance(r,dict)and isinstance(r.get('file'),str)and re.fullmatch('[0-9a-f]{64}',r['sha256'])
    p=rooted(r['file']);assert H(p)==r['sha256']
    if 'bytes'in r:assert p.stat().st_size==r['bytes']
    return p
def exits(d,value=0):
    xs=[d[k]for k in ('exit_code','actual_exit_code','actual_runner_exit_code')if k in d]
    assert xs and all(type(x)is int and x==value for x in xs)
assert not OUT.exists()
for p,h in PINS.items():assert H(p)==h
old=J(OLD);candidate=J(C);o=J(O);old_o=J(OLD_O);a=J(A)
expected=copy.deepcopy(old)
indices=[(58,4),(58,5),(191,3)]
ids=['lipsdp.html#book-m12-b1::proved-component-1','lipsdp.html#book-m12-b1::proved-component-2','verification.html::exercise-15::proved-component-1']
for (i,j),cid in zip(indices,ids):
    assert old['exercises'][i]['claims'][j]['id']==cid
    assert old['exercises'][i]['claims'][j]['status']=='proved'and len(old['exercises'][i]['claims'][j]['remaining_gaps'])==1
    expected['exercises'][i]['claims'][j]['remaining_gaps']=[]
assert enc(old)==OLD.read_bytes() and enc(expected)==C.read_bytes()
inverse=copy.deepcopy(candidate)
for i,j in indices:inverse['exercises'][i]['claims'][j]['remaining_gaps']=copy.deepcopy(old['exercises'][i]['claims'][j]['remaining_gaps'])
assert enc(inverse)==OLD.read_bytes()
assert candidate==expected and candidate['counts']==old['counts']
assert candidate['proof_files']==old['proof_files']and candidate['declarations']==old['declarations']and candidate['material_claims']==old['material_claims']
assert candidate['source_sha256']==old['source_sha256']
for e in candidate['exercises']:
    if e['status']=='complete_math':assert not any(c.get('remaining_gaps')for c in e['claims'])
assert o['status']=='prepared_current60_modules28_three_stale_gap_repair_offer_pending_supplemental_independent_peer'and o['errors']==[]
assert o['candidate']==ref(C)and o['original_reviewed_three_gap_candidate']==ref(OLD)
assert o['original_reviewed_offer_before_three_gap_repair']==ref(OLD_O)and o['three_stale_gap_completion_associations']==ref(A)
assert o['whole976_approved']is False and o['coverage_complete']is False and o['supplemental_three_gap_independent_peer']is None
changed={'status','candidate','required_evidence_artifacts_sha256','original_closed_byte_aliases'}
assert {k for k in old_o if old_o[k]!=o[k]}==changed
added={'three_gap_author_execution_scope','actual_three_gap_candidate_preparation','original_three_gap_preparation_offer','actual_three_gap_candidate_preparation_reader','supplemental_three_gap_independent_peer','original_reviewed_offer_before_three_gap_repair','three_stale_gap_completion_associations','actual_three_gap_candidate_preparation_original_byte_catalog','original_reviewed_three_gap_candidate'}
assert set(o)-set(old_o)==added
for k in ('required_evidence_artifacts_sha256','original_closed_byte_aliases'):
    assert all(o[k].get(n)==v for n,v in old_o[k].items())
    assert len(o[k])-len(old_o[k])==(15 if k=='required_evidence_artifacts_sha256'else 5)
assert len(o['required_evidence_artifacts_sha256'])==990 and len(o['original_closed_byte_aliases'])==680
for n,h in o['required_evidence_artifacts_sha256'].items():assert H(rooted(n))==h
for n,r in o['original_closed_byte_aliases'].items():checked(r)
prior=J(checked(o['final_independent_candidate_mapping_peer']))
assert H(checked(o['final_independent_candidate_mapping_peer']))=='551b46799ca996cf2f136c8a0f6cf2b17e56adaccad6dd2ffa107a85eb7c45e6'
assert prior['errors']==[]and prior['candidate']==ref(OLD)
inventory=J(checked(a['current60_inventory']));inv={r['key']:r for r in inventory['exercises']}
assert H(R/'book/coverage/inventory.json')==a['current60_inventory']['sha256']=='6290f87b8be03fd9818dcdee4663c4f37fd159118c16e1dbeefea82a2958747a'
assert len(a['associations'])==3 and a['new_whole_scope_or_promotion']is False
decisions=[]
for x,(i,j),cid in zip(a['associations'],indices,ids):
    e=old['exercises'][i];c=e['claims'][j]
    assert x['exercise_key']==e['inventory_key']and x['claim_index']==j and x['claim_id']==cid
    assert x['original_entire_claim']==c and x['original_claim_canonical_json_sha256']==CH(c)
    assert x['exact_field_changed']=='remaining_gaps'and x['before']==c['remaining_gaps']and x['after']==[]
    assert x['current60_entire_literal']==inv[e['inventory_key']]
    assert e['source_text_sha256']==inv[e['inventory_key']]['text_sha256']and H(R/e['source'])==e['source_sha256']
    assert x['discharged']is True and x['remaining_missing_clauses']==[]and x['old_claim_declarations_hypotheses_correspondence_or_status_changed']is False
    for supporting in x['supporting_existing_claims']:
        sc=next(y for y in e['claims']if y['id']==supporting['claim_id'])
        assert supporting['claim_canonical_json_sha256']==CH(sc)and supporting['lean_declarations']==sc['lean_declarations']and sc['status']=='proved'
    source=checked(x['actual_current60_canonical_source']);text=source.read_text()
    namespace=re.findall(r'^namespace\s+(\S+)',text,re.M)[0]
    names=[namespace+'.'+v for v in re.findall(r'^theorem\s+(\S+)',text,re.M)]
    assert set(x['actual_canonical_declarations'])<=set(names)
    p=J(checked(x['original_unchanged_full_source_peer']));assert p['errors']==[]and p['source']['sha256']==H(source)
    if i==58:
        assert p['prospective_source59_whole_exercise']['whole_exercise_approved_under_proposed_literal']is True
        assert p['prospective_source59_whole_exercise']['entire_proposed_inventory_record']==inv[e['inventory_key']]
    else:
        original=next(y for y in p['whole_exercise_records']if y['inventory_key']==e['inventory_key'])
        assert original['whole_exercise_approved']is True
        assert original['entire_inventory_record']['source_text']==inv[e['inventory_key']]['source_text']
    assert [v['kind']for v in x['actual_canonical_pair']]==['standalone','named']
    for row in x['actual_canonical_pair']:
        exits(row);n=J(checked(row['actual_record']));exits(n);assert n['status']=='passed'
        assert n['source']==str(source.relative_to(R))and n['source_sha256_before']==n['source_sha256_after']==H(source)
        assert row['source']==ref(source)and H(checked(row['source_snapshot']))==H(source)
        assert row['raw_log']=={'file':n['log'],'sha256':n['log_sha256']};checked(row['raw_log'])
    if x['selected_network_source']is not None:
        net=checked(x['selected_network_source']);sel=J(R/'reports/full-coverage/checkpoint-27-selection.json')
        assert H(net)==sel['proof_files'][str(net.relative_to(R))]['sha256']=='4e77816cb2218b77076647dea388687fbf6b166ebf0f69f1894b8bb45e44be14'
        nt=net.read_text();assert all('theorem '+n.rsplit('.',1)[1]in nt for n in x['selected_network_declarations'])
    decisions.append({'claim_id':cid,'original_gap':c['remaining_gaps'],'approved_discharge':True,'missing_clauses':[],'explicit_full_association':x['completion_correspondence'],'canonical_source':x['actual_current60_canonical_source'],'original_full_semantic_peer':x['original_unchanged_full_source_peer']})
native=J(checked(o['actual_three_gap_candidate_preparation']));exits(native)
assert native['status']=='passed'and native['protection_errors']==[]and native['canonical_owner_source_selection_compiler_or_publication_written']is False
assert native['helper_sha256_before']==native['helper_sha256_after']
for n,h in {**native['helper_sha256_before'],native['log']:native['log_sha256']}.items():
    r=o['original_closed_byte_aliases'][n];assert r['sha256']==h;checked(r)
fails=a['genuine_root_preflight_and_integrity_failures_preserved'];assert len(fails)==5
for r in fails:checked(r)
exits(J(checked(fails[0])),1)
diagnostic=J(checked(fails[2]));assert diagnostic['integrity_status']=='failed'and len(diagnostic['errors'])==3
result={'status':'passed','errors':[],'checked_at_utc':datetime.now(timezone.utc).isoformat(),'candidate':ref(C),'offer':ref(O),'old_candidate':ref(OLD),'original_full_pair_bound_candidate_peer':o['final_independent_candidate_mapping_peer'],'exact_forward_and_byte_inverse':True,'changed_fields_only':[['exercises',i,'claims',j,'remaining_gaps']for i,j in indices],'all_old_declarations_hypotheses_correspondence_status_times_counts_and_math_unchanged':True,'component_gap_associations':decisions,'verified_closure_count':990,'verified_alias_count':680,'canonical_mathematical_sources_unchanged':5,'new_public_names_unchanged':153,'actual_author_preparation':o['actual_three_gap_candidate_preparation'],'preserved_genuine_prewrite_failures':fails,'all_remaining_completed_exercise_gap_lists_empty':True,'whole976_approved':False,'additional_whole_scope_or_proof_promotion':False,'production_installer_or_compiler_executed':False}
OUT.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'status':'passed','candidate':ref(C),'offer':ref(O),'exact_three_field_inverse':True,'full_association_decisions':3,'closure_count':990,'alias_count':680}))
