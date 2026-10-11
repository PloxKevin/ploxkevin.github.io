from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json,re,sys
R=Path('/home/oxrexkevin/SafetyBased');sys.dont_write_bytecode=True;sys.path.insert(0,str(R/'book/coverage'))
from lean_names import declarations
H=lambda p:hashlib.sha256((Path(p) if Path(p).is_absolute() else R/p).read_bytes()).hexdigest()
J=lambda p:json.loads((Path(p) if Path(p).is_absolute() else R/p).read_text())
OUT=Path('/tmp/module24-source52-candidate-independent-applied-confirmation-v1.json');assert not OUT.exists()
O='book/coverage/checks/modules-future24/source52/modules-audit24-candidate-source52-additions-draft-v1.json'
assert H(O)=='f63887128bb965d81e532bcd1bed5b47ea201edd4691fe70ef859b7796fc6a35';o=J(O)
def checked(r):
 assert H(r['file'])==r['sha256'],r
 return J(r['file']) if r['file'].endswith('.json') else (R/r['file']).read_text()
oldoffer=checked(o['original_source51_reviewed_offer']);old=J(oldoffer['module_ledger']);new=J(o['module_ledger'])
assert H(oldoffer['module_ledger'])==oldoffer['module_ledger_sha256']=='27a36bb3e324ce88a2122625b580af4bfde662b9ac50bce78e95850b2bbf18d2'
assert H(o['module_ledger'])==o['module_ledger_sha256']=='1d4395c5b7cb9dc18217b0c4236a04868f67a2445d0ffed18f3a77215d3b2c90'
assert o['entire_original_source51_reviewed_offer_body_and_time']==oldoffer
prior=checked(oldoffer['independent_final_candidate_mapping_peer']);assert prior['errors']==[]
assert prior==o['original_source51_final_mapping_fields']['entire_original_final_candidate_mechanics_body_and_time']
side=checked(o['source52_unchanged_literal_identity']);binding=checked(o['source52_fresh_partial_literal_binding']);guard=checked(o['candidate_binding_integrity'])
assert not guard['live_owner_mutated'] and not guard['whole_source52_promotion']
invold=J('book/coverage/inventory-after-correction51.json');invnew=J(o['current_inventory'])
assert H(o['current_inventory'])==H('book/coverage/inventory.json')==o['current_inventory_sha256']=='38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
assert o['source_sha256']==new['source_sha256']
for n,d in o['source_sha256'].items():assert H(n)==d==invnew['source_sha256'][n]
assert H('SafeLearning/nn-in-the-loop.html')=='1a39cab6587a6fe91dca670facc5e58e7c85cb6c0a2c065f43763656d5b73041'
current={k:{r['key']:r for r in invnew[k]} for k in ['exercises','material_source_units']}
past={k:{r['key']:r for r in invold[k]} for k in ['exercises','material_source_units']}
scope=set(old['scope_pages']);actual_changed={}
canon=lambda d:hashlib.sha256(json.dumps(d,sort_keys=True,separators=(',',':'),ensure_ascii=False).encode()).hexdigest()
for kind,count,expected in [('exercises',216,{'nn-in-the-loop.html::exercise-20'}),('material_source_units',4975,{'nn-in-the-loop.html::node-1260','nn-in-the-loop.html::node-1262'})]:
 assert past[kind].keys()==current[kind].keys()
 changed={k for k in past[kind] if {n:x for n,x in past[kind][k].items() if n!='source_sha256'}!={n:x for n,x in current[kind][k].items() if n!='source_sha256'}}
 assert changed==expected;actual_changed[kind]=sorted(changed)
 unchanged={k for k,r in current[kind].items() if r['source'] in scope and k not in changed};assert len(unchanged)==count
 rows=side['unchanged_owned_records_except_page_source_digest'][kind];assert len(rows)==count and {r['key'] for r in rows}==unchanged
 for row in rows:
  a,b=past[kind][row['key']],current[kind][row['key']]
  assert row['entire_original51_inventory_record_sha256']==canon(a) and row['entire_current52_inventory_record_sha256']==canon(b)
  assert row['text_sha256']==a['text_sha256']==b['text_sha256']
  assert row['source_sha256_before']==a['source_sha256'] and row['source_sha256_after']==b['source_sha256']
assert side['changed_literal_keys']==actual_changed
apply=checked(binding['actual_root_source52_apply']);post=checked(binding['actual_root_source52_postwrite'])
assert apply['actual_exit_code']==post['actual_exit_code']==0 and post['inventory_after_sha256']==o['current_inventory_sha256']
assert H(apply['log'])==apply['log_sha256']
proposal=checked(binding['approved_proposal']);proposalpeer=checked(binding['independent_full_proposal_semantic_primary_parser_peer'])
assert proposalpeer['proposal_text_approved'] and not proposalpeer['whole_exercise_or_material_unit_approved'] and proposalpeer['errors']==[]
before=checked(proposal['source_bytes_before_snapshot']);after=before
for replacement in proposal['replacements']:
 assert after.count(replacement['before'])==replacement['count']==1
 after=after.replace(replacement['before'],replacement['after'],replacement['count'])
assert after==(R/'SafeLearning/nn-in-the-loop.html').read_text()
assert len(proposal['replacements'])==2
key='nn-in-the-loop.html::exercise-20'
assert binding['entire_original51_changed_exercise_record']==past['exercises'][key]
assert binding['entire_actual52_changed_exercise_record']==current['exercises'][key]
assert not binding['whole_exercise_approved'] and not binding['whole_changed_material_units_approved'] and not binding['temporal_sources_selected']
for r in binding['changed_material_records']:
 k=r['entire_actual52_inventory_record']['key'];assert r['entire_original51_inventory_record']==past['material_source_units'][k]
 assert r['entire_actual52_inventory_record']==current['material_source_units'][k]
reviews=[checked(r) for r in o['original_full_or_precise_source_reviews']]
assert reviews==binding['entire_original_source51_reviews_bodies_and_times']
for r,p in zip(o['original_full_or_precise_source_reviews'],reviews):assert p['reviewed_at_utc']==r['original_review_time'] and p['errors']==[]
olde={e['inventory_key']:e for e in old['exercises']};newe={e['inventory_key']:e for e in new['exercises']}
assert len(newe)==217 and olde.keys()==newe.keys()
for k,e in newe.items():
 assert e['source_sha256']==current['exercises'][k]['source_sha256'] and e['source_text_sha256']==current['exercises'][k]['text_sha256']
 assert e['claims']==olde[k]['claims'] and e['status']==olde[k]['status']
assert newe[key]['claims'][-12:]==binding['entire_original_twelve_proved_component_atoms']==olde[key]['claims'][-12:]
assert newe[key]['status']=='partial' and newe[key]['remaining_whole_source_gaps24']==binding['active_remaining_scope']
assert binding['active_remaining_scope'] and len(binding['active_remaining_scope'])==3
nm={r['id']:r for r in new['material_claims']};om={r['id']:r for r in old['material_claims']};assert nm.keys()==om.keys() and len(nm)==5195
for k,c in nm.items():
 assert c['status']==om[k]['status'] and c['lean_declarations']==om[k]['lean_declarations'] and c['hypotheses']==om[k]['hypotheses']
 for field in ['independent_source_review','entire_original_component_body','canonical_source_binding_peer']:
  if field in om[k]:assert c[field]==om[k][field]
pending=['nn-in-the-loop.html::node-'+str(n)+'::claim-review' for n in [1254,1260,1262]]
for k in pending:
 unit=k.split('::claim-review')[0];assert nm[k]['status']=='pending' and nm[k]['remaining_gaps']
 assert nm[k]['statement_in_prose']==current['material_source_units'][unit]['source_text']
assert nm['nn-in-the-loop.html::node-1258::claim-review']['status']=='proved'
assert new['proof_files']==old['proof_files'] and new['declarations']==old['declarations'] and new['counts']==old['counts']
assert o['proof_files']==oldoffer['proof_files'] and o['original_full_or_precise_source_reviews']==oldoffer['original_full_or_precise_source_reviews']
reverse=copy.deepcopy(new)
for k,e in zip(old['exercises'],reverse['exercises']):
 for field in ['source52_fresh_partial_literal_binding','source52_unchanged_literal_identity']:e.pop(field,None)
 for field in ['source_sha256','source_text_sha256','remaining_whole_source_gaps24']:
  if field in k:e[field]=copy.deepcopy(k[field])
for k,c in zip(old['material_claims'],reverse['material_claims']):
 for field in ['source52_fresh_partial_literal_binding','source52_unchanged_literal_identity']:c.pop(field,None)
 for field in ['statement_in_prose','remaining_gaps']:c[field]=copy.deepcopy(k[field])
for field in ['source_sha256','chapter_fragment_sha256','current_inventory','current_inventory_sha256']:reverse[field]=copy.deepcopy(old[field])
reverse.pop('inventory_identity_rebase52');assert reverse==old
a=checked(o['actual_builder']);checked(o['actual_builder_raw_log'])
assert a['actual_exit_code']==0 and a['actual_command']==['python3',o['module_builder'],o['current_inventory_sha256']] and a['actual_workdir']==str(R)
assert H(o['module_builder'])==o['module_builder_sha256']=='60a78a980a0d670874695709cad826e66af06109af21137a1338b6ddad56bed0'
assert a['actual_helper_sha256_before']==a['actual_helper_sha256_after']==o['module_builder_sha256']
assert H(a['raw_log'])==a['raw_log_sha256']==o['actual_builder_raw_log']['sha256']
for n,d in o['required_evidence_artifacts_sha256'].items():assert H(n)==d,n
selected=checked(o['baseline23_selection']);assert selected['proof_file_count']==1131
for n,r in selected['proof_files'].items():assert H(n)==r['sha256']
for n,r in old['proof_files'].items():assert H(n)==r['sha256']
names=[]
for n,p in o['proof_files'].items():
 assert H(n)==p['sha256'];actualnames=[d['name'] for d in declarations((R/n).read_text()) if d['kind'] in ['theorem','lemma']]
 assert actualnames==p['declarations'];names+=actualnames
 for pair in p['actual_paired_records']:
  rec=checked(pair['actual_record']);checked(pair['raw_log']);checked(pair['source_snapshot'])
  assert rec==pair['entire_original_actual_record_body_and_time'] and rec['actual_exit_code']==0
  assert rec['source']==n and rec['source_sha256_before']==rec['source_sha256_after']==p['sha256']==pair['source_snapshot']['sha256']
assert len(names)==16
for n,d in guard['protected_live_owner_sha256'].items():assert H(n)==d
assert H(O)=='f63887128bb965d81e532bcd1bed5b47ea201edd4691fe70ef859b7796fc6a35'
report={'status':'passed_independent_current52_module24_static_tanh_fresh_literal_binding_and_exact_isolated_candidate_mechanics',
 'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'/root/applied_next','errors':[],
 'offer':{'file':O,'sha256':H(O)},'candidate':{'file':o['module_ledger'],'sha256':H(o['module_ledger'])},
 'identity_sidecar':o['source52_unchanged_literal_identity'],'fresh_partial_literal_binding':o['source52_fresh_partial_literal_binding'],
 'entire_original_current51_candidate_mechanics_body_and_time':prior,
 'original_source_reviews_and_times':o['original_full_or_precise_source_reviews'],'actual_source52_apply':binding['actual_root_source52_apply'],
 'actual_source52_postwrite':binding['actual_root_source52_postwrite'],'exact_inverse_restores_entire_current51_candidate':True,
 'counts':{'unchanged_exercise_texts':216,'unchanged_material_texts':4975,'changed_exercise_texts':1,'changed_material_texts':2,'original_static_component_groups':12,'new_sources':3,'new_public_exports':16,'retained_actual_paired_records':6,'all_old_selected23_sources':1131,'all_original_candidate_material_bodies':5195,'original_candidate_proof_rows':478},
 'remaining_whole_gaps':binding['active_remaining_scope'],'whole_exercise_or_changed_units_approved':False,
 'fresh_literal_correspondence':'All current answer(b) exact symbolic QC, approximation signs and qualified invalid-premise claim match the retained actual counterexample/rounding components. Current answer(c) preserves the actual static shift/sector/full-block/bias-free components and expressly states the additional temporal/shared-channel assumptions; its full temporal, general doubly-hyperdominant and local-bound/method clauses remain pending. Only the earlier unchanged answer(a)1258 remains whole approved.',
 'checker':{'file':str(Path(__file__)),'sha256':H(Path(__file__))},'coverage_complete':False,
 'scope':'Fresh reading of complete corrected source52 exercise20/answers and exact metadata correspondence to preserved independent static component reviews. No whole temporal theorem, new Lean execution, live installation/global24, aggregate or publication claim. All old bodies/times and genuine failures remain unchanged.'}
with OUT.open('x') as f:f.write(json.dumps(report,indent=2)+'\n')
print(str(OUT),H(OUT))
