"""Isolated Source52 literal binding; execute only after authoritative Root0.

This is metadata/literal scope preparation, not a new whole mathematical review.
Original source51 candidate, twelve components, proofs and review dates stay exact.
"""
from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json,sys
R=Path(__file__).resolve().parents[2];B='book/coverage/checks/modules-future24/source52'
O='book/coverage/checks/modules-future24/source51'
OLD_INV='book/coverage/inventory-after-correction51.json'
NEW_INV='book/coverage/inventory-after-correction52.json'
OLD_CAND=O+'/modules24-candidate-source51-v1.json'
OLD_OFFER=O+'/modules-audit24-candidate-source51-additions-v1-reviewed.json'
H=lambda n:hashlib.sha256((R/n).read_bytes()).hexdigest()
J=lambda n:json.loads((R/n).read_text())
ref=lambda n:{'file':n,'sha256':H(n)}
def atomsha(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':'),ensure_ascii=False).encode()).hexdigest()
def put(n,d):
 p=R/n;assert not p.exists(),n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
def main():
 assert len(sys.argv)==2 and len(sys.argv[1])==64,'Pass the authoritative actual immutable inventory52 digest.'
 new_sha=sys.argv[1]
 assert H(OLD_INV)=='d746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41'
 assert H(NEW_INV)==new_sha==H('book/coverage/inventory.json')
 assert H(OLD_CAND)=='27a36bb3e324ce88a2122625b580af4bfde662b9ac50bce78e95850b2bbf18d2'
 assert H(OLD_OFFER)=='95ee6d8d90056a5d0b02c6586b6a613a2637a8228cb1047608660907371b4022'
 apply='reports/full-coverage/source52-apply-execution-v1.json';post='book/coverage/checks/root-source-batch52/postwrite-source-integrity-v1.json'
 a=J(apply);p=J(post)
 assert a['actual_exit_code']==p['actual_exit_code']==0
 assert p['inventory_after']==NEW_INV and p['inventory_after_sha256']==new_sha
 assert H(a['log'])==a['log_sha256']
 old=J(OLD_CAND);offer=J(OLD_OFFER);before=J(OLD_INV);after=J(NEW_INV)
 source='SafeLearning/nn-in-the-loop.html';new_source='1a39cab6587a6fe91dca670facc5e58e7c85cb6c0a2c065f43763656d5b73041'
 assert H(source)==new_source==after['source_sha256'][source]
 catalog='book/coverage/checks/future24-nn-source52/approved-source52-proposal-original-byte-alias-catalog-v1.json'
 assert H(catalog)=='6a08c185cc062e257934cc1f560e2ec862d91c85b8b9b3a8b166f6137b730d5f'
 cat=J(catalog);proposal=J(cat['original_proposal']['file']);peer=J(cat['original_independent_semantic_primary_and_parser_peer']['file'])
 assert proposal['proposed_source_sha256_after']==new_source and peer['proposal_text_approved']
 assert not peer['whole_exercise_or_material_unit_approved'] and peer['errors']==[]
 scope=set(old['scope_pages']);unchanged={};changed={};oldrows={};newrows={}
 for kind in ['exercises','material_source_units']:
  ob={x['key']:x for x in before[kind]};na={x['key']:x for x in after[kind]};assert ob.keys()==na.keys()
  expected={'nn-in-the-loop.html::exercise-20'} if kind=='exercises' else {'nn-in-the-loop.html::node-1260','nn-in-the-loop.html::node-1262'}
  changed[kind]=[];unchanged[kind]=[];oldrows[kind]=ob;newrows[kind]=na
  for k,v in ob.items():
   assert v['source']==na[k]['source']
   normalized_before={n:x for n,x in v.items() if n!='source_sha256'}
   normalized_after={n:x for n,x in na[k].items() if n!='source_sha256'}
   if normalized_before!=normalized_after:changed[kind].append(k)
   if v['source'] in scope and k not in expected:
    assert normalized_before==normalized_after,k
    unchanged[kind].append({'key':k,'entire_original51_inventory_record_sha256':atomsha(v),
     'entire_current52_inventory_record_sha256':atomsha(na[k]),'text_sha256':na[k]['text_sha256'],
     'source_sha256_before':v['source_sha256'],'source_sha256_after':na[k]['source_sha256'],
     'only_permitted_record_delta':'source_sha256'})
  assert set(changed[kind])==expected,(kind,changed[kind])
 assert len(unchanged['exercises'])==216 and len(unchanged['material_source_units'])==4975
 for n,h in old['source_sha256'].items():assert H(n)==after['source_sha256'][n] and (n==source or H(n)==h)
 selection=J('reports/full-coverage/checkpoint-23-selection.json');assert selection['proof_file_count']==1131
 for n,r in selection['proof_files'].items():assert H(n)==r['sha256']
 for n,r in old['proof_files'].items():assert H(n)==r['sha256']
 for n,h in offer['required_evidence_artifacts_sha256'].items():assert H(n)==h
 protected={n:H(n) for n in ['book/coverage/core.json','book/coverage/foundations.json','book/coverage/applied.json','book/coverage/modules.json','book/coverage/applied-promotions.json']}
 assert protected['book/coverage/modules.json']=='448b83324829b136ef9745977e10f397086b6872f6d3141854d96504dfd53367'
 prepared=datetime.now(timezone.utc).isoformat();side=B+'/unchanged-owned-literal-identity-v1.json'
 put(side,{'status':'exact_source51_to52_unchanged_module_literal_identity_with_three_changed_text_records_excluded',
  'prepared_at_utc':prepared,'historical_inventory':ref(OLD_INV),'current_inventory':ref(NEW_INV),
  'original_reviewed_candidate':ref(OLD_CAND),'original_reviewed_offer':ref(OLD_OFFER),
  'unchanged_owned_records_except_page_source_digest':unchanged,'changed_literal_keys':changed,
  'actual_root_source52_apply':ref(apply),'actual_root_source52_postwrite':ref(post),
  'scope':'216 unchanged exercise texts/4975 unchanged material texts are checked individually; source page digest updates are explicit. Changed exercise20/1260/1262 require the separate current52 partial literal binding.'})
 bind=B+'/tanh24-current52-fresh-partial-literal-binding-v1.json'
 groups=old['reviewed_work_integration24_tanh_candidate']
 original_reviews=[J(x['file']) for x in groups['original_source_reviews']]
 original_atoms=next(e for e in old['exercises'] if e['inventory_key']=='nn-in-the-loop.html::exercise-20')['claims'][-12:]
 put(bind,{'status':'fresh_actual_source52_complete_literal_read_with_original_twelve_static_components_and_whole_pending_scope_retained',
  'bound_at_utc':prepared,'reviewer':'/root/modules_resume','current_inventory':ref(NEW_INV),
  'actual_source':ref(source),'actual_root_source52_apply':ref(apply),'actual_root_source52_postwrite':ref(post),
  'approved_proposal':cat['original_proposal'],'independent_full_proposal_semantic_primary_parser_peer':cat['original_independent_semantic_primary_and_parser_peer'],
  'entire_original_source51_reviews_bodies_and_times':original_reviews,'original_reviewed_source51_candidate':ref(OLD_CAND),
  'original_reviewed_source51_offer':ref(OLD_OFFER),'entire_original_twelve_proved_component_atoms':original_atoms,
  'entire_original51_changed_exercise_record':oldrows['exercises']['nn-in-the-loop.html::exercise-20'],
  'entire_actual52_changed_exercise_record':newrows['exercises']['nn-in-the-loop.html::exercise-20'],
  'changed_material_records':[{'entire_original51_inventory_record':oldrows['material_source_units'][k],
   'entire_actual52_inventory_record':newrows['material_source_units'][k]} for k in changed['material_source_units']],
  'twelve_groups_hypotheses_reasons_declarations_statuses_and_review_times_unchanged':True,
  'whole_exercise_approved':False,'whole_changed_material_units_approved':False,'temporal_sources_selected':False,
  'active_remaining_scope':['No fresh independent whole-unit approval of corrected answer(b) or answer(c) is inferred from the approved wording proposal.',
   'General doubly hyperdominant repeated-function and common-local-interval/common-bound correspondence remain outside this static pack.',
   'Admissible diagonal temporal Zames–Falb finite-horizon/channel-invariance and method attribution scope remain outside this static pack.'],
  'scope':'Full new corrected text is checked against the exact approved two substitutions and current literal records. The six corrected decimal equalities and narrowed invalid-premise wording are resolved text corrections; original source51 gaps remain historical. This records only unchanged precise component correspondence, not whole corrected-unit promotion or new mathematical proof.'})
 out=copy.deepcopy(old);ident=ref(side);bindingref=ref(bind);key='nn-in-the-loop.html::exercise-20'
 for e in out['exercises']:
  k=e['inventory_key'];current=newrows['exercises'][k]
  e['source_sha256']=current['source_sha256']
  if k==key:
   e['source_text_sha256']=current['text_sha256'];e['source52_fresh_partial_literal_binding']=bindingref
   e['remaining_whole_source_gaps24']=copy.deepcopy(J(bind)['active_remaining_scope'])
  else:e['source52_unchanged_literal_identity']=ident
 for c in out['material_claims']:
  if c['id'] in {k+'::claim-review' for k in ['nn-in-the-loop.html::node-'+str(n) for n in [1254,1260,1262]]}:
   unit=c['id'].split('::claim-review')[0];c['statement_in_prose']=newrows['material_source_units'][unit]['source_text']
   c['source52_fresh_partial_literal_binding']=bindingref
   c['remaining_gaps']=copy.deepcopy(J(bind)['active_remaining_scope']) if not unit.endswith('1260') else [J(bind)['active_remaining_scope'][0]]
   assert c['status']=='pending'
  elif c['id'].startswith(key+'::material-source51-reviewed24-component-'):
   c['source52_fresh_partial_literal_binding']=bindingref
  else:c['source52_unchanged_literal_identity']=ident
 out['source_sha256'][source]=new_source
 out['chapter_fragment_sha256']={n:H(n) for n in old['chapter_fragment_sha256']}
 out['current_inventory']=NEW_INV;out['current_inventory_sha256']=new_sha
 out['inventory_identity_rebase52']={'prepared_at_utc':prepared,'identity_sidecar':ident,
  'fresh_partial_literal_binding':bindingref,'original_source51_candidate':ref(OLD_CAND),
  'original_source51_reviewed_offer':ref(OLD_OFFER),'whole_or_component_mathematical_decisions_and_original_times_unchanged':True}
 assert out['proof_files']==old['proof_files'] and out['declarations']==old['declarations'] and out['counts']==old['counts']
 # Normalize only the permitted current metadata and literal text/gap fields.
 reverse=copy.deepcopy(out)
 for before_e,after_e in zip(old['exercises'],reverse['exercises']):
  for k in ['source52_fresh_partial_literal_binding','source52_unchanged_literal_identity']:after_e.pop(k,None)
  for k in ['source_sha256','source_text_sha256','remaining_whole_source_gaps24']:
   if k in before_e:after_e[k]=copy.deepcopy(before_e[k])
 for before_c,after_c in zip(old['material_claims'],reverse['material_claims']):
  for k in ['source52_fresh_partial_literal_binding','source52_unchanged_literal_identity']:after_c.pop(k,None)
  for k in ['statement_in_prose','remaining_gaps']:after_c[k]=copy.deepcopy(before_c[k])
 for k in ['source_sha256','chapter_fragment_sha256','current_inventory','current_inventory_sha256']:reverse[k]=copy.deepcopy(old[k])
 reverse.pop('inventory_identity_rebase52');assert reverse==old
 candidate=B+'/modules24-candidate-source52-v1.json';put(candidate,out)
 guard=B+'/modules24-source52-candidate-integrity-v1.json';put(guard,{'status':'passed_exact_isolated_source52_literal_and_identity_candidate_with_source51_semantics_preserved',
  'candidate':ref(candidate),'historical_source51_candidate':ref(OLD_CAND),'historical_source51_offer':ref(OLD_OFFER),
  'unchanged_literal_sidecar':ident,'fresh_partial_literal_binding':bindingref,'current_inventory':ref(NEW_INV),
  'counts':{'unchanged_owned_exercise_texts':216,'unchanged_owned_material_texts':4975,'current_twelve_component_groups':12,
   'proof_rows':len(out['proof_files']),'distinct_selected_new_public_exports':16},
  'exact_reverse_recovers_entire_original_source51_candidate':True,'all_proof_compiler_and_original_review_times_unchanged':True,
  'protected_live_owner_sha256':protected,'live_owner_mutated':False,'whole_source52_promotion':False})
 for n,h in protected.items():assert H(n)==h
 print(json.dumps({'candidate':ref(candidate),'identity':ident,'fresh_partial_binding':bindingref,'integrity':ref(guard)}))
if __name__=='__main__':main()
