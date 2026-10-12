from pathlib import Path
from datetime import datetime,timezone
from collections import Counter
import copy,hashlib,json,sys
R=Path('/home/oxrexkevin/SafetyBased');D=R/'book/coverage/checks/future28-foundations/current64-owner29-provisional-v3';assert not D.exists()
OWNER='book/coverage/foundations.json';INV='book/coverage/inventory-after-correction64.json';SCOPE='book/coverage/checks/future28-foundations/owner29-approved-eight-scope-plan-v2/foundations-owner29-approved-eight-math-units-six-source-scope-plan-v2.json';CTX='/tmp/root_tmp_lean_current64_owner28_context_v1.json'
def p(n):return Path(n) if Path(n).is_absolute() else R/n
def sha(n):return hashlib.sha256(p(n).read_bytes()).hexdigest()
def read(n):return json.loads(p(n).read_bytes())
def ref(n):return {'file':str(n),'sha256':sha(n)}
def check(r):assert p(r['file']).is_file() and sha(r['file'])==r['sha256'];return read(r['file']) if p(r['file']).suffix=='.json' else p(r['file']).read_bytes()
def data(v):return (json.dumps(v,indent=2)+'\n').encode()
c=read(CTX)
def guard():
 for field in ['pins_sha256','held_current_source_sha256','owners_sha256']:
  for n,h in c[field].items():assert sha(n)==h,n
 assert sha(OWNER)=='269b6f6053c4fd91fa9c4346b469e190a804f41a5edb0f9d5a74319fcadf5ddf'
 assert sha(INV)==sha('book/coverage/inventory.json') and len(read('book/coverage/material-corrections.json')['corrections'])==64
 assert sha(SCOPE)=='1827ef3534994d6f5d9a38e49b9ab8a0d8c531e5c7b1ede2dfe4bb7d080032be'
 return {'owner':ref(OWNER),'inventory':ref(INV),'corrections':ref('book/coverage/material-corrections.json'),'selection':ref('reports/full-coverage/checkpoint-28-selection.json'),'context':ref(CTX)}
started=datetime.now(timezone.utc).isoformat();before=guard();old=read(OWNER);inv=read(INV);scope=read(SCOPE);original=scope['immutable_owner28_source60_foundations'];assert check(original)==old
oldinv=check(scope['immutable_original_source60_inventory']);units={x['key']:x for x in inv['material_source_units']};oldunits={x['key']:x for x in oldinv['material_source_units']};ex={x['key']:x for x in inv['exercises']}
assert len(old['exercises'])==119 and all(x['status']=='complete_math' for x in old['exercises']);pages=set(old['scope_pages']);assert len(pages)==3
owned_old=[x for x in oldinv['material_source_units'] if x['source'] in pages];owned_new=[x for x in inv['material_source_units'] if x['source'] in pages];assert len(owned_old)==len(owned_new)==1756
changed_owned=[a['key'] for a,b in zip(owned_old,owned_new) if a['text_sha256']!=b['text_sha256']];assert changed_owned==['primer-basics.html::node-1029','primer-basics.html::node-1031','primer-basics.html::node-1142','primer-linalg.html::node-141','primer-linalg.html::node-171','primer-optimization.html::node-200','primer-optimization.html::node-202']
for a,b in zip(owned_old,owned_new):
 aa={k:v for k,v in a.items() if k not in ['source_sha256','source_text','text_sha256']};bb={k:v for k,v in b.items() if k not in ['source_sha256','source_text','text_sha256']};assert aa==bb
for x in old['exercises']:
 u=ex[x['inventory_key']];assert (x['source'],x['locator'],x['source_text'],x['source_text_sha256'])==(u['source'],u['locator'],u['source_text'],u['text_sha256'])
current=copy.deepcopy(old);identity=[]
for n in list(current['source_sha256']):
 h=inv['source_sha256'].get(n,sha(n));assert sha(n)==h;current['source_sha256'][n]=h
for table in ['exercises','material_claims','surrounding_prose_reviews']:
 for j,row in enumerate(current[table]):
  changes={};source=row['source'];h=inv['source_sha256'][source]
  if 'source_sha256' in row and row['source_sha256']!=h:changes['source_sha256']={'before':row['source_sha256'],'after':h};row['source_sha256']=h
  keys=row.get('source_unit_keys',[row.get('inventory_key')]);affected=set(keys)&set(changed_owned)
  if affected:
   assert len(keys)==1;u=units[keys[0]]
   for field,value in [('source_text',u['source_text']),('source_text_sha256',u['text_sha256'])]:
    if row[field]!=value:changes[field]={'before':row[field],'after':value};row[field]=value
  if changes:identity.append({'table':table,'index':j,'field_changes':changes})
rebased=copy.deepcopy(current);proof_rows={};groups={s['group']:s for s in scope['proof_source_scope']};support=[]
for s in scope['proof_source_scope']:
 n=s['suggested_new_canonical_destination'];h=s['durable_exact_source']['sha256'];check(s['durable_exact_source']);assert len(s['public_theorem_names'])==s['public_theorem_count']
 if p(n).exists():assert sha(n)==h
 peer=check(s['independent_full_source_correspondence_peer']);assert peer['errors']==[]
 history=s['original_genuine_trial_chain'];assert history[-1]['actual_exit_code']==0
 for trial in history:
  a=check(trial['actual']);check(trial['raw_log']);check(trial['source_snapshot']);assert a['actual_exit_code']==trial['actual_exit_code'] and a['started_at_utc']==trial['started_at_utc'] and a['finished_at_utc']==trial['finished_at_utc']
 es_refs=[s['durable_exact_source'],s['independent_full_source_correspondence_peer']]
 es_refs += [r for t in history for r in [t['actual'],t['raw_log'],t['source_snapshot']]]
 es={r['file']:r['sha256'] for r in es_refs}
 proof_rows[n]={'sha256':h,'theorem_count':s['public_theorem_count'],'public_theorem_names':s['public_theorem_names'],'mapped_named_declarations':s['public_theorem_names'],'evidence_sha256':es,'original_exact_source':s['durable_exact_source'],'original_genuine_tmp_trial_chain':history,'independent_full_source_correspondence_peer':s['independent_full_source_correspondence_peer'],'scope':s['scope'],'new_current64_or_later_canonical_standalone_and_named_pair_pending':True,'actual_pair':None,'evidence_scope':'Exact independently reviewed whole mathematics or explicitly narrower source-correction support. Historical genuine TMP kernels retain original Source60/owner context. No new canonical pair or installed owner claim.'}
 if s['scope'] in ['countermodel_components_only','components_only']:
  support.append({'proof_group':s['group'],'canonical_source_pending':n,'exact_source':s['durable_exact_source'],'full_component_peer':s['independent_full_source_correspondence_peer'],'public_theorem_names':s['public_theorem_names'],'physical_literal_keys':s['physical_literal_keys'],'whole_literal_approval':False,'scope':'Actual counterexamples and sufficient timing-coverage implication support only the independently reviewed source qualifiers; every unclosed whole literal remains pending.'})
current['proof_files']=old['proof_files']+list(proof_rows);current['proof_sha256']={**old['proof_sha256'],**{n:v['sha256'] for n,v in proof_rows.items()}};assert len(proof_rows)==6 and sum(v['theorem_count'] for v in proof_rows.values())==53
replacements=[]
for m in scope['material_scope']:
 key=m['inventory_key'];u=units[key];assert u['text_sha256']==m['expected_literal_text_sha256'] and u['source_sha256']==m['expected_post_source64_source_sha256']
 indices=[j for j,r in enumerate(rebased['material_claims']) if r['status']=='pending' and key in r['source_unit_keys']];assert len(indices)==1;j=indices[0];prior=copy.deepcopy(rebased['material_claims'][j]);s=groups[m['proof_group']]
 row={'source_unit_keys':[key],'source':u['source'],'locator':u['locator'],'source_text':u['source_text'],'source_text_sha256':u['text_sha256'],'source_sha256':u['source_sha256'],'id':key+'::independently-reviewed29-whole-literal','statement_in_prose':u['source_text'],'kind':'independently_reviewed_whole_material_unit','lean_declarations':m['direct_new_named_declarations'],'status':'proved','hypotheses':'Finite real coordinate spaces, real symmetric positive definite weights when used, and source symmetry/linearity/strict positivity for a generic inner form. The p-norm scopes require p>=1; an attained coordinate maximum requires a nonempty finite index. Euclidean vector norms follow page notation. Unit141 has the actual Source64 qualifiers umax>=0 and j!=y.','correspondence':m['full_clause_correspondence_reason'],'remaining_gaps':[],'source_review':m['whole_peer'],'additional_corrected_literal_association_peer':m['additional_corrected_literal_association_peer'],'whole_literal_scope_independently_approved':True,'new_canonical_source':s['suggested_new_canonical_destination'],'new_canonical_standalone_and_named_pair_pending':True,'installed_owner_or_aggregate_coverage_claimed':False}
 current['material_claims'][j]=row;replacements.append({'original_index':j,'original_source60_owner_row':copy.deepcopy(old['material_claims'][j]),'rebased_pending_row':prior,'new_row':row,'classification':'whole_math'})
bib=check(scope['separate_nonformal_editorial_scope']['individual_full_literal_primary_reference_peer']);assert bib['errors']==[]
for d in bib['individual_full_literal_decisions']:
 key=d['source_unit_key'];assert d['approved_exact_nonformal_bibliographic_classification'] is True and d['missing_clauses']==[];u=units[key];indices=[j for j,r in enumerate(rebased['material_claims']) if r['status']=='pending' and key in r['source_unit_keys']];assert len(indices)==1;j=indices[0];prior=copy.deepcopy(rebased['material_claims'][j]);row=copy.deepcopy(prior)
 row.update(id=key+'::independently-reviewed29-bibliographic-reference',statement_in_prose=u['source_text'],kind='individually_reviewed_nonformal_bibliographic_reference',status='not_a_formal_claim',lean_declarations=[],hypotheses='Bibliographic facts and curricular recommendations; no external mathematical theorem is promoted.',correspondence=d['independent_factual_and_scope_reason'],remaining_gaps=[],source_review=scope['separate_nonformal_editorial_scope']['individual_full_literal_primary_reference_peer'],primary_url=d['primary_url'],mathematical_whole_approval_claimed=False)
 current['material_claims'][j]=row;replacements.append({'original_index':j,'original_source60_owner_row':copy.deepcopy(old['material_claims'][j]),'rebased_pending_row':prior,'new_row':row,'classification':'nonformal_reference'})
assert len(replacements)==16 and len({r['original_index'] for r in replacements})==16
current['counts']=copy.deepcopy(old['counts']);current['counts']['material_claim_statuses']=dict(Counter(x['status'] for x in current['material_claims']));assert current['counts']['material_claim_statuses']=={'not_a_formal_claim':532,'proved':1141,'pending':446}
physical_before=len({k for x in old['material_claims'] if x['status']=='pending' for k in x['source_unit_keys']});physical_after=len({k for x in current['material_claims'] if x['status']=='pending' for k in x['source_unit_keys']});assert (physical_before,physical_after)==(431,415)
base=D.relative_to(R).as_posix();candidate=base+'/foundations29-current64-provisional-candidate-v3.json';interface=base+'/foundations29-current64-exact-identity-and-sixteen-row-inverse-v3.json';offer=base+'/foundations29-current64-provisional-offer-draft-v3.json'
current['current64_owner_identity']={'inventory':ref(INV),'actual_source61_to64_application':c['actual_source61_to64_application'],'actual_application_native':c['actual_application_native'],'original_installed28_owner':original,'source_changed_owned_material_keys':changed_owned,'all119_owned_exercise_literals_and_proof_claims_unchanged':True,'old_semantic_body_commands_and_times_unchanged':True,'scope':'Only current source identities and seven precisely corrected pending literal bodies are rebased. Historical metadata and semantic/compiler receipts retain their original bodies and times.'}
current['current29_material_mapping']={'exact_interface':{'file':interface},'approved_scope_plan':ref(SCOPE),'whole_math_material_units':8,'new_nonformal_reference_rows':8,'new_proof_files':list(proof_rows),'new_public_theorem_bodies':53,'whole_math_public_theorem_bodies':46,'correction_support_public_theorem_bodies':7,'original16_pending_rows_and_all_identity_changes_retained_in_interface':True,'all119_exercises_and1133_prior_proved_claims_retained_under_explicit_source_identity_rebase':True,'new_canonical_pairs_pending':True,'final_independent_mapping_review_pending':True,'installed_owner_or_aggregate_claimed':False}
current['current29_source_qualification_support']=support
invcheck=copy.deepcopy(current)
for field in ['current64_owner_identity','current29_material_mapping','current29_source_qualification_support']:invcheck.pop(field)
invcheck['source_sha256']=copy.deepcopy(old['source_sha256']);invcheck['proof_files']=copy.deepcopy(old['proof_files']);invcheck['proof_sha256']=copy.deepcopy(old['proof_sha256']);invcheck['counts']=copy.deepcopy(old['counts'])
for r in replacements:invcheck['material_claims'][r['original_index']]=copy.deepcopy(r['rebased_pending_row'])
for change in reversed(identity):
 row=invcheck[change['table']][change['index']]
 for field,v in change['field_changes'].items():assert row[field]==v['after'];row[field]=v['before']
assert invcheck==old
for j,x in enumerate(old['material_claims']):
 if x['status']=='proved':assert {k:v for k,v in x.items() if k!='source_sha256'}=={k:v for k,v in current['material_claims'][j].items() if k!='source_sha256'}
assert len(current['material_claims'])==len(old['material_claims']) and current['counts']['exercise_statuses']==old['counts']['exercise_statuses'] and current['exercises']==old['exercises']
iface={'status':'prepared_exact_current64_foundations29_source_identity_and16_row_interface_only','errors':[],'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'original_entire_installed28_owner':original,'current_inventory':ref(INV),'approved_scope_plan':ref(SCOPE),'source_identity_field_changes':identity,'sixteen_individual_row_replacements':replacements,'all_exact_original_owned_exercises_retained_except_source_identity':119,'all1133_prior_proved_claims_retained_except_source_identity':True,'all_original_proof_metadata_histories_reviews_commands_body_times_unchanged':True,'exact_reverse_restores_entire_original_owner':True,'source64_owned_changed_literal_keys':changed_owned,'old_counts':old['counts'],'provisional_candidate_counts':current['counts'],'physical_pending_before':physical_before,'physical_pending_after':physical_after,'new_canonical_pair_execution_pending':True,'independent_final_mapping_review_pending':True,'coverage_complete':False}
ifacebytes=data(iface);ir={'file':interface,'sha256':hashlib.sha256(ifacebytes).hexdigest()};current['current29_material_mapping']['exact_interface']=ir;candidatebytes=data(current);cr={'file':candidate,'sha256':hashlib.sha256(candidatebytes).hexdigest()}
record={'status':'prepared_current64_foundations29_provisional_candidate_pending_canonical_pairs_and_final_mapping','errors':[],'started_at_utc':started,'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'candidate':cr,'mapped_ledger':candidate,'mapped_ledger_sha256':cr['sha256'],'inventory':ref(INV),'inventory_sha256':sha(INV),'source_sha256':current['source_sha256'],'proof_files':proof_rows,'new_proof_file_count':6,'new_theorem_or_lemma_count':53,'new_whole_material_unit_count':8,'new_nonformal_reference_row_count':8,'new_whole_exercise_count':0,'exercise_counts':current['counts']['exercise_statuses'],'material_claim_counts':current['counts']['material_claim_statuses'],'physical_pending_unit_count':physical_after,'exact_interface':ir,'original_installed28_ledger':original,'approved_scope_plan':ref(SCOPE),'additional_frozen_inputs':scope['required_evidence_artifacts_sha256'],'current64_original_context':ref(CTX),'all_new_actual_canonical_pairs_pending':True,'independent_final_candidate_mapping_peer_pending':True,'source65_or_later_inventory_identity_not_inferred':True,'coverage_complete':False,'live_owner_canonical_selection_publication_mutated':False}
after=guard();assert before==after
planned={candidate:candidatebytes,interface:ifacebytes,offer:data(record)}
for n,b in planned.items():assert not p(n).exists()
for n,b in planned.items():p(n).parent.mkdir(parents=True,exist_ok=True);p(n).write_bytes(b)
assert guard()==before
print(json.dumps({'status':record['status'],'candidate':cr,'exact_interface':ir,'draft_offer':ref(offer),'counts':record['material_claim_counts'],'physical_pending_before_after':[physical_before,physical_after],'proof_sources_public_bodies':[6,53],'exact_inverse':True}))
