from pathlib import Path
from datetime import datetime,timezone
from collections import Counter
import copy,hashlib,json,re,sys
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased');D=Path('/tmp/foundations30-current79-provisional-candidate-v3');assert not D.exists()
PLAN=Path('/tmp/foundations30-owner30-approved-scope-plan-current65-originals-v1.json')
SUPPLY=R/'book/coverage/checks/future30-foundations/source66-qualified-supply-v1/foundations30-six-approved-unnumbered-qualifier-supply-v1.json'
CTX=Path('/tmp/root_tmp_lean_current79_historical_owner29_context_v1.json')
OWNER=R/'book/coverage/foundations.json';INV=R/'book/coverage/inventory.json';OLDINV=R/'book/coverage/inventory-after-correction65.json'
CONTRACT=R/'book/coverage/checks/future30-core/source66-79-contract-v3/source66-79-fourteen-step-application-contract-v3.json'
APP=R/'reports/full-coverage/source66-79-corrections-application-v3.json';NATIVE=R/'reports/full-coverage/source66-79-actual-application-execution-v1.json'
def path(n):
 p=Path(n);return p if p.is_absolute() else R/p
def sha(n):return hashlib.sha256(path(n).read_bytes()).hexdigest()
def ref(n):
 p=path(n);return {'file':p.relative_to(R).as_posix() if p.is_relative_to(R) else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
def read(n):return json.loads(path(n).read_bytes())
refs={}
def check(q):
 p=path(q['file']);assert p.is_file() and sha(p)==q['sha256'],str(p)
 if 'bytes' in q:assert p.stat().st_size==q['bytes']
 refs[str(p)]=q['sha256'];return read(p) if p.suffix=='.json' else p.read_bytes()
def data(x):return (json.dumps(x,indent=2)+'\n').encode()
def unitidentity(u):return {k:v for k,v in u.items() if k!='source_sha256'}
assert sha(PLAN)=='f1118a9d259b9f9a9acad63fb3142080d6b28b4bc621024e317510f8e3b463bb'
assert sha(SUPPLY)=='71e3b464aebcf47cad35151bd0226b334880916e06849578d7ba23333d6b613c'
assert sha(CTX)=='d06f4ef21178b787db693df28ca5ae01386728915e0596cba5fd17f000db0737'
assert sha(INV)=='9f2a37c42e8a54b81ea542ead730dbfa1d3f665be469c41e4eaa6a27703520de' and sha(OLDINV)=='5f68ee3c68c1da1275a0a2667fe43b42263b8fc31800a834371de5bfbed01b68'
assert sha(APP)=='6e3f8ac09f4622761959e71af89ab7ccc6ea7730453f871faffd537a25246df7' and sha(NATIVE)=='df708cab86daaefe894db0eb55ad7b2537361dd3f30031c17141613cf23e2e83'
ctx=read(CTX)
def guard():
 for fld in ['pins_sha256','held_current_source_sha256','owners_sha256']:
  for n,h in ctx[fld].items():assert sha(n)==h,n
 assert sha(OWNER)=='67889e85ad190d150ec888b803cfcc4d2c80dc48aa096d1969ddfbf90cda5f07'
 assert sha(INV)=='9f2a37c42e8a54b81ea542ead730dbfa1d3f665be469c41e4eaa6a27703520de'
 return {fld:copy.deepcopy(ctx[fld]) for fld in ['pins_sha256','held_current_source_sha256','owners_sha256']}
original1=[Path('/tmp/prepare-foundations30-current79-provisional-candidate-v1.py'),Path('/tmp/run-foundations30-current79-provisional-candidate-preparation-v1.py'),Path('/tmp/foundations30-current79-provisional-candidate-preparation-actual-v1.json'),Path('/tmp/foundations30-current79-provisional-candidate-preparation-actual-v1.log')]
for p in original1:check(ref(p))
failure1=read(original1[2]);assert failure1['actual_exit_code']==1 and failure1['protection_errors']==[]
original2=[Path('/tmp/prepare-foundations30-current79-provisional-candidate-v2.py'),Path('/tmp/run-foundations30-current79-provisional-candidate-preparation-v2.py'),Path('/tmp/foundations30-current79-provisional-candidate-preparation-actual-v2.json'),Path('/tmp/foundations30-current79-provisional-candidate-preparation-actual-v2.log')]
for p in original2:check(ref(p))
failure2=read(original2[2]);assert failure2['actual_exit_code']==1 and failure2['protection_errors']==[]
before=guard();started=datetime.now(timezone.utc).isoformat()
plan=check(ref(PLAN));supply=check(ref(SUPPLY));inv=check(ref(INV));oldinv=check(ref(OLDINV));old=check(ref(OWNER));contract=check(ref(CONTRACT));app=check(ref(APP));native=check(ref(NATIVE));check(ref(CTX))
assert native['status']=='passed' and type(native['actual_exit_code']) is int and native['actual_exit_code']==0 and native['helper_sha256_before']==native['helper_sha256_after'] and sha(native['log'])==native['log_sha256'];check(ref(native['log']))
assert old==check(plan['original_installed29_foundations_owner_immutable_existing29_ref'])
assert len(old['exercises'])==119 and all(r['status']=='complete_math' for r in old['exercises']) and old['counts']['material_claim_statuses']=={'not_a_formal_claim':532,'proved':1141,'pending':446}
assert (plan['new_distinct_source_count'],plan['genuine_passed_public_theorem_body_count'],plan['current65_whole_key_count'],plan['qualified_whole_key_count'])==(27,370,43,15)
assert [s['correction_id'] for s in contract['steps']]==list(range(66,80))
assert all(contract['final_source_sha256'][n]==sha(n) for n in contract['final_source_sha256'])
pages=set(old['scope_pages']);oldunits={u['key']:u for u in oldinv['material_source_units'] if u['source'] in pages};units={u['key']:u for u in inv['material_source_units'] if u['source'] in pages};assert len(oldunits)==len(units)==1756 and oldunits.keys()==units.keys()
changed=[k for k in oldunits if oldunits[k]['text_sha256']!=units[k]['text_sha256']]
expectedchanged=[k for s in contract['steps'][:6] for k in s['changed']['material_source_units']]
assert set(changed)==set(expectedchanged) and len(changed)==14
for k,u in oldunits.items():
 a={n:v for n,v in u.items() if n not in ['source_sha256','source_text','text_sha256']};b={n:v for n,v in units[k].items() if n not in ['source_sha256','source_text','text_sha256']};assert a==b
# Exact per-step fresh parsed records are already genuine Root contract artifacts, not reexecuted here.
for step in contract['steps'][:6]:
 si=check(step['inventory_after']);sm={u['key']:u for u in si['material_source_units']}
 for k in step['changed']['material_source_units']:assert unitidentity(sm[k])==unitidentity(units[k])
# Source79 association changes only current source identity/literal slots; histories remain untouched.
current=copy.deepcopy(old);identity=[]
for n in current['source_sha256']:current['source_sha256'][n]=inv['source_sha256'].get(n,sha(n));assert sha(n)==current['source_sha256'][n]
for table in ['exercises','material_claims','surrounding_prose_reviews']:
 for i,row in enumerate(current[table]):
  changes={};h=inv['source_sha256'][row['source']]
  if 'source_sha256' in row and row['source_sha256']!=h:changes['source_sha256']={'before':row['source_sha256'],'after':h};row['source_sha256']=h
  keys=row.get('source_unit_keys',[row.get('inventory_key')]);affected=set(keys)&set(changed)
  if affected:
   assert len(keys)==1;u=units[keys[0]]
   for fld,value in [('source_text',u['source_text']),('source_text_sha256',u['text_sha256'])]:
    if row[fld]!=value:changes[fld]={'before':row[fld],'after':value};row[fld]=value
  if changes:identity.append({'table':table,'index':i,'field_changes':changes})
rebased=copy.deepcopy(current)
proposals={k:s for s in supply['proposals'] for k in s['whole_unit_keys_for_later_corrected_mapping']};assert len(proposals)==15
sources={};families={};keyfamilies={};proofnames=set()
sys.path.insert(0,str(R/'book/coverage'));import lean_names;check(ref(R/'book/coverage/lean_names.py'))
for f in plan['approved_proof_sources']:
 source=check(f['proof_source']);body=source.decode();decs=lean_names.declarations(body);names=[x['name'] for x in decs if x['kind'] in ['theorem','lemma']]
 assert names==f['public_theorem_names'] and len(names)==f['public_theorem_count'] and not proofnames.intersection(names);proofnames.update(names)
 assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by|run_elab|ofReduceBool|sorryAx)\b',lean_names.without_comments(body))
 peer=check(f['full_independent_semantic_peer']);assert peer.get('errors',[])==[] and ('independent_full_review_pending' not in f or f['independent_full_review_pending'] is False)
 if 'independent_full_review_pending' not in f:
  assert f['family']=='symmetric_functional_calculus' and f['full_independent_semantic_peer']['sha256']=='738ee8941cc07d48b86e18749f974141fb097e1a95d5551f6097625fb6525891'
  ar=check(f['independent_actual_reader_execution']);assert ar['actual_exit_code']==0
 a=check(f['genuine_final_TMP_native']);check(f['genuine_final_raw_log']);check(f['genuine_final_source_snapshot'])
 assert type(a['actual_exit_code']) is int and a['actual_exit_code']==0 and a['protection_errors']==[] and a['source_sha256_before']==a['source_sha256_after']==f['proof_source']['sha256'] and a['source_unchanged'] is True
 assert f['genuine_final_original_times']=={k:a[k] for k in ['started_at_utc','finished_at_utc','elapsed_seconds']}
 es={q['file']:q['sha256'] for q in [f['proof_source'],f['full_independent_semantic_peer'],f['genuine_final_TMP_native'],f['genuine_final_raw_log'],f['genuine_final_source_snapshot'],plan['original_compiled_inventory10']]}
 dest=f['proposed_canonical_destination'];assert dest not in old['proof_files'] and dest not in sources
 sources[dest]={'sha256':f['proof_source']['sha256'],'theorem_count':len(names),'public_theorem_names':names,'mapped_named_declarations':names,'evidence_sha256':es,'original_exact_source':f['proof_source'],'original_genuine_TMP_final_native':f['genuine_final_TMP_native'],'original_genuine_TMP_source_snapshot':f['genuine_final_source_snapshot'],'original_genuine_TMP_raw_log':f['genuine_final_raw_log'],'original_genuine_times':f['genuine_final_original_times'],'original_complete_trial_histories_retained_by_inventory10_and_full_peer_refs':True,'independent_full_source_correspondence_peer':f['full_independent_semantic_peer'],'source_level_public_declarations':decs,'new_current79_canonical_standalone_and_named_pair_pending':True,'actual_pair':None,'evidence_scope':'Approved full source with original Source65 TMP native body/time preserved. Whole and component literal correspondence is explicitly distinct; new canonical pair, owner integration and selected aggregate remain pending.'}
 families[f['family']]={'plan':f,'peer':peer}
 for k in f['current_whole_keys_independently_approved']+f['requested_prospective_corrected_whole_keys']:assert k not in keyfamilies;keyfamilies[k]=f['family']
assert len(sources)==27 and len(proofnames)==370 and len(keyfamilies)==58
current['proof_files']=old['proof_files']+list(sources);current['proof_sha256']={**old['proof_sha256'],**{n:x['sha256'] for n,x in sources.items()}}
def decisions(peer):
 return [x for k in ['individual_decisions','individual_full_literal_decisions','individual_prospective_decisions','individual_whole_literal_decisions','individual_current_decisions'] for x in peer.get(k,[]) if isinstance(x,dict)]
def decision_for(peer,k):
 ds=[x for x in decisions(peer) if x.get('inventory_key',x.get('source_unit_key'))==k];return ds[0] if ds else None
def supports(d,f):
 for fld in ['new_lean_declarations','exact_support','public_support','public_theorem_names','lean_declarations']:
  ns=d.get(fld)
  if isinstance(ns,list) and ns and all(isinstance(n,str) for n in ns):
   assert set(ns).issubset(proofnames) or all(n.startswith('SafeLearning.') for n in ns);return ns
 return f['public_theorem_names']
replacements=[];whole_bindings=[]
for k,family in keyfamilies.items():
 f=families[family]['plan'];peer=families[family]['peer'];dec=decision_for(peer,k);u=units[k];qualification=None
 if k in plan['current65_whole_keys_independently_approved']:
  assert unitidentity(u)==unitidentity(oldunits[k]);assert dec is not None
  assert any(dec.get(n) is True for n in ['whole_literal_approved','current_whole_literal_approved','entire_current_literal_approved','entire_literal_approved'])
 else:
  q=proposals[k];check(q['proposal']);qp=check(q['full_wording_and_actual_isolated_both_ROOT_OUT29_parser_peer']);assert qp.get('errors',[])==[]
  for r in q['full_mathematical_scope_peers']+q['additional_full_prospective_literal_associations']:check(r)
  qualification={'original_individual_Source65_proposal':q['proposal'],'full_wording_and_independent_parser_peer':q['full_wording_and_actual_isolated_both_ROOT_OUT29_parser_peer'],'full_mathematical_scope_peers':q['full_mathematical_scope_peers'],'additional_full_prospective_literal_associations':q['additional_full_prospective_literal_associations'],'actual_Source66_to79_application':ref(APP),'actual_Source66_to79_native':ref(NATIVE),'current79_entire_literal':u,'individual_proposed_page_SHA_is_historical_and_distinct_from_cumulative79_identity':True,'whole_mapping_requires_independent_final_candidate_review':True}
 if family=='norm190':
  assert peer['prospective_corrected190_whole_semantic_approved'] is True and unitidentity(u)==unitidentity(peer['entire_prospective_corrected_literal']);dec={'inventory_key':k,'exact_support':f['public_theorem_names'],'full_clause_correspondence':peer['clause_correspondence']}
 assert dec is not None or family=='Rayleigh_quotient_and_printed_positive_example'
 ns=supports(dec or {},f)
 indices=[i for i,r in enumerate(rebased['material_claims']) if r['status']=='pending' and k in r['source_unit_keys']];assert indices
 binding={'inventory_key':k,'entire_current79_literal':u,'family':family,'original_full_semantic_peer':f['full_independent_semantic_peer'],'original_individual_decision_retained':dec,'qualification_application_association':qualification,'public_support':ns,'current79_whole_mapping_proposed_pending_final_independent_mapping_review':True};whole_bindings.append(binding)
 for i in indices:
  prior=copy.deepcopy(rebased['material_claims'][i]);row={'source_unit_keys':[k],'source':u['source'],'locator':u['locator'],'source_text':u['source_text'],'source_text_sha256':u['text_sha256'],'source_sha256':u['source_sha256'],'id':k+'::independently-reviewed30-whole-literal-'+str(i),'statement_in_prose':u['source_text'],'kind':'independently_reviewed_whole_material_unit','lean_declarations':ns,'status':'proved','hypotheses':'Exactly the domains, guards and hypotheses in the retained entire-literal independent semantic decision. Actual current79 qualifications are explicitly associated when applicable; no neighboring inference.','correspondence':dec.get('full_correspondence',dec.get('correspondence',dec.get('approved_scope','Entire literal correspondence is preserved in the exact full semantic peer and explicit clause decision.'))) if dec else 'Entire corrected positive example422 correspondence is supplied by the distinct full prospective association peer; original current422 gap/body/time stays historical.','remaining_gaps':[],'source_review':f['full_independent_semantic_peer'],'original_full_literal_decision_and_actual79_association':binding,'whole_literal_scope_independently_approved':True,'new_canonical_source':f['proposed_canonical_destination'],'new_canonical_standalone_and_named_pair_pending':True,'installed_owner_or_aggregate_coverage_claimed':False}
  current['material_claims'][i]=row;replacements.append({'index':i,'classification':'whole_math','original_row':copy.deepcopy(old['material_claims'][i]),'rebased_pending_row':prior,'new_row':copy.deepcopy(row)})
nf=check(plan['individual_nonformal_classification_peer'])
for d in nf['individual_full_literal_decisions']:
 k=d['source_unit_key'];u=units[k];assert k in plan['individual_nonformal_keys'] and d['classification']=='not_a_formal_claim' and d['approved'] is True and d['missing_clauses']==[] and unitidentity(u)==unitidentity(d['entire_literal'])
 indices=[i for i,r in enumerate(rebased['material_claims']) if r['status']=='pending' and k in r['source_unit_keys']];assert len(indices)==1;i=indices[0];prior=copy.deepcopy(rebased['material_claims'][i]);row=copy.deepcopy(prior)
 row.update(id=k+'::independently-reviewed30-nonformal-reference',statement_in_prose=u['source_text'],kind='individually_reviewed_nonformal_reference',status='not_a_formal_claim',lean_declarations=[],hypotheses='Exact editorial reference row only; linked mathematical/exercise obligations remain separate.',correspondence=d['reason'],remaining_gaps=[],source_review=plan['individual_nonformal_classification_peer'],mathematical_whole_approval_claimed=False)
 current['material_claims'][i]=row;replacements.append({'index':i,'classification':'nonformal_reference','original_row':copy.deepcopy(old['material_claims'][i]),'rebased_pending_row':prior,'new_row':copy.deepcopy(row)})
component_rows=[]
for family,k,field in [('induced','primer-linalg.html::node-323',None),('symmetric_Hermitian_spectral','primer-linalg.html::node-421',None),('determinant_log','primer-linalg.html::node-873','adjacent873_component_decision'),('sylvester','primer-linalg.html::node-879','adjacent879_component_decision')]:
 f=families[family]['plan'];peer=families[family]['peer'];dec=peer[field] if field else decision_for(peer,k);assert dec is not None and not any(dec.get(x) is True for x in ['whole_literal_approved','current_whole_literal_approved']);u=units[k];ns=supports(dec,f);assert any(r['status']=='pending' and k in r['source_unit_keys'] for r in current['material_claims'])
 row={'source_unit_keys':[k],'source':u['source'],'locator':u['locator'],'source_text':u['source_text'],'source_text_sha256':u['text_sha256'],'source_sha256':u['source_sha256'],'id':k+'::independently-reviewed30-components','statement_in_prose':dec.get('approved_scope',dec.get('correspondence','Exactly the separately reviewed component support in the original full peer.')),'kind':'independently_reviewed_mathematical_subclaim','lean_declarations':ns,'status':'proved','hypotheses':dec.get('hypotheses','Only exact corresponding declarations; full current literal remains pending.'),'correspondence':'Component only. Entire original pending row is retained; the original independent full-scope decision is bound without inferring whole coverage.','remaining_gaps':[],'source_review':f['full_independent_semantic_peer'],'original_component_decision':dec,'current_whole_literal_approved':False,'new_canonical_source':f['proposed_canonical_destination'],'new_canonical_standalone_and_named_pair_pending':True,'installed_owner_or_aggregate_coverage_claimed':False}
 current['material_claims'].append(row);component_rows.append(copy.deepcopy(row))
current['counts']=copy.deepcopy(old['counts']);current['counts']['material_claim_statuses']=dict(Counter(r['status'] for r in current['material_claims']))
physical_before=len({k for r in old['material_claims'] if r['status']=='pending' for k in r['source_unit_keys']});physical_after=len({k for r in current['material_claims'] if r['status']=='pending' for k in r['source_unit_keys']});assert (physical_before,physical_after)==(415,354)
assert len(whole_bindings)==58 and len(replacements)==66 and len(component_rows)==4 and len({r['index'] for r in replacements})==66
assert current['counts']['material_claim_statuses']=={'not_a_formal_claim':535,'proved':1208,'pending':380}
# Full dictionary and byte inverse retains every old review body/time, old proved component and119 exercises.
inverse=copy.deepcopy(current);inverse['material_claims']=inverse['material_claims'][:-4]
for r in replacements:inverse['material_claims'][r['index']]=copy.deepcopy(r['rebased_pending_row'])
for change in reversed(identity):
 row=inverse[change['table']][change['index']]
 for fld,v in change['field_changes'].items():assert row[fld]==v['after'];row[fld]=v['before']
for k in ['source_sha256','proof_files','proof_sha256','counts']:inverse[k]=copy.deepcopy(old[k])
assert inverse==old and data(inverse)==OWNER.read_bytes()
for i,row in enumerate(old['material_claims']):
 if row['status']=='proved':
  allowed={'source_sha256'}|({'source_text','source_text_sha256'} if set(row['source_unit_keys'])&set(changed) else set())
  assert {k:v for k,v in row.items() if k not in allowed}=={k:v for k,v in current['material_claims'][i].items() if k not in allowed}
assert len(current['exercises'])==119 and [{k:v for k,v in r.items() if k!='source_sha256'} for r in current['exercises']]==[{k:v for k,v in r.items() if k!='source_sha256'} for r in old['exercises']]
interface={'status':'prepared_current79_Foundation_owner30_exact_identity_and_66_row_inverse_pending_canonical_pairs_and_independent_mapping','errors':[],'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'original_entire_installed29_owner':ref(OWNER),'original_existing29_immutable_owner':plan['original_installed29_foundations_owner_immutable_existing29_ref'],'historical_Source65_inventory':ref(OLDINV),'actual_Source79_inventory':ref(INV),'source_identity_field_changes':identity,'source65_to79_changed_owned_literal_keys':changed,'all58_entire_math_literal_bindings':whole_bindings,'individual66_pending_row_replacements':replacements,'four_component_only_rows_appended':component_rows,'original_all119_exercises_and1141_proved_components_retained_except_explicit_current_source_identity_and_corrected_literal_slots':True,'all_original_metadata_native_histories_semantic_reviews_commands_body_times_unchanged':True,'exact_reverse_restores_entire_original29_owner_bytes':True,'inverse_protocol':'Remove four exact trailing component rows; restore each rebased_pending_row at recorded index; reverse source_identity_field_changes; restore original top source_sha256/proof_files/proof_sha256/counts; remove new current79_owner_identity/current30_material_mapping fields. The original owner bytes use json.dumps(indent=2)+newline ASCII escaping.','old_counts':old['counts'],'provisional_candidate_counts':current['counts'],'physical_pending_before':415,'physical_pending_after':354,'coverage_complete':False,'new_canonical_pairs_pending':True,'final_independent_mapping_peer_pending':True}
D.mkdir();ip=D/'foundations30-current79-provisional-exact-inverse-v3.json';ip.write_bytes(data(interface));ir=ref(ip)
current['current79_owner_identity']={'inventory':ref(INV),'original_historical_Source65_owner':plan['original_installed29_foundations_owner_immutable_existing29_ref'],'actual_Source66_to79_application':ref(APP),'actual_Source66_to79_native':ref(NATIVE),'actual79_TMP_guard_context':ref(CTX),'source_changed_owned_material_keys':changed,'old_semantic_body_commands_and_times_unchanged':True,'scope':'Current source identity and fourteen exact corrected Foundation literals only; historical source65 owner/kernel bodies remain preserved. No new aggregate79 audit inferred.'}
current['current30_material_mapping']={'exact_interface':ir,'approved_scope_plan':ref(PLAN),'original_inventory10':plan['original_compiled_inventory10'],'actual_Source79_inventory':ref(INV),'new_proof_files':list(sources),'new_public_theorem_bodies':370,'new_distinct_sources':27,'whole_math_material_units':58,'whole_math_pending_rows':63,'new_individual_nonformal_rows':3,'new_component_only_rows':4,'all_original119_exercises_and1141_proved_rows_retained_under_explicit_source_identity_rebase':True,'new_canonical_pairs_pending':True,'final_independent_mapping_review_pending':True,'installed_owner_or_aggregate_claimed':False,'redundant_Cayley6_and_Semicontinuity9_excluded_from_counts_install':True}
cp=D/'foundations30-current79-provisional-candidate-v3.json';cp.write_bytes(data(current));cr=ref(cp)
offer={'status':'prepared_current79_Foundation_owner30_provisional_27_source_370_body_candidate_pending_actual_pairs_and_full_mapping','errors':[],'original_preparation2_true_failure':{'refs':[ref(p) for p in original2],'reason':'The added Functional18 scope-plan row has an explicit completed independent_actual_reader_execution and full whole425 peer but no redundant independent_full_review_pending boolean. NEW3 checks the exact known Functional18 full peer and genuine completed reader instead of requiring that absent field. All source/proof/peer/body times unchanged.','actual_original_elapsed_seconds':failure2['elapsed_seconds']},'original_preparation1_true_failure':{'refs':[ref(p) for p in original1],'reason':'Top source_sha256 includes actual book/chapters mirror paths, whereas inventory source_sha256 lists SafeLearning input pages. NEW2 retains the actual mirror SHA for those existing names, using the same explicit fallback as earlier authentic Foundation identity rebasers; all Source79 inventoried pages remain exactly checked.','actual_original_elapsed_seconds':failure1['elapsed_seconds']},'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'candidate':cr,'mapped_ledger':str(cp),'mapped_ledger_sha256':cr['sha256'],'inventory':ref(INV),'inventory_sha256':sha(INV),'source_sha256':current['source_sha256'],'proof_files':sources,'new_proof_file_count':27,'new_theorem_or_lemma_count':370,'new_whole_material_unit_count':58,'new_whole_mathematical_pending_row_count':63,'new_nonformal_reference_row_count':3,'new_component_only_row_count':4,'new_whole_exercise_count':0,'exercise_counts':current['counts']['exercise_statuses'],'material_claim_counts':current['counts']['material_claim_statuses'],'physical_pending_unit_count':354,'exact_interface':ir,'original_installed29_ledger':plan['original_installed29_foundations_owner_immutable_existing29_ref'],'approved_scope_plan':ref(PLAN),'actual_Source66_to79_application':ref(APP),'actual_Source66_to79_native':ref(NATIVE),'actual79_context':ref(CTX),'all_new_actual_canonical_pairs_pending':True,'independent_final_candidate_mapping_peer_pending':True,'required_evidence_artifacts_sha256':refs,'original_history_refs_are_bounded_direct_not_recursive_copies':True,'old_snapshots_or_lake_trees_copied':False,'coverage_complete':False,'live_owner_canonical_selection_publication_mutated':False}
op=D/'foundations30-current79-provisional-offer-v3.json';op.write_bytes(data(offer));assert guard()==before
print(json.dumps({'candidate':cr,'offer':ref(op),'exact_interface':ir,'proof_sources_public_bodies':[27,370],'whole_math_units_rows':[58,63],'NF_rows':3,'component_only_rows':4,'counts':current['counts']['material_claim_statuses'],'physical_pending':354,'exact_inverse':True,'new_canonical_pairs_pending':True,'errors':[]}))
