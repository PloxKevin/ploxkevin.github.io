from pathlib import Path
from datetime import datetime, timezone
import copy, hashlib, json, re

ROOT=Path('/home/oxrexkevin/SafetyBased')
BASE='book/coverage/checks/future28-foundations/current60-owner28-v1'
OWNER='book/coverage/foundations.json'
OWNER_SHA='b3de5e813f882355cd90e46d27adc4ce56351ddd51d9038a1b8c79511b365b55'
INV='book/coverage/inventory-after-correction60.json'
INV_SHA='6290f87b8be03fd9818dcdee4663c4f37fd159118c16e1dbeefea82a2958747a'
READY='book/coverage/checks/future28-core/current60-canonical-pairs-v1/actual-current60-canonical-paired-readiness28-v1.json'
READY_SHA='209f306bc9c9b70b51a4eca063f453d546353bd9860ac3a96c6a3e4e037cc453'
OUTER='reports/full-coverage/current60-canonical-pairs28-execution-v1.json'
SCOPE='book/coverage/checks/future28-foundations/original-foundations-current60-approved21-scope-plan28-v1/1e58d5cce1dcd200015a67e241cab118849dc2de218e2ac3272446898df74b86/foundations-owner28-approved21-scope-plan-v2.json'
SCOPE_SHA='1e58d5cce1dcd200015a67e241cab118849dc2de218e2ac3272446898df74b86'
def path(n):
 p=Path(n);p=p if p.is_absolute() else ROOT/p
 assert p.is_relative_to(ROOT) or p.is_relative_to(Path('/tmp'))
 return p
def sha(n):return hashlib.sha256(path(n).read_bytes()).hexdigest()
def read(n):return json.loads(path(n).read_bytes())
def ref(n):
 p=path(n);return {'file':str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p),'sha256':sha(n)}
def checked(r):
 assert isinstance(r,dict) and type(r['file']) is str and type(r['sha256']) is str
 assert sha(r['file'])==r['sha256'],r['file'];return path(r['file'])
def zero(d):
 ks=[k for k in ['exit_code','actual_exit_code','actual_runner_exit_code'] if k in d]
 assert ks and all(type(d[k]) is int and d[k]==0 for k in ks),d
def actual(d,command,cwd):
 zero(d);assert d.get('status','passed')=='passed'
 ks=[k for k in ['command','actual_command'] if k in d];assert ks and all(d[k]==command for k in ks)
 ks=[k for k in ['cwd','working_directory','actual_workdir'] if k in d];assert ks and all(d[k]==cwd for k in ks)
def data(d):return (json.dumps(d,indent=2)+'\n').encode()
def main():
 started=datetime.now(timezone.utc).isoformat()
 assert sha(OWNER)==OWNER_SHA and sha(INV)==sha('book/coverage/inventory.json')==INV_SHA
 assert sha(READY)==READY_SHA and sha(SCOPE)==SCOPE_SHA
 ready,scope,old,inv=map(read,[READY,SCOPE,OWNER,INV])
 assert ready['errors']==[] and ready['source_count']==10 and ready['public_theorem_count']==235 and ready['actual_compiler_command_count']==20
 assert ready['coverage_complete'] is False and ready['selection_or_aggregate_or_publication_claimed'] is False
 protected=copy.deepcopy(ready['protected_inputs_sha256'])
 def guard():
  for n,h in protected.items():assert sha(n)==h,n
  assert sha(OWNER)==OWNER_SHA and sha(INV)==sha('book/coverage/inventory.json')==INV_SHA and sha(READY)==READY_SHA and sha(SCOPE)==SCOPE_SHA
 guard()
 outer=read(OUTER)
 actual(outer,['python3','book/coverage/checks/run_root28_current60_canonical_pairs_v2.py','--plan','/tmp/root28-current60-canonical-pair-plan-v1.json','--plan-sha256','64fe57b1296bf5d016eaf3da375a382454ea8c310c23c3421220000f0565533b','--apply'],str(ROOT))
 assert outer['helper_sha256_before']==outer['helper_sha256_after']=={'book/coverage/checks/run_root28_current60_canonical_pairs_v2.py':'69a8eab0c5710ea143dde3c72ecf08c5c6811fa87536cec688c3fe2ea7afbe83'}
 assert sha(outer['log'])==outer['log_sha256']=='6e91e0b5fde820e9dd17935837f832acd245f542e185fdc2ad1bea908bc055e4'
 assert outer['selection_sha256']==sha('reports/full-coverage/checkpoint-27-selection.json')=='ff2cf797d5171fbd9d7edb94683e779cdb442e476dde6f2ccc76470d81186bcd'
 oldinv=read('book/coverage/inventory-after-correction55.json');pages=set(old['scope_pages']);assert len(pages)==3
 for field,count in [('exercises',119),('material_source_units',1756)]:
  a=[u for u in oldinv[field] if u['source'] in pages];b=[u for u in inv[field] if u['source'] in pages]
  assert a==b and len(a)==count
 assert len(old['exercises'])==119 and all(r['status']=='complete_math' for r in old['exercises'])
 for n,h in old['source_sha256'].items():assert sha(n)==h,n
 for n,h in old['proof_sha256'].items():assert sha(n)==h,n
 assert set(old['proof_files'])==set(old['proof_sha256']) and len(old['proof_files'])==250
 units={u['key']:u for u in inv['material_source_units']};keys={r['inventory_key'] for r in scope['material_scope']}
 assert len(keys)==21 and len(scope['proof_source_scope'])==6
 sources={s['canonical_source']:s for s in ready['sources']}
 pairs={(p['source']['file'],p['kind']):p for p in ready['actual_paired_records']}
 assert len(sources)==10 and len(pairs)==20
 aliases=ready['original_closed_byte_aliases'];evidence={READY:READY_SHA,OUTER:sha(OUTER),outer['log']:sha(outer['log']),SCOPE:SCOPE_SHA,INV:INV_SHA,'book/coverage/material-corrections.json':sha('book/coverage/material-corrections.json')}
 def historical(r):
  checked(r);a=aliases[r['file']];checked(a);assert a['sha256']==r['sha256'];return copy.deepcopy(a)
 proof_rows={};allnames=set();group_rows={}
 for s in scope['proof_source_scope']:
  n=s['proposed_root_canonical_destination'];r=sources[n];h=s['original_tmp_proof']['sha256'];assert sha(n)==h==r['original_tmp_source']['sha256']
  assert r['public_theorem_count']==s['public_theorem_count'] and r['public_declarations']==s['public_theorem_names']
  names=[];namespace=None
  for line in path(n).read_text().splitlines():
   if line.startswith('namespace '):namespace=line.split()[1]
   if line.startswith('theorem '):names.append(namespace+'.'+line.split()[1])
  assert names==s['public_theorem_names'] and not(allnames&set(names));allnames.update(names)
  assert not re.search(r'\b(sorry|admit|axiom)\b',path(n).read_text())
  es={};actual_pair={}
  for kind in ['standalone','named']:
   p=pairs[(n,kind)];assert p['actual_exit_code']==0 and type(p['actual_exit_code']) is int
   assert p['source']=={'file':n,'sha256':h};native=read(checked(p['actual_record']))
   command=['lake','env','lean',str(Path(n).relative_to('verification/lean'))] if kind=='standalone' else ['lake','build','.'.join(Path(n).relative_to('verification/lean').with_suffix('').parts)]
   actual(native,command,str(ROOT/'verification/lean'))
   assert native['source']==n and native['source_sha256_before']==native['source_sha256_after']==h and native['source_unchanged'] is True
   assert native['log']==p['raw_log']['file'] and native['log_sha256']==p['raw_log']['sha256']
   for k in ['actual_record','raw_log','source_snapshot']:
    checked(p[k]);es[p[k]['file']]=p[k]['sha256']
   assert p['source_snapshot']['sha256']==h
   actual_pair[kind]=copy.deepcopy(p)
  peer=historical(s['whole_peer']);trial=historical(s['original_tmp_trial']);raw=historical(s['original_raw_log']);snapshot=historical(s['original_source_snapshot'])
  for a in [peer,trial,raw,snapshot]:es[a['file']]=a['sha256']
  assert read(peer['file'])['reviewed_at_utc']==s['original_peer_reviewed_at_utc']
  actual_pair['outer_execution']=ref(OUTER);actual_pair['readiness']=ref(READY)
  mapped=sorted(set(d for x in scope['material_scope'] if x['proof_group']==s['id'] for d in x['new_source_declarations']))
  assert set(mapped)==set(names)
  proof_rows[n]={'sha256':h,'evidence_sha256':es,'theorem_count':len(names),'public_theorem_names':names,'mapped_named_declarations':mapped,'actual_pair':actual_pair,'original_whole_source_peer':peer,'original_peer_reviewed_at_utc':s['original_peer_reviewed_at_utc'],'evidence_scope':'Actual current60 canonical standalone and named builds; original full literal semantic decision and historical TMP execution retain their original bodies and times. Aggregate28 and installed owner coverage remain separate.'}
  evidence.update(es);group_rows[s['id']]=(n,peer)
 assert len(proof_rows)==6 and len(allnames)==99
 removed=[{'original_index':j,'claim':copy.deepcopy(c)} for j,c in enumerate(old['material_claims']) if c['status']=='pending' and keys.intersection(c['source_unit_keys'])]
 assert len(removed)==21 and {r['claim']['source_unit_keys'][0] for r in removed}==keys
 assert all(len(r['claim']['source_unit_keys'])==1 for r in removed)
 original_rows=[{'original_index':j,'claim':copy.deepcopy(c)} for j,c in enumerate(old['material_claims']) if keys.intersection(c['source_unit_keys'])]
 assert len(original_rows)==31
 new=[]
 for m in scope['material_scope']:
  k=m['inventory_key'];u=units[k];n,peer=group_rows[m['proof_group']]
  assert u['text_sha256']==m['expected_current60_text_sha256'] and u['source_sha256']==m['expected_current60_source_sha256']
  assert m['whole_literal_scope_independently_approved'] is True and m['missing_clauses']==[]
  assert set(m['new_source_declarations'])<=allnames
  for d,r in m['selected_reused_declaration_source_refs'].items():
   checked(r);assert r['file'] in old['proof_files'];evidence[r['file']]=r['sha256']
  new.append({'source_unit_keys':[k],'source':u['source'],'locator':u['locator'],'source_text':u['source_text'],'source_text_sha256':u['text_sha256'],'source_sha256':u['source_sha256'],'id':k+'::independently-reviewed28-whole-literal','statement_in_prose':u['source_text'],'kind':'independently_reviewed_whole_material_unit','lean_declarations':m['lean_declarations'],'status':'proved','hypotheses':m['hypotheses'],'correspondence':m['correspondence'],'remaining_gaps':[],'source_review':dict(peer,reviewed_at_utc=m['original_peer_reviewed_at_utc'],scope='Original entire literal full-source semantic approval, exact Source55 body/time; entire current60 literal record unchanged. Actual current60 canonical compiler pair is separate.'),'actual_current60_canonical_pair':proof_rows[n]['actual_pair'],'new_source_declarations':m['new_source_declarations'],'selected_reused_declarations':m['selected_reused_declarations'],'whole_literal_scope_independently_approved':True})
 orig=BASE+'/original-installed27-foundations-source55.json';interface=BASE+'/foundations28-current60-exact21-interface-and-inverse-v1.json';candidate=BASE+'/foundations28-current60-candidate-v1.json';integrity=BASE+'/foundations28-current60-candidate-integrity-v1.json';offer=BASE+'/foundations28-current60-offer-draft-v1.json'
 planned={orig:path(OWNER).read_bytes()};original_ref={'file':orig,'sha256':OWNER_SHA}
 current=copy.deepcopy(old);current['material_claims']=[c for j,c in enumerate(old['material_claims']) if j not in {x['original_index'] for x in removed}]+new
 current['proof_files']=old['proof_files']+list(proof_rows)
 current['proof_sha256']=dict(old['proof_sha256'],**{n:r['sha256'] for n,r in proof_rows.items()})
 from collections import Counter
 current['counts']=copy.deepcopy(old['counts']);current['counts']['material_claim_statuses']=dict(Counter(c['status'] for c in current['material_claims']))
 assert current['counts']['material_claim_statuses']=={'not_a_formal_claim':524,'proved':1133,'pending':462}
 before_physical=len({k for c in old['material_claims'] if c['status']=='pending' for k in c['source_unit_keys']});after_physical=len({k for c in current['material_claims'] if c['status']=='pending' for k in c['source_unit_keys']});assert (before_physical,after_physical)==(452,431)
 current['current60_owner_identity']={'inventory':ref(INV),'original_installed27_source55_ledger':original_ref,'all1756_entire_owned_material_records_equal55_to60':True,'all119_entire_owned_exercise_records_equal55_to60':True,'actual_source56_to60_application':ref('reports/full-coverage/source56-60-corrections-application-v1.json'),'scope':'Only global inventory identity changes; all three Foundation pages and all entire owned records are byte-identical. Original semantic bodies and times are retained.'}
 current['current28_material_mapping']={'exact_interface':{'file':interface},'original_scope_plan':ref(SCOPE),'actual_canonical_readiness':ref(READY),'actual_canonical_outer_execution':ref(OUTER),'new_proof_files':list(proof_rows),'new_public_exports':99,'whole_material_units':21,'actual_canonical_commands':12,'original_21_pending_rows_retained_in_exact_interface':True,'all1112_prior_proved_claims_and119_exercises_retained_exact':True,'whole_physical_pending_before':452,'whole_physical_pending_after':431,'final_independent_mapping_review_pending':True,'installed_owner_or_aggregate28_claimed':False}
 invcurrent=copy.deepcopy(current);invcurrent.pop('current60_owner_identity');invcurrent.pop('current28_material_mapping');invcurrent['proof_files']=old['proof_files'];invcurrent['proof_sha256']=old['proof_sha256'];invcurrent['counts']=old['counts'];invcurrent['material_claims']=invcurrent['material_claims'][:-21]
 for r in removed:invcurrent['material_claims'].insert(r['original_index'],r['claim'])
 assert invcurrent==old and current['exercises']==old['exercises']
 assert [c for c in current['material_claims'] if c['status']=='proved'][:-21]==[c for c in old['material_claims'] if c['status']=='proved']
 stamp=datetime.now(timezone.utc).isoformat()
 iface={'status':'passed_exact_current60_foundation21_whole_literal_mapping_and_inverse','errors':[],'prepared_at_utc':stamp,'current_inventory':ref(INV),'original_installed27_ledger':original_ref,'original_scope_plan':ref(SCOPE),'entire_21_current60_literal_records':[units[m['inventory_key']] for m in scope['material_scope']],'all31_original_affected_claim_rows':original_rows,'removed21_pending_rows_with_original_indices':removed,'new21_whole_claim_rows':new,'exact_inverse_restores_original_entire_ledger':True,'original_semantic_review_bodies_and_times_unchanged':True,'canonical_pairs':ref(READY),'outer_canonical_execution':ref(OUTER),'counts':{'exercises_retained_complete':119,'old_proved_claims_retained':1112,'new_whole_material_units':21,'new_proof_sources':6,'new_public_theorem_bodies':99,'current60_canonical_commands':12,'physical_pending_before':452,'physical_pending_after':431},'coverage_complete':False}
 planned[interface]=data(iface);interface_ref={'file':interface,'sha256':hashlib.sha256(planned[interface]).hexdigest()};current['current28_material_mapping']['exact_interface']=interface_ref
 planned[candidate]=data(current);candidate_ref={'file':candidate,'sha256':hashlib.sha256(planned[candidate]).hexdigest()}
 integ={'status':'passed_actual_current60_foundations28_isolated_candidate_preparation','errors':[],'started_at_utc':started,'prepared_at_utc':stamp,'candidate':candidate_ref,'interface':interface_ref,'original_ledger':original_ref,'all119_exercises_and1112_prior_proved_claims_exact':True,'all1756_owned_inventory_records_equal55_to60':True,'all1175_selected27_source_bytes_protected':True,'all6_sources_and12_native_pairs_closed':True,'exact_inverse_restores_original_ledger':True,'coverage_complete':False,'installed_owner_source_selection_or_publication_mutated':False}
 planned[integrity]=data(integ)
 offerbody={'schema_version':1,'status':'prepared_current60_foundation28_canonical21_candidate_pending_independent_final_mapping','prepared_at_utc':stamp,'candidate':candidate_ref,'mapped_ledger':candidate,'mapped_ledger_sha256':candidate_ref['sha256'],'inventory':ref(INV),'inventory_sha256':INV_SHA,'source_sha256':old['source_sha256'],'proof_files':proof_rows,'new_proof_file_count':6,'new_theorem_or_lemma_count':99,'new_whole_material_unit_count':21,'new_whole_exercise_count':0,'exercise_counts':current['counts']['exercise_statuses'],'material_claim_counts':current['counts']['material_claim_statuses'],'physical_pending_unit_count':431,'exact_interface':interface_ref,'integrity':{'file':integrity,'sha256':hashlib.sha256(planned[integrity]).hexdigest()},'original_installed27_ledger':original_ref,'actual_canonical_readiness':ref(READY),'actual_canonical_outer_execution':ref(OUTER),'additional_frozen_inputs':evidence,'candidate_preparation_actual_pending':True,'independent_final_candidate_mapping_peer_pending':True,'coverage_complete':False,'aggregate28_selection_installation_or_publication_claimed':False}
 planned[offer]=data(offerbody)
 guard()
 for n,b in planned.items():assert not path(n).exists(),n
 for n,b in planned.items():
  p=path(n);p.parent.mkdir(parents=True,exist_ok=True)
  with p.open('xb') as f:f.write(b)
 guard()
 for n,b in planned.items():assert path(n).read_bytes()==b
 print(json.dumps({'status':integ['status'],'candidate':candidate_ref,'interface':interface_ref,'draft_offer':ref(offer),'counts':iface['counts']}))
if __name__=='__main__':main()
