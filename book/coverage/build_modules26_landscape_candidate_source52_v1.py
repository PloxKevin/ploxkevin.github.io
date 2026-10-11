"""Isolated Landscape26 candidate: reviewed eight classifications and three literals.

Module selects Wind4, Applied supplies CVaR8 explicitly. Earlier positive atoms,
proof rows and review bodies/times are preserved. No live ledger/source writes.
"""
from pathlib import Path
from datetime import datetime,timezone
import collections,copy,hashlib,json,re
from lean_names import declarations
R=Path(__file__).resolve().parents[2];BASE='book/coverage/checks/modules-future26/landscape'
LIVE='book/coverage/modules.json';LIVE_SHA='9f3736a26e2c729b138fd4cc10b3376d67d475b1e759e4fe56fb393c27e08a63'
INV='book/coverage/inventory-after-correction52.json';INV_SHA='38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
SUPP='/tmp/landscape15-three-physical-units-independent-foundations-final-scope-supplement26-v1.json';SUPP_SHA='0e5cc3e4e44884cba6116a42152217dcee7e161bb2c1237b9058fdb53a22367f'
WIND_READY='book/coverage/checks/future26-core/wind-classification/root-wind-classification26-canonical-readiness-v1.json';WIND_SHA='da67082cb6f1b4a59904ee5d3e8ae398fff4b47f51b2c471ee274e67c70d3bda'
CVAR_READY='book/coverage/checks/applied-future26/cvar-fractional-selector/one-source8-canonical-paired-build-readiness-v1.json';CVAR_SHA='5d5d43994379208e74f249d74aed915a3d70f35cebd09ad20dc6d9922c05f311'
APPLIED='book/coverage/checks/applied-future26/source52-v2/applied-audit26-candidate-source52-additions-v2-reviewed.json';APPLIED_SHA='ce4aa9363d8d9c614cb0689bb048d839d378d649e380b3274e07f022784d587c'
EX='landscape.html::exercise-15';KEYS=['landscape.html::node-1285','landscape.html::node-1294','landscape.html::node-1297']
def P(n):return Path(n) if Path(n).is_absolute() else R/n
def H(n):return hashlib.sha256(P(n).read_bytes()).hexdigest()
def J(n):return json.loads(P(n).read_text())
def ref(n):return {'file':n,'sha256':H(n)}
def put(n,b):
 p=P(n);assert not p.exists(),n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(b,indent=2,ensure_ascii=False)+'\n')
def zero(d):
 codes=[d[k] for k in ['actual_exit_code','exit_code'] if k in d];assert codes and all(type(v)is int and v==0 for v in codes)
def public(n):return [d['name'] for d in declarations(P(n).read_text()) if d['kind']in['theorem','lemma']]
def declrows(out,n,names):
 text=P(n).read_text();seen={d['name'] for d in out['declarations']}
 for name in names:
  if name in seen:continue
  m=re.search(r'^\s*(?:theorem|lemma)\s+'+re.escape(name.rsplit('.',1)[1])+r'\b',text,re.M);assert m,name
  out['declarations'].append({'name':name,'file':n,'line':text[:m.start()].count('\n')+1,'statement':text[m.start():].split(':=',1)[0].strip()});seen.add(name)
def compile_evidence(n,record,log):
 d=J(record);zero(d);assert d['source']==n
 before=d.get('source_sha256_before',d.get('sha256_before'));after=d.get('source_sha256_after',d.get('sha256_after'));assert before==after==H(n)
 hashes=[d[k] for k in ['log_sha256','raw_log_sha256'] if k in d];assert hashes and all(x==H(log)for x in hashes)
 return {'file':n,'sha256':H(n),'exit_code':0,'source_unchanged':True,'compiler_manifest':record,'compiler_manifest_sha256':H(record),'log':log,'log_sha256':H(log)}
def pair(n,record,log,snapshot,kind):
 d=J(record);zero(d);assert H(snapshot)==H(n)
 commands=[d[k] for k in ['command','actual_command']if k in d];wanted=['lake','env','lean',n.removeprefix('verification/lean/')]if kind=='standalone' else ['lake','build','SafeLearning.'+Path(n).stem];assert commands and all(x==wanted for x in commands)
 compile_evidence(n,record,log)
 return {'source':ref(n),'kind':kind,'actual_record':ref(record),'raw_log':ref(log),'source_snapshot':ref(snapshot),'actual_exit_code':0,'entire_original_actual_record_and_time':d}
def main():
 assert H(LIVE)==LIVE_SHA and H(INV)==H('book/coverage/inventory.json')==INV_SHA and H(SUPP)==SUPP_SHA and H(WIND_READY)==WIND_SHA and H(CVAR_READY)==CVAR_SHA
 # Pin an explicitly supplied Applied proof offer, rather than inferring filename ownership.
 assert H(APPLIED)==APPLIED_SHA
 old=J(LIVE);iv=J(INV);supp=J(SUPP);w=J(WIND_READY);cv=J(CVAR_READY);ap=J(APPLIED);selection=J('reports/full-coverage/checkpoint-25-selection.json')
 assert len(selection['proof_files'])==1156 and supp['errors']==[] and 'passed'in supp['status']
 for n,row in selection['proof_files'].items():assert H(n)==row['sha256']
 protected=w['protected_input_sha256']
 for n,h in protected.items():assert H(n)==h,n
 em={e['key']:e for e in iv['exercises']};um={u['key']:u for u in iv['material_source_units']}
 whole=J(w['original_full_source_peer']['file']);assert H(w['original_full_source_peer']['file'])==w['original_full_source_peer']['sha256']
 assert supp['entire_original_whole_peer_body_time_and_decisions_unchanged']==whole and whole['whole_exercise_approved']is True and whole['missing_clauses']==[] and whole['remaining_gaps']==[]
 assert whole['entire_inventory_record']==em[EX] and whole['exercise_components']==whole['eight_literal_clause_decisions'] and len(whole['exercise_components'])==8
 units=supp['material_units'];assert [u['source_unit_key']for u in units]==KEYS
 for u in units:assert u['entire_inventory_record']==um[u['source_unit_key']] and u['whole_literal_approved']is True and u['missing_clauses']==u['remaining_gaps']==[]
 for u in [units[0],units[2]]:assert u['components']==whole['exercise_components'] and u['status']=='proved'
 assert units[1]['status']=='not_formalizable'
 aliases={}
 originals={SUPP:SUPP_SHA,**{n:h for n,h in supp['closed_evidence_sha256'].items()if Path(n).is_absolute()}}
 for n,h in originals.items():
  assert H(n)==h;dst=BASE+'/original-tmp/'+Path(n).name;p=P(dst);p.parent.mkdir(parents=True,exist_ok=True)
  assert not p.exists(),dst;p.write_bytes(P(n).read_bytes());assert H(dst)==h;aliases[n]=ref(dst)
 supplement=aliases[SUPP];baseline=BASE+'/pre-candidate25/modules.json';p=P(baseline);p.parent.mkdir(parents=True,exist_ok=True);assert not p.exists();p.write_bytes(P(LIVE).read_bytes());assert H(baseline)==LIVE_SHA
 out=copy.deepcopy(old);e=next(e for e in out['exercises']if e['inventory_key']==EX);prior_ex=copy.deepcopy(e);assert e['status']=='pending'
 e['claims']=[]
 for g in whole['exercise_components']:
  assert g['missing_clauses']==g['remaining_gaps']==[]
  e['claims'].append({'id':EX+'::source52-reviewed26-classification-'+str(g['clause']),'statement_in_prose':g['source_classification'],'kind':'independently_reviewed_complete_exercise_classification_clause','status':'proved','lean_declarations':copy.deepcopy(g['lean_declarations']),'hypotheses':copy.deepcopy(g['hypotheses']),'correspondence':g['reason'],'remaining_gaps':[],'source_unit_keys':[KEYS[0],KEYS[2]],'independent_source_review':w['original_full_source_peer'],'entire_original_component_body_and_review_time':copy.deepcopy(g),'original_whole_review_time':whole['reviewed_at_utc']})
 e.update(status='complete_math',prior_source52_pending_exercise_body_preserved26=prior_ex,independent_whole_source_review26=w['original_full_source_peer'],independent_physical_unit_scope_supplement26=supplement,entire_original_whole_review_body_and_time_preserved26=whole)
 for u in units:
  key=u['source_unit_key'];oldrow=next(x for x in out['material_claims']if x['id']==key+'::claim-review')
  atom={'id':key+'::source52-reviewed26-complete-literal','statement_in_prose':um[key]['source_text'],'kind':'independently_reviewed_complete_mathematical_source_unit'if u['status']=='proved'else'independently_reviewed_complete_conditional_modeling_caveat','status':'proved'if u['status']=='proved'else'not_a_formal_claim','lean_declarations':copy.deepcopy(u['lean_declarations']),'hypotheses':copy.deepcopy(u['hypotheses']),'correspondence':u['reason'],'remaining_gaps':[],'source_unit_keys':[key],'independent_source_review':supplement,'entire_original_literal_decision_and_review_time':copy.deepcopy(u),'entire_original_whole_review_body_and_time':whole}
  if key==KEYS[2]:
   assert oldrow['status']=='pending';prior=copy.deepcopy(oldrow);oldrow.update(atom);oldrow['id']=key+'::claim-review';oldrow['prior_source44_pending_claim_body_preserved26']=prior
  else:
   # Keep the two earlier positive atoms byte-identical; new caveat disposition adds no sampling guarantee.
   assert oldrow['status']=='proved';out['material_claims'].append(atom)
 nwind=w['source']['file'];ncvar=cv['proof_sources'][0]['source']['file'];assert nwind not in old['proof_files']and ncvar not in old['proof_files']
 assert ncvar in ap['proof_files'] and ap['proof_files'][ncvar]['sha256']==H(ncvar)
 new={};cross={}
 for n,ready,snap,owner in [(nwind,w,w['source_snapshot']['file'],'Modules26'),(ncvar,cv['proof_sources'][0],cv['proof_sources'][0]['source_snapshot']['file'],'Applied26')]:
  names=public(n);assert len(names)==(4 if owner=='Modules26'else 8)
  rawpairs=ready['actual_canonical_pair'];pairs=[]
  for raw,kind in zip(rawpairs,['standalone','named-build']):
   record=raw.get('record',raw)['file'];d=J(record);log=d.get('log',d.get('raw_log'));pairs.append(pair(n,record,log,snap,kind))
  stand=pairs[0];row={'sha256':H(n),'proof_selection_owner':owner,'selection_scope':'independently_whole_reviewed_landscape26_classification_source','standalone_compile_status':'passed','standalone_compile_evidence':compile_evidence(n,stand['actual_record']['file'],stand['raw_log']['file']),'actual_paired_records':pairs,'declarations':names}
  if owner=='Applied26':row.update(explicit_cross_owner_proof_offer=ref(APPLIED),entire_original_supplied_proof_metadata=ap['proof_files'][n]);cross[n]={'sha256':H(n),'proof_offer_owner':'Applied26','proof_offer':ref(APPLIED),'proof_metadata':ap['proof_files'][n],'actual_paired_records':pairs,'declarations':names}
  else:new[n]={'sha256':H(n),'declarations':names,'actual_paired_records':pairs,'evidence_sha256':{p[k]['file']:p[k]['sha256']for p in pairs for k in ['actual_record','raw_log','source_snapshot']}}
  out['proof_files'][n]=row;declrows(out,n,names)
 assert len(new)==len(cross)==1
 direct=supp['direct_declaration_sources']
 # Exact reused baseline sources may be new to Module metadata, but are never new selected proofs.
 reused={}
 for name,source in direct.items():
  n=source['file']if isinstance(source,dict)else source
  assert name in public(n)
  if n not in [nwind,ncvar]:
   sr=selection['proof_files'][n];assert H(n)==sr['sha256']
   if n not in out['proof_files']:
    record=sr.get('compiler_manifest',sr.get('original_actual_zero_record'));assert record,n
    logs=[f for f,h in sr['evidence_sha256'].items()if f.endswith('.log')];assert len(logs)==1,n
    out['proof_files'][n]={'sha256':H(n),'proof_selection_owner':'original_selected25_owner_reused_by_Modules26','selection_scope':'exact_selected25_proof_reused_for_reviewed_landscape26_literal','standalone_compile_status':'passed','standalone_compile_evidence':compile_evidence(n,record,logs[0]),'declarations':public(n),'entire_original_selected25_source_row':sr}
   reused[n]=sr
  declrows(out,n,[name])
 out['generated_at_utc']=datetime.now(timezone.utc).isoformat()
 out['reviewed_work_integration26_landscape_candidate']={'baseline25_module_ledger':ref(baseline),'current_inventory':ref(INV),'original_whole_review':w['original_full_source_peer'],'physical_unit_supplement':supplement,'entire_original_supplement_body_and_time':supp,'original_closed_byte_aliases':aliases,'Module_owned_new_proofs':new,'explicit_cross_owner_required_proofs':cross,'selected25_reused_source_rows':reused,'fresh_whole_exercise_keys':[EX],'fresh_physical_unit_keys':KEYS,'previous_positive_material_atoms_preserved_exact':KEYS[:2],'whole_classification_groups':8,'Module_new_source_count':1,'Module_new_public_export_count':4,'cross_owner_new_source_count':1,'cross_owner_new_public_export_count':8,'standalone_old_quantile_duplicate_selected':False,'live_owner_assets_mutated':False}
 out['counts']={'exercises':len(out['exercises']),'exercise_status':dict(collections.Counter(e['status']for e in out['exercises'])),'exercise_claim_status':dict(collections.Counter(c['status']for e in out['exercises']for c in e['claims'])),'material_claim_status':dict(collections.Counter(c['status']for c in out['material_claims'])),'new_declarations':len(out['declarations'])}
 for e0,e1 in zip(old['exercises'],out['exercises']):
  if e0['inventory_key']!=EX:assert e0==e1
 for c0,c1 in zip(old['material_claims'],out['material_claims']):
  if c0['id']!=KEYS[2]+'::claim-review':assert c0==c1
 for n,row in old['proof_files'].items():assert out['proof_files'][n]==row
 assert out['declarations'][:len(old['declarations'])]==old['declarations']
 for n,h in protected.items():assert H(n)==h,n
 for n,row in selection['proof_files'].items():assert H(n)==row['sha256']
 inputpath=BASE+'/modules26-landscape-source52-input-bindings-v1.json';put(inputpath,{'status':'passed_exact_original_reviews_and_explicit_cross_owner_scope_bindings','errors':[],'baseline25_module_ledger':ref(baseline),'inventory':ref(INV),'original_whole_peer':w['original_full_source_peer'],'physical_unit_supplement':supplement,'entire_original_whole_review_body_and_time':whole,'entire_original_supplement_body_and_time':supp,'original_closed_byte_aliases':aliases,'Module_owned_new_proofs':new,'explicit_cross_owner_required_proofs':cross,'selected25_reused_sources':reused,'protected_input_sha256':protected})
 candidate=BASE+'/modules26-landscape-candidate-source52-v1.json';put(candidate,out)
 integrity=BASE+'/modules26-landscape-source52-candidate-integrity-v1.json';put(integrity,{'status':'passed_isolated_exact_landscape26_whole_and_physical_mapping','errors':[],'candidate':ref(candidate),'input_bindings':ref(inputpath),'baseline25_module_ledger':ref(baseline),'inventory':ref(INV),'fresh_whole_exercise_keys':[EX],'fresh_physical_unit_keys':KEYS,'old_other_exercise_bodies_exact':216,'old_other_material_bodies_exact':len(old['material_claims'])-1,'old_proof_rows_exact':len(old['proof_files']),'old_declaration_prefix_exact':True,'whole_groups':8,'own_new_sources':1,'own_new_public_exports':4,'cross_owner_new_sources':1,'cross_owner_new_public_exports':8,'duplicate_old_quantile_source_added':False,'live_owner_assets_mutated':False})
 print(json.dumps({'candidate':ref(candidate),'input_bindings':ref(inputpath),'integrity':ref(integrity),'counts':out['counts']}))
if __name__=='__main__':main()
