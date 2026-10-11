from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,copy,sys
R=Path('/home/oxrexkevin/SafetyBased');H=lambda n:hashlib.sha256((R/n).read_bytes()).hexdigest();J=lambda n:json.loads((R/n).read_text());ref=lambda n:{'file':str(n),'sha256':H(n)}
CACHE={}
def exact(n,h):
 if n not in CACHE:CACHE[n]=H(n)
 assert CACHE[n]==h,(n,CACHE[n],h)
def checked(r):exact(r['file'],r['sha256']);return J(r['file'])
def atom(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':'),ensure_ascii=False).encode()).hexdigest()
def actual(n,helper):
 r=J(n);assert r.get('actual_exit_code',r.get('exit_code'))==0
 cmd=r.get('actual_command',r.get('command'));assert cmd and any(str(x).endswith(helper) for x in cmd),(n,cmd,helper)
 log=r.get('raw_log',r.get('log'));lh=r.get('raw_log_sha256',r.get('log_sha256'));exact(log,lh)
 if isinstance(r.get('helper_sha256_before'),dict):
  assert r['helper_sha256_before']==r['helper_sha256_after'];exact(helper,r['helper_sha256_before'][helper])
 else:
  before=r.get('actual_helper_sha256_before',r.get('helper_sha256_before'));after=r.get('actual_helper_sha256_after',r.get('helper_sha256_after'));assert before==after;exact(helper,before)
 return {'actual_record':ref(n),'raw_log':ref(log),'helper':ref(helper),'entire_original_record_body_and_time':r}
def evidence(o):
 maps={}
 for field in ['required_evidence_artifacts_sha256','required_live_integration_evidence_sha256','exact_source_reviews_sha256','actual_canonical_execution_records_sha256','canonical_readiness_sha256','canonical_source_peer_bindings_sha256']:
  maps.update(o.get(field,{}))
 for n,row in o['proof_files'].items():exact(n,row['sha256']);maps.update(row.get('evidence_sha256',{}))
 for n,h in maps.items():exact(n,h)
 return len(maps)
def main():
 assert len(sys.argv)==3
 corefile,out=sys.argv[1:]
 inv51='book/coverage/inventory-after-correction51.json';inv52='book/coverage/inventory-after-correction52.json';exact(inv51,'d746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41');exact(inv52,'38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3');assert H('book/coverage/inventory.json')==H(inv52)
 before,after=J(inv51),J(inv52)
 apply='reports/full-coverage/source52-apply-execution-v1.json';post='book/coverage/checks/root-source-batch52/postwrite-source-integrity-v1.json'
 a,p=J(apply),J(post);assert a['actual_exit_code']==p['actual_exit_code']==0;exact(a['log'],a['log_sha256']);assert p['inventory_after_sha256']==H(inv52)
 manifest='reports/full-coverage/checkpoint-23-manifest.json';exact(manifest,'e21eac7bfafd8002d75966240e5c3ea940ebec3dba4066fb1e9a767627d7fb06');m=J(manifest)
 held=['book/coverage/'+x+'.json' for x in ['core','foundations','applied','modules','applied-promotions']]
 heldsha={n:m['working_inputs_sha256'][n] for n in held}
 for n,h in heldsha.items():exact(n,h)
 specs=[('core',corefile)]
 rows={}
 for owner,n in specs:
  o=J(n)
  if owner=='core':
   oldref=o['original_source51_reviewed_offer'];old=checked(oldref);idref=o['source52_identity'];side=checked(idref)
   oldcandref=side['original_candidate'];oldcand=checked(oldcandref);newcandref=o['candidate_ledger'];cand=checked(newcandref)
   reverse=copy.deepcopy(cand);reverse.pop('source52_core_identity_binding');reverse['current_inventory']=oldcand['current_inventory'];reverse['current_inventory_sha256']=oldcand['current_inventory_sha256'];assert reverse==oldcand
   rev=copy.deepcopy(o)
   mb=rev.pop('unrelated_source52_offer_map_binding');mv1=checked(mb['original_source52_offer_v1'])
   assert mb['entire_original_source52_offer_v1_body_and_time']==mv1 and mb['original_source_sha256']==mv1['source_sha256']
   nm='SafeLearning/nn-in-the-loop.html';assert mv1['source_sha256'][nm]=='413846b5ffc2a5fd70f74fb6f4a24e96b7983b6a745f50340c9d2d25c75d7049' and o['source_sha256'][nm]=='1a39cab6587a6fe91dca670facc5e58e7c85cb6c0a2c065f43763656d5b73041'
   assert {k:v for k,v in o['source_sha256'].items() if k!=nm}=={k:v for k,v in mv1['source_sha256'].items() if k!=nm}
   rev['source_sha256']=copy.deepcopy(mb['original_source_sha256']);assert rev==mv1
   mapactual=actual('reports/full-coverage/root-core24-source52-offer-map-v2-execution-v1.json','book/coverage/checks/root_rebind_core24_offer52_source_map_v2.py')
   for k in ['source52_identity','original_source51_reviewed_offer','entire_original_source51_offer_body_and_time','final_independent_source52_identity_peer_pending']:rev.pop(k)
   for k in ['prepared_at_utc','candidate_ledger','inventory','inventory_sha256']:rev[k]=copy.deepcopy(old[k])
   assert rev==old
   assert o['entire_original_source51_offer_body_and_time']==old
   build='reports/full-coverage/root-core24-source52-identity-execution-v1.json';helper='book/coverage/checks/root_rebase_core24_source52_v1.py'
  else:
   rb=o['current52_identity_rebase'];oldref=rb['original_source51_reviewed_offer'];old=checked(oldref);idref=rb['identity_sidecar'];side=checked(idref)
   oldcandref=side['original_source51_candidate'];oldcand=checked(oldcandref);newcandref={'file':o['mapped_ledger'],'sha256':o['mapped_ledger_sha256']};cand=checked(newcandref)
   reverse=copy.deepcopy(cand);reverse.pop('current52_owner_identity');assert reverse==oldcand
   rev=copy.deepcopy(o);rev.pop('current52_identity_rebase');rev.update(rb['original_source51_outer_fields']);assert rev==old
   if owner=='foundations':
    build='book/coverage/checks/foundations-future24/source52/identity-builder-actual-execution-source52-v2.json';helper='book/coverage/build_foundations24_candidate_source52_identity_v2.py'
    hist=side['preserved_first_identity_builder_failure'];failed=checked(hist['record']);assert failed==hist['entire_original_record_body_and_time'] and failed['actual_exit_code']==1;checked(hist['raw_log']);checked(hist['helper']);checked(hist['runner'])
   else:
    oldp=checked(side['original_source51_promotions']);newp=J(o['mapped_promotions']);exact(o['mapped_promotions'],o['mapped_promotions_sha256']);v=copy.deepcopy(newp);v.pop('current52_owner_identity');assert v==oldp
    build='book/coverage/checks/applied-future24/source52/applied24-source52-isolated-identity-actual-v1.json';helper='book/coverage/checks/applied-future24/prepare_applied24_source52_identity_candidate_v1.py'
  assert o['proof_files']==old['proof_files']
  # Every original entire candidate row is recovered above, including all atoms,
  # reasons, hypotheses, review bodies/times and source/compiler metadata.
  owned={};scope=set(oldcand['scope_pages'])
  for kind in ['exercises','material_source_units']:
   bb={r['key']:r for r in before[kind] if r['source'] in scope};aa={r['key']:r for r in after[kind] if r['source'] in scope};assert bb==aa
   owned[kind]=len(aa)
   if 'entire_owned_inventory_records' in side:assert {r['key']:r for r in side['entire_owned_inventory_records'][kind]}==aa
   else:assert side['exact_owned_inventory_literal_sha256'][kind]=={k:r['text_sha256'] for k,r in aa.items()}
  for path,h in cand['source_sha256'].items():exact(path,h)
  for path,h in o['source_sha256'].items():exact(path,h)
  evidcount=evidence(o)
  proofmap=cand.get('proof_sha256',cand['proof_files'])
  for path,row in proofmap.items():exact(path,row if isinstance(row,str) else row['sha256'])
  rows[owner]={'status':'independent_exact_inventory_identity_rebase_confirmation_passed','errors':[],
   'source52_offer':ref(n),'original_source51_offer':oldref,'source52_candidate':newcandref,'original_source51_candidate':oldcandref,
   'rebase_manifest':idref['file'],'rebase_manifest_sha256':idref['sha256'],'immutable_inventory_after':inv52,'immutable_inventory_after_sha256':H(inv52),
   'owned_entire_literal_counts':owned,'original_candidate_exercise_rows':len(cand['exercises']),'original_material_claim_atoms':len(cand['material_claims']),
   'original_proof_metadata_rows':len(cand['proof_files']),'exact_evidence_artifacts_checked':evidcount,
   'actual_identity_execution':actual(build,helper),'actual_map_only_execution':mapactual,'candidate_and_offer_inverse_exact':True,'mathematical_bodies_hypotheses_reasons_decisions_times_proofs_and_compiler_records_unchanged':True,
   'new_math_compiler_live_global_aggregate_claim':False}
 assert len(m['proof_files'])==1131 and len(m['frozen_inputs_sha256'])==36910
 for n,row in m['proof_files'].items():exact(n,row['sha256'])
 snap=Path(m['snapshot']);
 for n,h in m['frozen_inputs_sha256'].items():exact(str(snap/n),h)
 for n,h in heldsha.items():assert H(n)==h
 result={'status':'independent_exact_inventory_identity_rebase_confirmation_passed','errors':[],
  'checked_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'/root/modules_resume','owners':rows,
  'immutable_inventory_after':inv52,'immutable_inventory_after_sha256':H(inv52),'actual_source52_apply':ref(apply),'actual_source52_postwrite':ref(post),
  'baseline23_manifest':ref(manifest),'all1131_selected_source_and36910_frozen_input_hashes_exact':True,'held_live_owner_sha256':heldsha,
  'scope':'Read-only exact identity mechanics only. Original full/partial semantic decisions and times retained. No new mathematical rereview, compiler run, live copy, global24 or aggregate claim.'}
 p=Path(out);assert not p.exists();p.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'report':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}))
if __name__=='__main__':main()
