"""NEW isolated identity51 candidate; prior proof/semantic/mapping records are immutable."""
from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json
ROOT=Path(__file__).resolve().parents[2];OLD_BASE=ROOT/'book/coverage/checks/foundations-future23/source50';BASE=ROOT/'book/coverage/checks/foundations-future23/source51'
INV=ROOT/'book/coverage/inventory-after-correction51.json';INV_SHA='d746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def rel(p):return p.relative_to(ROOT).as_posix()
def ref(p):return {'file':rel(p),'sha256':sha(p)}
def write(p,d):
 with p.open('x') as f:f.write(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
def pin(p,h):assert sha(p)==h,p;return read(p)
def exact_copy(src,dst):
 dst.parent.mkdir(parents=True,exist_ok=True)
 if dst.exists():assert dst.read_bytes()==src.read_bytes(),dst
 else:
  with dst.open('xb') as f:f.write(src.read_bytes())
 return {'original':{'file':str(src),'sha256':sha(src)},'canonical_alias':ref(dst),'exact_original_bytes':True}
def main():
 assert sha(INV)==sha(ROOT/'book/coverage/inventory.json')==INV_SHA
 oldofferpath=OLD_BASE/'foundations-audit23-candidate-source50-additions-v1.json';oldoffer=pin(oldofferpath,'dcc4056b55caecf0ec0068918fe56cc779f1833f5df95ff5dbe6cb791220775a')
 oldcandidatepath=OLD_BASE/'foundations23-candidate-source50-v1.json';old=pin(oldcandidatepath,'ab48adca29ae6bc13fe87466700e07cb0b6112a2668ad494b98a6a4a34a93c79')
 oldinterfacepath=OLD_BASE/'foundations23-complete-literal-interface-source50-v1.json';oldinterface=pin(oldinterfacepath,'99bad47ce7dcfc716e2da475ea0be820c01745b348f860d9bb73bc6e500e4b9c')
 peerpath=Path('/tmp/foundations23-source50-candidate-independent-modules-mechanical-confirmation-v2.json');peer=pin(peerpath,'54f9ebe6c0412cfd8b29ed049b42a893243f4b44b42bd19de0e9c5a5ea517a2b')
 assert 'passed' in peer['status'] and peer['errors']==[] and peer['candidate_ledger']==ref(oldcandidatepath) and peer['candidate_offer']==ref(oldofferpath)
 inv=read(INV);prev=read(ROOT/'book/coverage/inventory-after-correction50.json');held=ROOT/'book/coverage/foundations.json';heldsha='305229a7e1df78c23bc1af728c7f3f4e0ac09d13c55e4e687fe721160b43bf88';assert sha(held)==heldsha
 scopes=set(old['scope_pages']);owned=[r for r in inv['material_source_units'] if r['source'] in scopes];ex=[r for r in inv['exercises'] if r['source'] in scopes]
 assert len(owned)==1756 and owned==[r for r in prev['material_source_units'] if r['source'] in scopes]
 assert len(ex)==119 and ex==[r for r in prev['exercises'] if r['source'] in scopes]
 assert all(r=={u['key']:u for u in owned}[r['key']] for r in [m['entire_current50_inventory_record'] for m in oldinterface['material_units']])
 manifest=read(ROOT/'reports/full-coverage/checkpoint-22-manifest.json');assert len(manifest['proof_files'])==1113
 frozenassets={n:h for n,h in manifest['working_inputs_sha256'].items() if n.startswith('SafeLearning/')};assert len(frozenassets)==31
 protected={n:r['sha256'] for n,r in manifest['proof_files'].items()}
 protected.update(frozenassets);protected.update({n:h for n,h in manifest['working_inputs_sha256'].items() if n in {'book/coverage/core.json','book/coverage/modules.json','book/coverage/applied.json','book/coverage/foundations.json'}})
 protected.update({'SafeLearning/cmdp.html':'76c03226e17b8c058fa05085e55dbe9374272541fd1c347d7a0dc98542b3795a','SafeLearning/lyapunov-mpc.html':'228e4e22eaa32ad287069001abe9507706ec0112ec2ed9e1d3cfb2d569c4be7c','book/coverage/inventory.json':INV_SHA,'book/coverage/inventory-after-correction51.json':INV_SHA})
 protected.update(oldoffer['source_sha256']);protected.update({oldoffer['current_owner_builder']:oldoffer['current_owner_builder_sha256']})
 for n,row in oldoffer['proof_files'].items():
  protected[n]=row['sha256'];protected.update(row['evidence_sha256'])
 def guard():
  for n,h in protected.items():assert sha(ROOT/n)==h,n
  for n,h in frozenassets.items():assert sha(ROOT/'reports/full-coverage/checkpoint-22'/n)==h,n
 guard();BASE.mkdir(parents=True,exist_ok=True)
 paths=[BASE/'foundations23-candidate-source51-v1.json',BASE/'foundations23-complete-literal-interface-source51-v1.json',BASE/'foundations-audit23-candidate-source51-additions-draft-v1.json',BASE/'source50-to51-original-candidate-and-peer-binding-v1.json']
 assert not any(p.exists() for p in paths)
 names=['foundations23-source50-candidate-independent-modules-mechanical-confirmation-v2.json','modules-foundation23-source50-candidate-mechanical-check-v1.py','modules-foundation23-source50-candidate-mechanical-check-v2.py','modules-foundation23-source50-candidate-mechanics-actual-execution-v1.json','modules-foundation23-source50-candidate-mechanics-actual-execution-v1.log','modules-foundation23-source50-candidate-mechanics-actual-execution-v2.json','modules-foundation23-source50-candidate-mechanics-actual-execution-v2.log']
 archives=[exact_copy(Path('/tmp')/n,BASE/'original-source50-candidate-module-peer'/n) for n in names]
 canonicalpeer=BASE/'original-source50-candidate-module-peer'/peerpath.name
 exe=read(Path('/tmp')/names[-2]);assert exe['actual_exit_code']==0 and sha(Path(exe['log']))==exe['log_sha256'] and exe['actual_checker_sha256_before']==exe['actual_checker_sha256_after']==sha(Path('/tmp')/names[2])
 integritypath=ROOT/'book/coverage/checks/root-source-batch51/postwrite-source-integrity-v1.json';integrity=read(integritypath);assert integrity['actual_exit_code']==0 and 'passed' in integrity['status'] and integrity['inventory_after_sha256']==INV_SHA
 rootactual=ROOT/'reports/full-coverage/source51-apply-execution-v1.json';rootrecord=read(rootactual);assert rootrecord.get('actual_exit_code',rootrecord.get('exit_code'))==0
 candidate=copy.deepcopy(old)
 candidate['current23_owner_identity']=dict(old['current23_owner_identity'],inventory=ref(INV),original_source50_candidate=ref(oldcandidatepath),original_source50_independent_mapping_peer=ref(canonicalpeer),original_source50_owner_identity_exact=old['current23_owner_identity'],scope='Global identity51 is new. All1756 Foundation physical records,119 complete exercises,14 semantic rows,39 exports and original review bodies/times remain exactly equal to the independently reviewed source50 candidate. Only the isolated identity/interface metadata changes.')
 candidate['current23_material_mapping']=dict(old['current23_material_mapping'],interface_binding=rel(paths[1]))
 allowed={'current23_owner_identity','current23_material_mapping'};assert {k:v for k,v in candidate.items() if k not in allowed}=={k:v for k,v in old.items() if k not in allowed}
 write(paths[0],candidate)
 binding={'status':'passed_exact_source50_to51_unchanged_foundation_candidate_identity','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'candidate_ledger':ref(paths[0]),'current_inventory':ref(INV),'original_source50_candidate':ref(oldcandidatepath),'original_source50_interface':ref(oldinterfacepath),'entire_original_source50_interface_body_and_times':oldinterface,'original_source50_independent_mapping_peer':ref(canonicalpeer),'entire_original_independent_peer_body_and_time':peer,'all1756_foundation_literals_and119_exercises_unchanged50_to51':True,'semantic_or_proof_changes':False,'new_whole_material_units':14,'new_sources':3,'new_public_exports':39,'candidate_changes_only_owner_identity_and_interface_metadata':True,'actual_root_source51_apply':ref(rootactual),'actual_root_source51_postwrite_integrity':ref(integritypath),'limits':['The immutable source50 candidate was independently reviewed; this is a distinct source51 identity/interface delta.','No old semantic decision/time/source/actual execution or current22 ledger is changed. No aggregate23/publication or live installation is claimed.']}
 write(paths[1],binding)
 final50=copy.deepcopy(oldoffer);final50['status']='passed_isolated_source50_candidate39_exports14_whole_units_with_independent_final_mapping_peer';final50['final_independent_candidate_mapping_peer']=ref(canonicalpeer);final50['independent_final_candidate_mapping_peer_pending']=False
 final50path=OLD_BASE/'foundations-audit23-candidate-source50-additions-v2-reviewed.json';assert not final50path.exists();write(final50path,final50)
 draft=copy.deepcopy(final50);draft.update({'status':'isolated_source51_identity_candidate23_pending_narrow_identity_delta_peer','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'original_source50_final_offer':ref(final50path),'mapped_ledger':rel(paths[0]),'mapped_ledger_sha256':sha(paths[0]),'current_inventory':rel(INV),'current_inventory_sha256':INV_SHA,'material23_exact_interface_binding':rel(paths[1]),'material23_exact_interface_binding_sha256':sha(paths[1]),'current_owner_builder':rel(Path(__file__)),'current_owner_builder_sha256':sha(Path(__file__)),'original_actual_source50_candidate_builder':oldoffer['actual_builder_record'],'actual_identity_builder_record_pending':True,'independent_source51_identity_delta_peer_pending':True})
 draft.pop('actual_builder_record',None);write(paths[2],draft)
 write(paths[3],{'status':'passed_exact_source50_candidate_and_actual_peer_history_retained_under_identity51','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'archives':archives,'source50_original_offer':ref(oldofferpath),'source50_reviewed_offer':ref(final50path),'source50_candidate':ref(oldcandidatepath),'source51_candidate':ref(paths[0]),'source51_interface':ref(paths[1]),'source51_draft':ref(paths[2]),'protected_current51_and_four_held22_ledger_sha256':protected,'frozen22_original31_asset_sha256':frozenassets,'full_32040_and34051_frozen_map_rehash_claimed_here':False,'actual_root_frozen21_22_integrity_evidence':ref(integritypath),'semantic_body_time_proof_evidence_changes':False})
 guard();print(json.dumps({'status':'passed_isolated_new_source51_identity_builder','candidate':ref(paths[0]),'interface':ref(paths[1]),'draft_offer':ref(paths[2]),'source50_final_offer':ref(final50path),'history':ref(paths[3])}))
if __name__=='__main__':main()
