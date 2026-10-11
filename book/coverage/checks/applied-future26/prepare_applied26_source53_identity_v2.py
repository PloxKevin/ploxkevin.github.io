"""Root-authorized isolated Applied26 identity copy, preserving all source52 math."""
from pathlib import Path
from datetime import datetime,timezone
import argparse,copy,hashlib,json
ROOT=Path(__file__).resolve().parents[4];B='book/coverage/checks/applied-future26/source53-v2'
O='book/coverage/checks/applied-future26/source52-v2/applied-audit26-candidate-source52-additions-v2-reviewed.json';OS='ce4aa936bdad154afc2a3d90da092a50c4c16183ddf929369e23ba90696ef81c'
I0='book/coverage/inventory-after-correction52.json';I='book/coverage/inventory-after-correction53.json';IS='4b1e657eb61234a6d2e2a3a3ea6a0b11986c01d7d1c7cb5ba2dd5452d1fe29be'
H=lambda n:hashlib.sha256((ROOT/n).read_bytes()).hexdigest();J=lambda n:json.loads((ROOT/n).read_text());ref=lambda n:{'file':n,'sha256':H(n)}
def put(n,d):
 p=ROOT/n;assert not p.exists(),n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
def zero(d):
 cs=[d[k]for k in ('actual_exit_code','exit_code')if k in d];assert cs and all(type(x)is int and x==0 for x in cs)
def main():
 p=argparse.ArgumentParser();p.add_argument('--root-authorized-source53-identity-rebase',action='store_true',required=True);p.add_argument('--inventory-sha256',required=True);a=p.parse_args()
 assert a.root_authorized_source53_identity_rebase and a.inventory_sha256==IS==H(I)==H('book/coverage/inventory.json') and H(O)==OS
 o=J(O);c=J(o['mapped_ledger']);pr=J(o['mapped_promotions']);assert H(o['mapped_ledger'])==o['mapped_ledger_sha256']=='9f2e976dc67da15a6ae94f14bcd3891fbc8dc320a00296a5da56cfb1374e97c3';assert H(o['mapped_promotions'])==o['mapped_promotions_sha256']=='e4465ec73f4c68a0eb90154c873c834200240887f3d64605bf11d89c1fcc0b94'
 old=J(I0);new=J(I);scope=set(c['scope_pages']);assert len(scope)==3
 records={}
 for sec,count in [('exercises',128),('material_source_units',2059)]:
  x={r['key']:r for r in old[sec]if r['source']in scope};y={r['key']:r for r in new[sec]if r['source']in scope};assert x==y and len(y)==count;records[sec]=y
 assert c['source_sha256']==o['source_sha256']
 for n,h in c['source_sha256'].items():assert H(n)==h==old['source_sha256'][n]==new['source_sha256'][n]
 assert len(c['exercises'])==128 and sum(len(e['claims'])for e in c['exercises'])==468 and len(c['material_claims'])==1954 and len(c['proof_files'])==312
 assert len(o['proof_files'])==3
 for n,h in c['proof_files'].items():assert H(n)==h
 for n,h in o['required_evidence_artifacts_sha256'].items():assert H(n)==h
 manifest=J('reports/full-coverage/checkpoint-25-manifest.json');selection=J('reports/full-coverage/checkpoint-25-selection.json');assert len(selection['proof_files'])==1156
 protected={n:r['sha256']for n,r in selection['proof_files'].items()};ownerpaths=['book/coverage/'+x+'.json'for x in ['core','foundations','applied','modules','applied-promotions']]
 protected.update({n:manifest['working_inputs_sha256'][n]for n in ownerpaths});assert protected['book/coverage/applied.json']=='0a4ee34e6e3b55391a596c90ea92591eaa6bb3f6a103016c1c01635d225e0a9b'
 protected.update({n:h for n,h in manifest['working_inputs_sha256'].items()if n.startswith('SafeLearning/')});protected['SafeLearning/lyapunov-mpc.html']='5e21c5319d41968468781ee0bf9b18aec5147666f764827f3a96e9e73d0138af';protected[I]=IS;protected['book/coverage/inventory.json']=IS
 def guard():
  for n,h in protected.items():assert H(n)==h,n
 guard();native='reports/full-coverage/source53-correction-application-v1.json';act='reports/full-coverage/source53-correction-application-execution-v1.json';zero(J(act));assert H(native)=='fbc298db9520fb9eae49997fe7955062b1bb373605a3af81f40801fd317da548';ar=J(act);assert H(ar['log'])==ar['log_sha256']
 identity=B+'/unchanged-owned-literal-identity-v1.json';put(identity,{'status':'passed_exact_entire_applied_owned_source52_to53_identity','errors':[],'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'original_source52_final_offer':ref(O),'original_source52_candidate':ref(o['mapped_ledger']),'original_source52_promotions':ref(o['mapped_promotions']),'historical_inventory':ref(I0),'current_inventory':ref(I),'entire_owned_inventory_records':records,'owned_source_sha256':c['source_sha256'],'counts':{'exercises':128,'exercise_claims':468,'physical_units':2059,'material_claims':1954,'proof_metadata_rows':312,'new_identity_proofs':0},'actual_source53_application':ref(native),'actual_source53_execution':ref(act),'all_original_decisions_hypotheses_bodies_times_and_actual_math_pairs_unchanged':True,'protected_installed25_owner_sha256':{n:protected[n]for n in ownerpaths},'scope':'Identity copy only; preserves all three actual23-public proof source rows/six actual compiler records, whole371 decision and explicit Applied CVaR8 supply. No new review, mathematical or exercise promotion.'})
 overlay={'inventory':I,'inventory_sha256':IS,'identity_sidecar':ref(identity),'original_source52_final_offer':ref(O),'scope':'All owned entire literal records and original mathematical/evidence/review bodies unchanged52-to53.'}
 out=copy.deepcopy(c);outpr=copy.deepcopy(pr);out['current53_owner_identity']=copy.deepcopy(overlay);outpr['current53_owner_identity']=copy.deepcopy(overlay)
 assert {k:v for k,v in out.items()if k!='current53_owner_identity'}==c and {k:v for k,v in outpr.items()if k!='current53_owner_identity'}==pr
 C=B+'/applied26-candidate-source53-identity-v1.json';P=B+'/applied-promotions26-candidate-source53-identity-v1.json';put(C,out);put(P,outpr)
 integrity=B+'/identity-candidate-integrity-v1.json';put(integrity,{'status':'passed_actual_isolated_applied26_source53_identity','errors':[],'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'candidate':ref(C),'candidate_promotions':ref(P),'identity_sidecar':ref(identity),'original_offer':ref(O),'exact_inverse_restores_entire_source52_candidate_and_promotions':True,'all1156_selected25_sources_and_five_owners_current53_assets_exact':True,'live_owner_written':False,'coverage_complete':False})
 offer=copy.deepcopy(o);helper=str(Path(__file__).relative_to(ROOT));updates={'inventory':I,'inventory_sha256':IS,'mapped_ledger':C,'mapped_ledger_sha256':H(C),'mapped_promotions':P,'mapped_promotions_sha256':H(P),'candidate_builder':ref(helper),'candidate':ref(C),'candidate_promotions':ref(P)};orig={k:copy.deepcopy(o[k])for k in updates};offer.update(updates)
 offer['preserved_initial_source53_identity_preparation_failure']={'helper':ref('book/coverage/checks/applied-future26/prepare_applied26_source53_identity_v1.py'),'actual_execution':ref('book/coverage/checks/applied-future26/source53/source53-identity-preparation-actual-v1.json'),'raw_log':ref('book/coverage/checks/applied-future26/source53/source53-identity-preparation-actual-v1.log'),'scope':'Initial isolated identity preparation wrote only new candidate/promotions/sidecars, then failed reading candidate_builder_sha256 absent from original native offer. Original builder reference is typed file/sha256. No draft offer, live owner or math changed.'}
 offer['source53_identity_rebase']={'identity_sidecar':ref(identity),'identity_integrity':ref(integrity),'original_source52_reviewed_offer':ref(O),'original_source52_outer_fields':orig,'scope':'Only active inventory/candidate/builder pointers; original full final source52 offer preserved exactly by inverse. No semantic redecision or retiming.'}
 reverse=copy.deepcopy(offer);reverse.pop('source53_identity_rebase');reverse.pop('preserved_initial_source53_identity_preparation_failure');reverse.update(orig);assert reverse==o
 put(B+'/applied-audit26-candidate-source53-additions-draft-v1.json',offer);guard();print(json.dumps({'candidate':ref(C),'promotions':ref(P),'offer':ref(B+'/applied-audit26-candidate-source53-additions-draft-v1.json'),'integrity':ref(integrity)}))
if __name__=='__main__':main()
