"""NEW isolated Source53 identity rebinding; all Module literal/math bodies exact."""
from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json
R=Path(__file__).resolve().parents[2];B='book/coverage/checks/modules-future26/source53';OLD='book/coverage/checks/modules-future26/source52/modules26-combined-candidate-source52-v1.json';OS='03ace634c3e9b460931988a05ad9877e532d5b4927a852f346e3ec5703a6df50';OFFER='book/coverage/checks/modules-future26/source52/modules-audit26-candidate-source52-additions-draft-v1.json';OFFSHA='97570458140f20b339d550022c33d2e5e0c85e995e72725c1da23bf4a2ec634c';INV='book/coverage/inventory-after-correction53.json';IS='4b1e657eb61234a6d2e2a3a3ea6a0b11986c01d7d1c7cb5ba2dd5452d1fe29be';P=lambda n:R/n;H=lambda n:hashlib.sha256(P(n).read_bytes()).hexdigest();J=lambda n:json.loads(P(n).read_text());ref=lambda n:{'file':n,'sha256':H(n)}
def put(n,d):
 p=P(n);assert not p.exists(),n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
def zero(d):
 codes=[d[k]for k in['actual_exit_code','exit_code']if k in d];assert codes and all(type(v)is int and v==0 for v in codes)
assert H(OLD)==OS and H(OFFER)==OFFSHA and H(INV)==H('book/coverage/inventory.json')==IS
before=J('book/coverage/inventory-after-correction52.json');after=J(INV);old=J(OLD);of=J(OFFER);native='reports/full-coverage/source53-correction-application-v1.json';act='reports/full-coverage/source53-correction-application-execution-v1.json';n=J(native);a=J(act);zero(a);assert H(native)=='fbc298db9520fb9eae49997fe7955062b1bb373605a3af81f40801fd317da548'and H(act)=='443b21e920e2cd3d8b12607117c059e105c73b6015893d6e4f5976fc08684157'and n['inventory_after']==ref(INV);assert H(a['log'])==a['log_sha256'];assert a['helper_sha256_before']==a['helper_sha256_after']and all(H(p)==h for p,h in a['helper_sha256_after'].items())
owned={}
for section in['exercises','material_source_units']:
 rows0={r['key']:r for r in before[section]if r['source']in old['scope_pages']};rows1={r['key']:r for r in after[section]if r['source']in old['scope_pages']};assert rows0==rows1;owned[section]=rows0
assert len(owned['exercises'])==217 and len(owned['material_source_units'])==4977
for p,h in old['source_sha256'].items():assert H(p)==h
selected=J('reports/full-coverage/checkpoint-25-selection.json');assert len(selected['proof_files'])==1156
for p,row in selected['proof_files'].items():assert H(p)==row['sha256']==H('reports/full-coverage/checkpoint-25/'+p)
manifest=J('reports/full-coverage/checkpoint-25-manifest.json');ownerpaths=['book/coverage/'+k+'.json'for k in ['core','foundations','applied','modules','applied-promotions']]
for p in ownerpaths:assert H(p)==manifest['working_inputs_sha256'][p]
assets={p:h for p,h in manifest['working_inputs_sha256'].items()if p.startswith('SafeLearning/')};assert len(assets)==31
for p,h in assets.items():
 assert H('reports/full-coverage/checkpoint-25/'+p)==h
 if p!='SafeLearning/lyapunov-mpc.html':assert H(p)==h
assert H(n['source_after']['file'])==n['source_after']['sha256']and H(n['source_before']['file'])==n['source_before']['sha256']
I=B+'/modules26-source52-to53-owner-identity-binding-v1.json';C=B+'/modules26-combined-candidate-source53-v1.json';out=copy.deepcopy(old);original_active={'current_inventory':old['current_inventory'],'current_inventory_sha256':old['current_inventory_sha256']};out['current_inventory']=INV;out['current_inventory_sha256']=IS;out['inventory_identity_rebase53']={'original_source52_candidate':ref(OLD),'original_source52_offer':ref(OFFER),'identity_binding':I,'current_inventory':ref(INV),'original_active_inventory_fields':original_active,'entire_own_exercise_record_count':217,'entire_own_material_record_count':4977,'mathematics_reviews_times_proof_evidence_unchanged':True,'scope':'Metadata-only current53 pointer; entire Module-owned records unchanged52→53. All source52 literal semantic bodies/time and genuine compiler records remain historical exact.'}
rest=copy.deepcopy(out);del rest['inventory_identity_rebase53'];rest.update(original_active);assert rest==old
identity={'status':'passed_exact_unchanged_module_owner_records_source52_to53_identity_preparation','errors':[],'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'original_candidate':ref(OLD),'original_offer':ref(OFFER),'inventory_before':ref('book/coverage/inventory-after-correction52.json'),'inventory_after':ref(INV),'entire_owned_records_unchanged':owned,'original_active_inventory_fields':original_active,'actual_root_source53_execution':ref(act),'actual_root_source53_native_result':ref(native),'source53_changed_keys_outside_module_scope':n['changed_text_keys'],'old_proof_metadata_exact':len(old['proof_files']),'proof_and_review_bodies_times_preserved':True,'installed25_owner_sha256':{p:H(p)for p in ownerpaths},'all1156_selected25_sources_and_frozen_copies_exact':True,'old31_frozen_assets_exact':True,'current30_unchanged_assets_exact':True,'coverage_complete':False,'live_owner_assets_mutated':False}
put(I,identity);put(C,out);print(json.dumps({'candidate':ref(C),'identity_binding':ref(I),'unchanged_owned_exercises':217,'unchanged_owned_material_units':4977,'old_proof_metadata_exact':len(old['proof_files'])}))
