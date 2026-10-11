"""Prepare a new isolated Applied23 identity candidate; never write live ledgers."""
from pathlib import Path
from datetime import datetime,timezone
import copy,json,hashlib,sys
ROOT=Path(__file__).resolve().parents[2]
BASE='book/coverage/checks/applied-future23/source51'
H=lambda n:hashlib.sha256((ROOT/n).read_bytes()).hexdigest()
read=lambda n:json.loads((ROOT/n).read_text())
ref=lambda n:{'file':n,'sha256':H(n)}
def write(n,v):
 p=ROOT/n;assert not p.exists(),n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(v,indent=2,ensure_ascii=False)+'\n')
def main():
 assert len(sys.argv)==2 and len(sys.argv[1])==64
 newinv='book/coverage/inventory-after-correction51.json';assert H(newinv)==sys.argv[1]==H('book/coverage/inventory.json')
 oldinv='book/coverage/inventory-after-correction48.json';a,b=read(oldinv),read(newinv)
 ledger='book/coverage/applied.json';promotions='book/coverage/applied-promotions.json'
 assert H(ledger)=='0ee60f1f224d01f443a762e0427d4527d6bd9b1d3ae5ed1d893c67750e331d20'
 assert H(promotions)=='850899f6469b10201e219b0ab3eb37f3f660488ab35ea6c64025dac8ada1ca44'
 old,oldp=read(ledger),read(promotions);scope=set(old['scope_pages']);assert len(scope)==3
 for p,sha in old['source_sha256'].items():assert H(p)==sha==a['source_sha256'][p]==b['source_sha256'][p]
 entire={}
 for kind,count in [('exercises',128),('material_source_units',2059)]:
  aa={r['key']:r for r in a[kind] if r['source'] in scope};bb={r['key']:r for r in b[kind] if r['source'] in scope};assert aa==bb and len(aa)==count
  entire[kind]=list(bb.values())
 assert len(old['exercises'])==128 and sum(len(e['claims']) for e in old['exercises'])==468
 assert len(old['proof_files'])==298
 manifest='reports/full-coverage/checkpoint-22-manifest.json';m=read(manifest);assert H(manifest)=='c8e4ce87ceceed0092e0593d4b6d5fed1340bc151af9aa2aaeb6e07f220413bb' and len(m['proof_files'])==1113
 for p,r in m['proof_files'].items():assert H(p)==r['sha256']
 for p,sha in old['proof_files'].items():assert H(p)==sha
 extras={p:sha for p,sha in old['proof_files'].items() if p not in m['proof_files']}
 assert set(extras)=={'verification/lean/SafeLearning/CompleteAppliedBinaryTemperaturePrecision.lean','verification/lean/SafeLearning/CompleteAppliedBinaryVariationalPrecision.lean','verification/lean/SafeLearning/CompleteAppliedConformalCalibrationOnly.lean'}
 history=[]
 for p in [ledger,promotions,'book/coverage/checks/future22-core/applied-audit22-installed-source48-interface-v1.json','book/coverage/build_applied22_candidate_source48_v3.py']:
  target=BASE+'/baseline22-unpruned-working/'+Path(p).name;q=ROOT/target;assert not q.exists();q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes((ROOT/p).read_bytes());assert H(p)==H(target);history.append({'original':ref(p),'byte_exact_copy':ref(target)})
 side=BASE+'/unchanged-owned-literal-identity-v1.json'
 write(side,{'status':'exact_source48_to51_unchanged_applied_owned_entire_literal_records','created_at_utc':datetime.now(timezone.utc).isoformat(),'historical_inventory':ref(oldinv),'current_inventory':ref(newinv),'intermediate_inventory49':ref('book/coverage/inventory-after-correction49.json'),'intermediate_inventory50':ref('book/coverage/inventory-after-correction50.json'),'owned_source_sha256':old['source_sha256'],'entire_owned_inventory_records':entire,'baseline22_unpruned_working_history':history,'unreferenced_unselected_metadata_preserved_exactly':extras,'old_review_bodies_times_hypotheses_and_declarations_unchanged':True,'limits':['Only owner literal identity. Root CMDP49/51 and Lyapunov50 changes remain outside these three owned pages.','The three unreferenced proof metadata rows remain exact historical working data; no new verified coverage or selection is inferred from them.']})
 identity={'inventory':newinv,'inventory_sha256':H(newinv),'identity_sidecar':ref(side),'original_unpruned_working22_ledger':history[0],'original_unpruned_working22_promotions':history[1],'scope':'All128 exercises/468 claims/1954 material-claim bodies/2059 physical units and298 proof metadata rows unchanged. No fresh math/source/proof promotion.'}
 out=copy.deepcopy(old);outp=copy.deepcopy(oldp);out['current51_owner_identity']=identity;outp['current51_owner_identity']=identity
 reverse=copy.deepcopy(out);reversep=copy.deepcopy(outp);del reverse['current51_owner_identity'];del reversep['current51_owner_identity'];assert reverse==old and reversep==oldp
 candidate=BASE+'/applied23-candidate-source51-identity-v1.json';candidatep=BASE+'/applied-promotions23-candidate-source51-identity-v1.json';write(candidate,out);write(candidatep,outp)
 integrity=BASE+'/identity-candidate-integrity-v1.json';write(integrity,{'status':'passed_exact_isolated_applied23_source51_identity_preparation','checked_at_utc':datetime.now(timezone.utc).isoformat(),'errors':[],'candidate':ref(candidate),'candidate_promotions':ref(candidatep),'identity_sidecar':ref(side),'original_unpruned_working22':history[:2],'exact_inverse_restores_entire_unpruned_working22_bodies':True,'counts':{'owned_exercises':128,'exercise_claims':468,'material_claim_records':1954,'owned_physical_units':2059,'proof_metadata_rows_preserved':298,'new_sources':0,'new_exports':0,'new_whole_decisions':0,'new_material_decisions':0},'unreferenced_metadata_three_exact':extras,'all1113_selected22_sources_exact':True,'no_live_owner_write':True,'scope':'Observed Python isolated identity preparation, not a new semantic review, Lean build, live global validation or aggregate23 audit.'})
 offer=BASE+'/applied-audit23-candidate-source51-additions-v1.json';write(offer,{'schema_version':1,'status':'isolated_applied23_current51_unchanged_owner_identity_ready_for_independent_mechanics','created_at_utc':datetime.now(timezone.utc).isoformat(),'inventory':newinv,'inventory_sha256':H(newinv),'base_selection':manifest,'base_selection_sha256':H(manifest),'mapped_ledger':candidate,'mapped_ledger_sha256':H(candidate),'mapped_promotions':candidatep,'mapped_promotions_sha256':H(candidatep),'candidate_builder':str(Path(__file__).relative_to(ROOT)),'candidate_builder_sha256':H(str(Path(__file__).relative_to(ROOT))),'identity_sidecar':ref(side),'identity_integrity':ref(integrity),'baseline22_unpruned_working_history':history,'source_sha256':old['source_sha256'],'proof_files':{},'new_actual_paired_records':[],'new_material_keys':[],'required_evidence_artifacts_sha256':{side:H(side),integrity:H(integrity),**{r['byte_exact_copy']['file']:r['byte_exact_copy']['sha256'] for r in history}},'counts':{'unchanged_whole_exercises':128,'unchanged_exercise_claims':468,'unchanged_material_claim_records':1954,'unchanged_owned_physical_units':2059,'preserved_unpruned_proof_metadata_rows':298,'new_proof_sources':0,'new_public_exports':0,'new_whole_exercises':0,'new_material_units':0},'coverage_complete':False,'limits':['Identity-only candidate preserves old full review bodies/times and explicit original source48/49/50 histories.','Five new Lyapunov future23 sources43 exports are explicitly supplied for Core selection/mapping; no Applied exercise promotions or filename-based ownership inference.','The unreferenced metadata three remain historical unselected entries; this offer requests no new proof selection.','Current22 live ledger/promotions remain byte-identical. The independent mechanics peer and observed actual preparation execution are separate immutable supplements.']})
 assert H(ledger)==history[0]['original']['sha256'] and H(promotions)==history[1]['original']['sha256']
 print(json.dumps({'offer':ref(offer),'candidate':ref(candidate),'candidate_promotions':ref(candidatep),'identity':ref(side)}))
if __name__=='__main__':main()
