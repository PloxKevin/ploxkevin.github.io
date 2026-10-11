"""Prepare a reversible isolated inventory identity overlay; no live writes."""
from pathlib import Path
from datetime import datetime,timezone
import argparse,hashlib,json,copy
R=Path(__file__).resolve().parents[2]
BASE='book/coverage/checks/foundations-future26/source53'
OLD='book/coverage/checks/foundations-future26/source52/foundations-audit26-candidate-source52-additions-v1-reviewed.json'
OLD_SHA='d516611266b1781b23fb1d0d7bfa5365e18d9f9306002b5cd5245b3c5fe679a9'
OLDC='book/coverage/checks/foundations-future26/source52/foundations26-candidate-source52-v1.json'
OLDC_SHA='5930b0852eeee516238861f15f38c67f7c2719b2a3a03ec2676f862bf64048ef'
I52='book/coverage/inventory-after-correction52.json';I53='book/coverage/inventory-after-correction53.json'
I52_SHA='38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
I53_SHA='4b1e657eb61234a6d2e2a3a3ea6a0b11986c01d7d1c7cb5ba2dd5452d1fe29be'
OWNERS=['book/coverage/'+n+'.json' for n in ['core','foundations','applied','modules','applied-promotions']]
def H(p):return hashlib.sha256((R/p).read_bytes()).hexdigest()
def J(p):return json.loads((R/p).read_text())
def ref(p):return {'file':p,'sha256':H(p)}
def zero(d):
 ks=[k for k in ['actual_exit_code','exit_code'] if k in d];assert ks and all(type(d[k]) is int and d[k]==0 for k in ks)
def write(p,d):
 f=R/p;assert not f.exists(),p;f.parent.mkdir(parents=True,exist_ok=True)
 with f.open('x') as s:s.write(json.dumps(d,indent=2)+'\n')
def main():
 a=argparse.ArgumentParser();a.add_argument('--root-authorized-source53-identity-rebase',action='store_true',required=True);a.add_argument('--inventory-sha256',required=True);args=a.parse_args();assert args.root_authorized_source53_identity_rebase
 assert H(I53)==H('book/coverage/inventory.json')==args.inventory_sha256==I53_SHA and H(I52)==I52_SHA
 assert H(OLD)==OLD_SHA and H(OLDC)==OLDC_SHA
 appp='reports/full-coverage/source53-correction-application-v1.json';assert H(appp)=='fbc298db9520fb9eae49997fe7955062b1bb373605a3af81f40801fd317da548';app=J(appp);assert 'passed' in app['status'] and app['selected25_proof_sources_unchanged']==1156 and app['five_installed25_owner_ledgers_unchanged'] is True
 exp='reports/full-coverage/source53-correction-application-execution-v1.json';ex=J(exp);zero(ex);assert H(ex['log'])==ex['log_sha256'];assert ex['helper_sha256_before']==ex['helper_sha256_after']=={'book/coverage/checks/root_apply_source53_v2.py':'20d5933637d720bdd263838f2af361425d4aa730e6ad33d721e61f5c625d481e'};assert app['inventory_after']==ref(I53)
 old,offer=J(OLDC),J(OLD);assert offer['mapped_ledger']==OLDC and offer['mapped_ledger_sha256']==OLDC_SHA and offer['new_proof_file_count']==2 and offer['new_theorem_or_lemma_count']==15
 assert offer['independent_final_candidate_mapping_peer_pending'] is False and offer['actual_builder_record_pending'] is False
 manifestp='reports/full-coverage/checkpoint-25-manifest.json';manifest=J(manifestp);assert len(manifest['proof_files'])==1156
 held={p:manifest['working_inputs_sha256'][p] for p in OWNERS}
 for p,h in held.items():assert H(p)==h
 protected={p:r['sha256'] for p,r in manifest['proof_files'].items()}
 for p,h in protected.items():assert H(p)==H('reports/full-coverage/checkpoint-25/'+p)==h
 assets={p:h for p,h in manifest['working_inputs_sha256'].items() if p.startswith('SafeLearning/')};assert len(assets)==31
 for p,h in assets.items():
  assert H('reports/full-coverage/checkpoint-25/'+p)==h
  if p==app['source_after']['file']:assert H(p)==app['source_after']['sha256'] and h==app['source_before']['sha256']
  else:assert H(p)==h
 before,after=J(I52),J(I53);assert before['counts']==after['counts'];scope=set(old['scope_pages']);assert len(scope)==3
 records={}
 for kind,n in [('exercises',119),('material_source_units',1756)]:
  x=[u for u in before[kind] if u['source'] in scope];y=[u for u in after[kind] if u['source'] in scope];assert x==y and len(x)==n;records[kind]=y
 for p,h in old['source_sha256'].items():
  assert H(p)==h
  if p.startswith('SafeLearning/'):assert before['source_sha256'][p]==after['source_sha256'][p]==h
  else:assert J('book/coverage/foundations.json')['source_sha256'][p]==h
 assert len(old['proof_files'])==247 and set(old['proof_files'])==set(old['proof_sha256'])
 for p,h in old['proof_sha256'].items():assert H(p)==h
 evidence=copy.deepcopy(offer['additional_frozen_inputs'])
 for p,row in offer['proof_files'].items():assert H(p)==row['sha256'];evidence.update(row['evidence_sha256'])
 for field in ['exact_source_reviews_sha256','actual_canonical_execution_records_sha256','canonical_readiness_sha256']:evidence.update(offer[field])
 for p,h in evidence.items():assert H(p)==h
 assert len(offer['actual_canonical_execution_records_sha256'])==4
 for p in offer['actual_canonical_execution_records_sha256']:
  d=J(p);zero(d);assert H(d['source'])==d['source_sha256_before']==d['source_sha256_after'];hs=[d[k] for k in ['log_sha256','raw_log_sha256'] if k in d];assert hs and all(h==H(d['log']) for h in hs)
 side=BASE+'/foundations26-source52-to53-unchanged-entire-owned-records-v1.json';candidate=BASE+'/foundations26-candidate-source53-identity-v1.json';integrity=BASE+'/source53-identity-preparation-integrity-v1.json';draft=BASE+'/foundations-audit26-candidate-source53-additions-draft-v1.json';assert not any((R/p).exists() for p in [side,candidate,integrity,draft])
 stamp=datetime.now(timezone.utc).isoformat();identity={'status':'exact_source52_to53_unchanged_entire_foundation26_records_passed','errors':[],'prepared_at_utc':stamp,'historical_source52_inventory':ref(I52),'current_source53_inventory':ref(I53),'original_source52_final_offer':ref(OLD),'original_source52_candidate':ref(OLDC),'original_exact_three_whole_literal_interface':{'file':offer['material26_exact_interface_binding'],'sha256':offer['material26_exact_interface_binding_sha256']},'entire_owned_inventory_records':records,'owned_source_sha256':old['source_sha256'],'actual_source53_application':ref(appp),'actual_source53_application_execution':ref(exp),'baseline25_manifest':ref(manifestp),'five_installed25_owner_sha256':held,'counts':{'entire_exercises':119,'entire_material_units':1756,'whole_new_units_retained':3,'new_sources_retained':2,'public_exports_retained':15,'actual_canonical_records_retained':4},'all_original_math_bodies_hypotheses_decisions_times_and_compiler_records_unchanged':True,'scope':'Only the global inventory identity changes; all three owned pages and all119/1756 entire owned records are unchanged. Original source52 full decisions and actual pairs remain historical exact. No mathematical redecision, compiler rerun, live installation or aggregate26 result.'};write(side,identity)
 current=copy.deepcopy(old);assert 'current53_owner_identity' not in current;current['current53_owner_identity']={'inventory':ref(I53),'identity_sidecar':ref(side),'original_source52_reviewed_offer':ref(OLD),'scope':'Active Source53 identity. Every original source52 field, material/body/claim/source and time remains exact.'};inverse=copy.deepcopy(current);inverse.pop('current53_owner_identity');assert inverse==old;write(candidate,current)
 write(integrity,{'status':'passed_actual_isolated_foundation26_source53_identity_preparation','errors':[],'checked_at_utc':stamp,'candidate_ledger':ref(candidate),'identity_sidecar':ref(side),'original_source52_reviewed_offer':ref(OLD),'exact_inverse_restores_entire_original_candidate':True,'all119_and1756_entire_inventory_records_exact':True,'all1156_root_and_frozen25_sources_exact':True,'all247_candidate_sources_exact':True,'all31_frozen25_assets_and_authorized_current53_delta_exact':True,'all_four_original_canonical0_records_and_raw_logs_exact':True,'all_five_installed25_owner_sha256':held,'scope':'Actual isolated identity preparation only; no compiler or production coverage/execution inference.'})
 out=copy.deepcopy(offer);changes={'status':'isolated_source53_identity_foundation26_candidate_pending_actual_and_independent_identity_peer','mapped_ledger':candidate,'mapped_ledger_sha256':H(candidate),'current_inventory':I53,'current_inventory_sha256':I53_SHA,'current_owner_builder':str(Path(__file__).relative_to(R)),'current_owner_builder_sha256':H(str(Path(__file__).relative_to(R)))};originals={k:offer[k] for k in changes};out.update(changes);out['current53_identity_rebase']={'prepared_at_utc':stamp,'identity_sidecar':ref(side),'integrity':ref(integrity),'original_source52_final_offer':ref(OLD),'original_source52_outer_fields':originals,'actual_identity_builder_record_pending':True,'independent_source53_identity_peer_pending':True,'original_source52_final_math_and_candidate_peers_remain_exact':True};inverse=copy.deepcopy(out);inverse.pop('current53_identity_rebase');inverse.update(originals);assert inverse==offer;out['additional_frozen_inputs']=dict(out['additional_frozen_inputs']);out['additional_frozen_inputs'].update({p:H(p) for p in [OLD,OLDC,I52,I53,side,integrity,appp,exp,ex['log'],str(Path(__file__).relative_to(R))]});out['current53_identity_rebase']['original_additional_frozen_inputs']=offer['additional_frozen_inputs'];write(draft,out)
 for p,h in held.items():assert H(p)==h
 for p,h in protected.items():assert H(p)==h
 for p,h in evidence.items():assert H(p)==h
 assert H(OLD)==OLD_SHA and H(OLDC)==OLDC_SHA and H(I53)==H('book/coverage/inventory.json')==I53_SHA
 print(json.dumps({'status':'passed_actual_isolated_foundation26_source53_identity_preparation','candidate':ref(candidate),'sidecar':ref(side),'draft_offer':ref(draft),'whole_units':3,'public_exports':15}))
if __name__=='__main__':main()
