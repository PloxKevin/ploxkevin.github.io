"""Close an isolated reviewed offer; preserve all original evidence byte-for-byte."""
from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json
R=Path(__file__).resolve().parents[3]
BASE='book/coverage/checks/modules-future26/source53'
DRAFT=BASE+'/modules-audit26-candidate-source53-additions-draft-v1.json'
PEER=Path('/tmp/module26-combined-source53-final-candidate-independent-applied-review-v3.json')
OUT=BASE+'/modules-audit26-candidate-source53-additions-v1-reviewed.json'
def P(p):return Path(p) if Path(p).is_absolute() else R/p
def H(p):return hashlib.sha256(P(p).read_bytes()).hexdigest()
def J(p):return json.loads(P(p).read_text())
def ref(p):return {'file':str(p),'sha256':H(p)}
def zero(d):
 keys=[k for k in ('actual_exit_code','exit_code') if k in d];assert keys and all(type(d[k])is int and d[k]==0 for k in keys)
def main():
 assert H(DRAFT)=='28d6ed6ca17028f20d69986d451f78c2734a737f4654a73536f9f2d5fb992119'
 assert H(PEER)=='c8949789a56ca2af36015b425519194d06bd489b1af61766b66ede6b6a31bc24'
 d=J(DRAFT);peer=J(PEER);assert 'passed' in peer['status'] and peer['errors']==[] and peer['offer']==ref(DRAFT)
 assert peer['candidate']=={'file':d['mapped_ledger'],'sha256':d['mapped_ledger_sha256']} and H(d['mapped_ledger'])==d['mapped_ledger_sha256']
 assert d['new_proof_file_count']==2 and d['new_theorem_or_lemma_count']==48 and len(d['fresh_whole_exercise_keys'])==2 and len(d['fresh_whole_material_unit_keys'])==9
 for p,h in d['required_evidence_artifacts_sha256'].items():assert H(p)==h
 original_paths={str(PEER)}
 def collect(o):
  if isinstance(o,dict):
   if isinstance(o.get('file'),str) and o['file'].startswith('/tmp/') and 'sha256'in o:
    assert H(o['file'])==o['sha256'];original_paths.add(o['file'])
   for v in o.values():collect(v)
  elif isinstance(o,list):
   for v in o:collect(v)
 collect(peer)
 for n in ['check-module26-combined-source53-final-candidate-independent-applied-v3.py','run-module26-combined-source53-final-candidate-independent-applied-v3.py','module26-combined-source53-final-candidate-independent-applied-actual-v3.json','module26-combined-source53-final-candidate-independent-applied-actual-v3.log']:original_paths.add('/tmp/'+n)
 actual=J('/tmp/module26-combined-source53-final-candidate-independent-applied-actual-v3.json');zero(actual)
 assert actual['helper_sha256_before']==actual['helper_sha256_after']==H('/tmp/check-module26-combined-source53-final-candidate-independent-applied-v3.py')
 raw=actual.get('raw_log',actual.get('log'));rh=actual.get('raw_log_sha256',actual.get('log_sha256'));assert H(raw)==rh
 aliases={}
 for p in sorted(original_paths):
  assert P(p).is_file();target=BASE+'/original-final-independent-applied-peer-v1/'+P(p).name;f=P(target);assert not f.exists();f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(P(p).read_bytes());assert H(target)==H(p);aliases[p]=ref(target)
 cpeer=aliases[str(PEER)]
 extras={DRAFT:H(DRAFT),str(Path(__file__).relative_to(R)):H(Path(__file__))}
 for row in aliases.values():extras[row['file']]=row['sha256']
 prep=BASE+'/modules26-source53-offer-preparation-actual-v1.json';pd=J(prep);zero(pd);assert H(pd['log'])==pd['log_sha256']
 for p in [prep,pd['log'],'book/coverage/checks/prepare_modules26_source53_candidate_offer_v2.py']:extras[p]=H(p)
 # Preserve the measured preparation runner through an explicit exact-byte alias.
 runner=pd['actual_runner'];runner_path=runner['file']if isinstance(runner,dict)else runner;target=BASE+'/original-final-independent-applied-peer-v1/'+P(runner_path).name
 if P(target).exists():assert H(target)==H(runner_path)
 else:P(target).write_bytes(P(runner_path).read_bytes())
 extras[target]=H(target)
 out=copy.deepcopy(d);old_status=out['status'];out['status']='passed_reviewed_isolated_source53_module26_two_wholes_nine_units_two_owned_sources48_exports'
 out['independent_final_candidate_mapping_peer_pending']=False
 out['final_independent_candidate_mapping_peer']=cpeer
 out['final_independent_peer_actual_execution']=aliases['/tmp/module26-combined-source53-final-candidate-independent-applied-actual-v3.json']
 out['final_reviewed_offer_binding']={'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'original_isolated_candidate_draft':ref(DRAFT),'original_status':old_status,'original_independent_pending':d['independent_final_candidate_mapping_peer_pending'],'original_additional_frozen_inputs':d['additional_frozen_inputs'],'original_required_evidence_artifacts_sha256':d['required_evidence_artifacts_sha256'],'entire_original_independent_peer_body_and_time':peer,'original_closed_byte_aliases':aliases,'actual_closed_offer_preparation':ref(prep),'scope':'Evidence-only isolated reviewed offer finalization. Original full mathematical decisions, times, original candidate builder executions and source53 reversible identity remain exact. No compiler, live installation or aggregate26 claim.'}
 out['additional_frozen_inputs']={**d['additional_frozen_inputs'],**extras};out['required_evidence_artifacts_sha256']={**d['required_evidence_artifacts_sha256'],**extras}
 inv=copy.deepcopy(out);bind=inv.pop('final_reviewed_offer_binding');inv.pop('final_independent_candidate_mapping_peer');inv.pop('final_independent_peer_actual_execution');inv['status']=bind['original_status'];inv['independent_final_candidate_mapping_peer_pending']=bind['original_independent_pending'];inv['additional_frozen_inputs']=bind['original_additional_frozen_inputs'];inv['required_evidence_artifacts_sha256']=bind['original_required_evidence_artifacts_sha256'];assert inv==d
 assert H('book/coverage/inventory.json')==d['current_inventory_sha256'];assert not P(OUT).exists();P(OUT).write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps({'status':'passed_actual_isolated_reviewed_offer_finalization','offer':ref(OUT),'candidate':ref(d['mapped_ledger']),'final_peer':cpeer,'original_closed_peer_files':len(aliases),'own_sources':2,'own_public_theorems':48,'cross_Applied_sources':1,'cross_Applied_theorems':8,'scope':'No live installation or aggregate26 claim.'}))
if __name__=='__main__':main()
