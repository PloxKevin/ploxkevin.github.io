from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,copy
R=Path(__file__).resolve().parents[5];B='book/coverage/checks/modules-future24/source52'
H=lambda n:hashlib.sha256((R/n).read_bytes()).hexdigest();J=lambda n:json.loads((R/n).read_text());ref=lambda n:{'file':n,'sha256':H(n)}
def main():
 oldname=B+'/modules-audit24-candidate-source52-additions-draft-v1.json';assert H(oldname)=='f63887128bb965d81e532bcd1bed5b47ea201edd4691fe70ef859b7796fc6a35'
 old=J(oldname);o=copy.deepcopy(old)
 names=['/tmp/module24-source52-candidate-independent-applied-confirmation-v1.json','/tmp/check-module24-source52-candidate-independent-applied-v1.py',
 '/tmp/module24-source52-candidate-independent-applied-actual-v1.json','/tmp/module24-source52-candidate-independent-applied-actual-v1.log','/tmp/run-module24-source52-candidate-independent-applied-actual-v1.py']
 aliases={}
 for n in names:
  p=Path(n);q=R/B/'original-independent-source52-final-candidate-peer'/p.name;q.parent.mkdir(parents=True,exist_ok=True);assert not q.exists();q.write_bytes(p.read_bytes());aliases[n]=ref(str(q.relative_to(R)))
 peer=J(aliases[names[0]]['file']);assert aliases[names[0]]['sha256']=='35836aad2d05a27df19dee30f6fa737c88dfc548f6d9eb251dfdfe061874f31c';assert 'passed' in peer['status'] and peer['errors']==[]
 assert J(aliases[names[2]]['file'])['actual_exit_code']==0
 guard=J(old['candidate_binding_integrity']['file'])
 for n,h in guard['protected_live_owner_sha256'].items():assert H(n)==h
 assert H(old['module_ledger'])==old['module_ledger_sha256']
 for n,h in old['required_evidence_artifacts_sha256'].items():assert H(n)==h
 adds={r['file']:r['sha256'] for r in aliases.values()}
 for n in [oldname,B+'/prepare-modules24-source52-offer-v1.py',B+'/prepare-modules24-source52-offer-v2.py',B+'/modules24-source52-offer-preparation-actual-v1.json',B+'/modules24-source52-offer-preparation-actual-v1.log',B+'/modules24-source52-offer-preparation-actual-v2.json',B+'/modules24-source52-offer-preparation-actual-v2.log']:adds[n]=H(n)
 o['status']='independently_reviewed_isolated_source52_module24_static_tanh_component_offer'
 o['independent_final_candidate_mapping_peer_pending']=False;o['independent_final_candidate_mapping_peer']=aliases[names[0]]
 o['independent_final_candidate_mapping_actual_execution']=aliases[names[2]];o['independent_final_candidate_mapping_raw_log']=aliases[names[3]]
 o['entire_original_final_candidate_mechanics_body_and_time']=peer;o['original_source52_candidate_offer_before_peer']=ref(oldname)
 o['final_candidate_mapping_original_byte_aliases']=aliases;o['source52_mapping_peer_added_at_utc']=datetime.now(timezone.utc).isoformat()
 o['required_evidence_artifacts_sha256'].update(adds)
 rev=copy.deepcopy(o)
 for k in ['independent_final_candidate_mapping_peer','independent_final_candidate_mapping_actual_execution','independent_final_candidate_mapping_raw_log','entire_original_final_candidate_mechanics_body_and_time','original_source52_candidate_offer_before_peer','final_candidate_mapping_original_byte_aliases','source52_mapping_peer_added_at_utc']:rev.pop(k)
 rev['status']=old['status'];rev['independent_final_candidate_mapping_peer_pending']=True
 for n in adds:rev['required_evidence_artifacts_sha256'].pop(n)
 assert rev==old
 target=B+'/modules-audit24-candidate-source52-additions-v1-reviewed.json';p=R/target;assert not p.exists();p.write_text(json.dumps(o,indent=2,ensure_ascii=False)+'\n')
 for n,h in guard['protected_live_owner_sha256'].items():assert H(n)==h
 print(json.dumps({'final_reviewed_offer':ref(target),'candidate':ref(old['module_ledger']),'independent_peer':aliases[names[0]],'required_closed_artifacts':len(o['required_evidence_artifacts_sha256']),'exact_reverse_to_original_draft':True,'live_owner_bytes_unchanged':True}))
if __name__=='__main__':main()
