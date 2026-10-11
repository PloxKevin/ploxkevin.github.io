"""Copy the completed independent mechanics peer and finalize a separate offer."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,copy
R=Path(__file__).resolve().parents[5];B='book/coverage/checks/modules-future24/source51'
H=lambda n:hashlib.sha256((R/n).read_bytes()).hexdigest()
J=lambda n:json.loads((R/n).read_text())
ref=lambda n:{'file':n,'sha256':H(n)}
def main():
 oldname=B+'/modules-audit24-candidate-source51-additions-draft-v1.json'
 assert H(oldname)=='9be35fa54142f1a31fedb8f02af27dcfed18625fb6403bc39ca92d1867883979'
 old=J(oldname);offer=copy.deepcopy(old)
 files=['/tmp/module24-tanh-candidate-independent-applied-confirmation-v1.json',
  '/tmp/check-module24-tanh-candidate-independent-applied-v1.py',
  '/tmp/module24-tanh-candidate-independent-applied-actual-v1.json',
  '/tmp/module24-tanh-candidate-independent-applied-actual-v1.log',
  '/tmp/run-module24-tanh-candidate-independent-applied-actual-v1.py']
 aliases={}
 for n in files:
  p=Path(n);q=R/B/'original-independent-final-candidate-peer'/p.name;q.parent.mkdir(parents=True,exist_ok=True)
  assert not q.exists();q.write_bytes(p.read_bytes())
  aliases[n]=ref(str(q.relative_to(R)))
 peerref=aliases[files[0]];peer=J(peerref['file'])
 assert peerref['sha256']=='18518ea66c7501f88d2f656dd2069c5245b18471e01953e41d3f425079b19932'
 assert 'passed' in peer['status'] and peer['errors']==[]
 actual=J(aliases[files[2]]['file']);assert actual['actual_exit_code']==0
 assert H(old['module_ledger'])==old['module_ledger_sha256']=='27a36bb3e324ce88a2122625b580af4bfde662b9ac50bce78e95850b2bbf18d2'
 for n,h in old['required_evidence_artifacts_sha256'].items():assert H(n)==h,n
 inp=J(old['candidate_input_bindings']['file'])
 for n,h in inp['protected_owner_inventory_and31_asset_sha256'].items():assert H(n)==h,n
 additions={a['file']:a['sha256'] for a in aliases.values()}
 for n in [oldname,B+'/prepare-modules24-candidate-offer-v1.py',
  B+'/modules24-candidate-offer-preparation-actual-v1.json',B+'/modules24-candidate-offer-preparation-actual-v1.log']:
  additions[n]=H(n)
 offer['status']='independently_reviewed_isolated_source51_module24_static_tanh_component_offer'
 offer['independent_final_candidate_mapping_peer_pending']=False
 offer['independent_final_candidate_mapping_peer']=peerref
 offer['independent_final_candidate_mapping_actual_execution']=aliases[files[2]]
 offer['independent_final_candidate_mapping_raw_log']=aliases[files[3]]
 offer['entire_original_final_candidate_mechanics_body_and_time']=peer
 offer['original_candidate_offer_before_peer']=ref(oldname)
 offer['final_candidate_mapping_original_byte_aliases']=aliases
 offer['mapping_peer_added_at_utc']=datetime.now(timezone.utc).isoformat()
 offer['required_evidence_artifacts_sha256'].update(additions)
 target=B+'/modules-audit24-candidate-source51-additions-v1-reviewed.json';p=R/target;assert not p.exists()
 p.write_text(json.dumps(offer,indent=2,ensure_ascii=False)+'\n')
 restored=copy.deepcopy(offer)
 for k in ['independent_final_candidate_mapping_peer','independent_final_candidate_mapping_actual_execution',
  'independent_final_candidate_mapping_raw_log','entire_original_final_candidate_mechanics_body_and_time',
  'original_candidate_offer_before_peer','final_candidate_mapping_original_byte_aliases','mapping_peer_added_at_utc']:
  restored.pop(k)
 restored['status']=old['status'];restored['independent_final_candidate_mapping_peer_pending']=True
 for n in additions:restored['required_evidence_artifacts_sha256'].pop(n)
 assert restored==old
 for n,h in inp['protected_owner_inventory_and31_asset_sha256'].items():assert H(n)==h,n
 print(json.dumps({'final_reviewed_offer':ref(target),'candidate':ref(old['module_ledger']),
  'independent_peer':peerref,'required_closed_artifacts':len(offer['required_evidence_artifacts_sha256']),
  'exact_reverse_to_original_draft':True,'current51_live_owner_bytes_unchanged':True}))
if __name__=='__main__':main()
