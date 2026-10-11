"""Close the new identity-only offer after an independent explicit mapping peer."""
from pathlib import Path
from datetime import datetime,timezone
import argparse,copy,hashlib,json
R=Path(__file__).resolve().parents[2];B='book/coverage/checks/foundations-future26/source53'
def H(p):return hashlib.sha256((R/p).read_bytes()).hexdigest()
def J(p):return json.loads((R/p).read_text())
def ref(p):return {'file':p,'sha256':H(p)}
def safe(p):assert not Path(p).is_absolute() and '..' not in Path(p).parts and p.startswith('book/coverage/checks/')
def zero(d):
 ks=[k for k in ['exit_code','actual_exit_code'] if k in d];assert ks and all(type(d[k]) is int and d[k]==0 for k in ks)
def main():
 a=argparse.ArgumentParser();a.add_argument('--independent-peer',required=True);a.add_argument('--peer-sha256',required=True);args=a.parse_args();safe(args.independent_peer);assert H(args.independent_peer)==args.peer_sha256;peer=J(args.independent_peer);assert 'passed' in peer['status'] and peer['errors']==[]
 draft=B+'/foundations-audit26-candidate-source53-additions-draft-with-actual-v1.json';assert H(draft)=='1ee9addeeee1fcbdaf9fc50814dfebc878dae220076312690502177877b892a3';d=J(draft);identity=d['current53_identity_rebase'];oldref=identity['original_source52_final_offer'];assert H(oldref['file'])==oldref['sha256']=='d516611266b1781b23fb1d0d7bfa5365e18d9f9306002b5cd5245b3c5fe679a9';old=J(oldref['file']);assert H(d['mapped_ledger'])==d['mapped_ledger_sha256']=='60b1ebaa5d44b3e371466d89cc9af68572ccdc069127504940a5c6c7ecd48b3a'
 assert peer['candidate_ledger']==ref(d['mapped_ledger']) and peer['reviewed_offer']==ref(draft) and peer['original_source52_reviewed_offer']==oldref
 candidate=J(d['mapped_ledger']);reverse=copy.deepcopy(candidate);reverse.pop('current53_owner_identity');assert reverse==J(old['mapped_ledger']);inverse=copy.deepcopy(d);inverse.pop('current53_identity_rebase');inverse.update(identity['original_source52_outer_fields']);inverse['additional_frozen_inputs']=identity['original_additional_frozen_inputs'];assert inverse==old
 actual=J(d['actual_builder_record']);zero(actual);assert H(actual['log'])==actual['log_sha256'];assert actual['helper']==d['current_owner_builder'] and actual['helper_sha256_before']==actual['helper_sha256_after']==d['current_owner_builder_sha256'];assert H(d['current_inventory'])==H('book/coverage/inventory.json')==d['current_inventory_sha256']=='4b1e657eb61234a6d2e2a3a3ea6a0b11986c01d7d1c7cb5ba2dd5452d1fe29be'
 for p,h in d['additional_frozen_inputs'].items():assert H(p)==h
 out=copy.deepcopy(d);out['current53_identity_rebase']['original_source52_outer_fields']['status']=old['status'];out['status']='reviewed_isolated_source53_identity_foundation26_candidate_ready_for_root_selection';out['current53_identity_rebase']['independent_source53_identity_peer_pending']=False;out['current53_identity_rebase']['independent_source53_identity_peer']=ref(args.independent_peer);out['current53_identity_rebase']['identity_finalized_at_utc']=datetime.now(timezone.utc).isoformat();out['current53_identity_rebase']['identity_finalizer']=ref(str(Path(__file__).relative_to(R)));out['current53_identity_rebase']['draft_with_actual']=ref(draft)
 closure=peer['closed_evidence_sha256'];assert isinstance(closure,dict)
 for p,h in closure.items():safe(p);assert H(p)==h;out['additional_frozen_inputs'][p]=h
 out['additional_frozen_inputs'].update({p:H(p) for p in [args.independent_peer,draft,str(Path(__file__).relative_to(R))]})
 f=B+'/foundations-audit26-candidate-source53-additions-v1-reviewed.json';assert not (R/f).exists();(R/f).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'status':'passed_actual_isolated_source53_identity_offer_finalization','final_offer':ref(f),'candidate':ref(d['mapped_ledger']),'new_sources':2,'public_exports':15,'whole_material_units':3}))
if __name__=='__main__':main()
