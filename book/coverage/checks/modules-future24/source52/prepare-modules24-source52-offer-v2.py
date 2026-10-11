"""Bind closed actual source52 candidate evidence; preserve complete source51 offer."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,copy
R=Path(__file__).resolve().parents[5];B='book/coverage/checks/modules-future24/source52';O='book/coverage/checks/modules-future24/source51'
H=lambda n:hashlib.sha256((R/n).read_bytes()).hexdigest()
J=lambda n:json.loads((R/n).read_text())
ref=lambda n:{'file':n,'sha256':H(n)}
def main():
 oldname=O+'/modules-audit24-candidate-source51-additions-v1-reviewed.json'
 assert H(oldname)=='95ee6d8d90056a5d0b02c6586b6a613a2637a8228cb1047608660907371b4022'
 old=J(oldname);offer=copy.deepcopy(old)
 candidate=B+'/modules24-candidate-source52-v1.json';cand=J(candidate)
 assert H(candidate)=='1d4395c5b7cb9dc18217b0c4236a04868f67a2445d0ffed18f3a77215d3b2c90'
 inv='book/coverage/inventory-after-correction52.json'
 assert H(inv)==H('book/coverage/inventory.json')=='38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
 builder='book/coverage/build_modules24_candidate_source52_v1.py';actual=B+'/modules24-candidate-builder-actual-execution-v1.json';a=J(actual)
 assert a['actual_exit_code']==0 and a['execution_kind']=='actual_isolated_candidate_preparation'
 assert H(builder)==a['actual_helper_sha256_before']==a['actual_helper_sha256_after']
 assert H(a['raw_log'])==a['raw_log_sha256']
 guard=B+'/modules24-source52-candidate-integrity-v1.json';g=J(guard)
 assert g['exact_reverse_recovers_entire_original_source51_candidate'] and not g['whole_source52_promotion']
 for n,h in g['protected_live_owner_sha256'].items():assert H(n)==h
 assert cand['proof_files']==J(old['module_ledger'])['proof_files']
 for n,h in old['required_evidence_artifacts_sha256'].items():assert H(n)==h,n
 offer.update(status='isolated_source52_module24_static_tanh_component_offer_requires_independent_fresh_literal_and_final_candidate_mechanics',
  current_inventory=inv,current_inventory_sha256=H(inv),module_ledger=candidate,module_ledger_sha256=H(candidate),
  module_builder=builder,module_builder_sha256=H(builder),actual_builder=ref(actual),actual_builder_raw_log=ref(a['raw_log']),
  candidate_binding_integrity=ref(guard),source_sha256=cand['source_sha256'],independent_final_candidate_mapping_peer_pending=True)
 peerfields=['independent_final_candidate_mapping_peer','independent_final_candidate_mapping_actual_execution','independent_final_candidate_mapping_raw_log',
  'entire_original_final_candidate_mechanics_body_and_time','original_candidate_offer_before_peer','final_candidate_mapping_original_byte_aliases','mapping_peer_added_at_utc']
 offer['original_source51_final_mapping_fields']={k:offer.pop(k) for k in peerfields}
 offer['original_source51_reviewed_offer']=ref(oldname)
 offer['entire_original_source51_reviewed_offer_body_and_time']=old
 offer['source52_prepared_at_utc']=datetime.now(timezone.utc).isoformat()
 offer['source52_unchanged_literal_identity']=ref(B+'/unchanged-owned-literal-identity-v1.json')
 offer['source52_fresh_partial_literal_binding']=ref(B+'/tanh24-current52-fresh-partial-literal-binding-v1.json')
 offer['original_source51_scope_limits']=offer['scope_limits']
 offer['scope_limits']=[
  'All original source51 mathematical component decisions, proof/compiler identities, hypotheses, reasons and review times are unchanged.',
  'Source52 corrects exactly exercise20 and material1260/1262 text while current1258 whole correspondence and twelve static groups remain valid.',
  'The six false exact decimals and invalid-premise wording were corrected by the independently approved proposal; that wording approval does not promote whole answers(b)/(c) or the exercise.',
  'General repeated-function/common-local-bound correspondence and temporal method/finite-horizon scope remain outside this static pack; current question1254 and answers1260/1262 retain explicit whole pending gaps.',
  'No future25 temporal source, live installation, new Lean compile, aggregate audit or publication is claimed by this isolated preparation.']
 additions=[oldname,builder,actual,a['raw_log'],guard,B+'/unchanged-owned-literal-identity-v1.json',B+'/tanh24-current52-fresh-partial-literal-binding-v1.json',candidate,
  'book/coverage/checks/future24-nn-source52/approved-source52-proposal-original-byte-alias-catalog-v1.json',
  'reports/full-coverage/source52-apply-execution-v1.json','reports/full-coverage/source52-apply-execution-v1.log',
  'book/coverage/checks/root-source-batch52/postwrite-source-integrity-v1.json',inv]
 catalog=J(additions[8]);additions.extend(x['file'] for x in catalog['original_absolute_path_byte_aliases'].values())
 for n in additions:offer['required_evidence_artifacts_sha256'][n]=H(n)
 target=B+'/modules-audit24-candidate-source52-additions-draft-v1.json';p=R/target;assert not p.exists();p.write_text(json.dumps(offer,indent=2,ensure_ascii=False)+'\n')
 assert offer['proof_files']==old['proof_files'] and offer['counts']==old['counts']
 for n,h in g['protected_live_owner_sha256'].items():assert H(n)==h
 print(json.dumps({'draft_offer':ref(target),'candidate':ref(candidate),'fresh_partial_literal_binding':offer['source52_fresh_partial_literal_binding'],
 'closed_artifacts':len(offer['required_evidence_artifacts_sha256']),'original_source51_body_and_times_retained':True,'whole_source52_promotion':False}))
if __name__=='__main__':main()
