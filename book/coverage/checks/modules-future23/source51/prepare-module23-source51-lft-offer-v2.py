from pathlib import Path
from datetime import datetime,timezone
import copy,json,hashlib
R=Path('/home/oxrexkevin/SafetyBased');B=R/'book/coverage/checks/modules-future23/source51'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();J=lambda p:json.loads(Path(p).read_text());ref=lambda p:{'file':str(Path(p).relative_to(R)),'sha256':H(p)}
def archive(p):
 p=Path(p);q=B/p.name
 if q.exists():assert q.read_bytes()==p.read_bytes()
 else:q.write_bytes(p.read_bytes())
 return ref(q)
oldpath=B/'modules-audit23-candidate-source51-additions-v1-reviewed.json';assert H(oldpath)=='f60b6f4b1f9a49822ddd4a598f639024399886a3bbedcb059ea145bc037a090a';old=J(oldpath)
inputpath=B/'lft/lft-source51-input-bindings-v1.json';inp=J(inputpath);assert H(inputpath)=='ef9aa484215f8d5358de7968a851ba79d857b69157b7cd33cf6cbf7077c42c83'
candidate=B/'modules23-candidate-source51-lft-v2.json';assert H(candidate)=='448b83324829b136ef9745977e10f397086b6872f6d3141854d96504dfd53367';c=J(candidate)
binding=Path('/tmp/modules-lft23-canonical-source-original-full-peer-independent-foundations-binding-v1.json');assert H(binding)=='c6701ec4b53a9072811ff0a697521f8d82759219fbaa5c7c33acb1044d126dc6'
paths=[binding,Path('/tmp/review-modules-lft23-canonical-byte-binding-independent-foundations-v1.py'),Path('/tmp/modules-lft23-canonical-byte-binding-independent-foundations-actual-v1.json'),Path('/tmp/modules-lft23-canonical-byte-binding-independent-foundations-actual-v1.log'),Path('/tmp/modules23-source51-lft-candidate-builder-actual-v2.json'),Path('/tmp/modules23-source51-lft-candidate-builder-actual-v2.log'),Path('/tmp/modules-lft23-source51-input-preparation-actual-v1.json'),Path('/tmp/modules-lft23-source51-input-preparation-actual-v1.log'),Path('/tmp/modules-prepare-lft23-source51-inputs-v1.py'),Path('/tmp/finalize-module23-source51-reviewed-identity-offer-v1.py'),Path('/tmp/finalize-module23-source51-reviewed-identity-offer-v2.py'),Path('/tmp/modules-source51-reviewed-identity-offer-finalization-actual-v1.json'),Path('/tmp/modules-source51-reviewed-identity-offer-finalization-actual-v1.log'),Path('/tmp/modules-source51-reviewed-identity-offer-finalization-actual-v2.json'),Path('/tmp/modules-source51-reviewed-identity-offer-finalization-actual-v2.log')]
aliases={str(p):archive(p) for p in paths};actualref=aliases['/tmp/modules23-source51-lft-candidate-builder-actual-v2.json'];actual=J(R/actualref['file']);assert actual['actual_exit_code']==0 and H(Path(actual['log']))==actual['log_sha256']
helper=R/'book/coverage/build_modules23_candidate_source51_lft_v2.py';assert H(helper)==actual['actual_checker_sha256_before']==actual['actual_checker_sha256_after']
rv=inp['original_review'];reviewref={'file':rv['path'],'sha256':rv['sha256'],'reviewer':rv['reviewer'],'original_review_time':rv['original_review_time']}
out=copy.deepcopy(old);out.update(status='isolated_source51_eight_whole_nn_candidate_ready_for_final_delta_mechanics',module_ledger=ref(candidate)['file'],module_ledger_sha256=H(candidate),module_builder=ref(helper)['file'],module_builder_sha256=H(helper),actual_builder={**actualref,'actual_exit_code':0,'execution_kind':'actual_isolated_extension_candidate_builder'},actual_builder_raw_log=aliases['/tmp/modules23-source51-lft-candidate-builder-actual-v2.log'])
out['fresh_whole_exercise_keys']=old['fresh_whole_exercise_keys']+[inp['whole_exercise_key']];out['fresh_material_unit_keys']=old['fresh_material_unit_keys']+inp['material_unit_keys'];assert len(set(out['fresh_material_unit_keys']))==48
out['original_full_source_reviews']=old['original_full_source_reviews']+[reviewref]
out['counts']={**c['counts'],'new_owned_proofs':6,'new_public_theorems':64,'new_whole_exercises':8,'new_distinct_physical_units':48,'original_material_review_decisions':49}
out['required_external_import_dependencies']=c['required_external_import_dependencies']
out['original_identity51_reviewed_offer']=ref(oldpath);out['original_identity51_candidate']=c['reviewed_lft23_source51_candidate_extension']['original_reviewed_source51_identity_candidate'];out['original_identity51_independent_peer']=old['independent_final_candidate_mapping_peer']
out['lft23_canonical_binding_peer']=aliases[str(binding)];out['lft23_input_bindings']=ref(inputpath);out['lft23_original_path_aliases']=inp['canonical_path_aliases'];out['lft23_provenance_aliases']=aliases
out['independent_final_candidate_mapping_peer_pending']=True;out['prior_final_identity_mapping_peer']=out.pop('independent_final_candidate_mapping_peer')
out['scope_limits']=old['scope_limits']+['Distinct whole LFT Exercise14.1/six units added from original full peer54e1, with2 genuine canonical paired sources16 exports. Equilibrium attainment/local-sector/common-slope hypotheses retained. No global stability or numerical Algorithm1 optimization guarantee inferred.']
required=out['required_evidence_artifacts_sha256']
for p in [oldpath,candidate,helper,inputpath,R/inp['canonical_path_aliases']['file'],B/'modules23-source51-lft-candidate-binding-integrity-v2.json']:
 required[ref(p)['file']]=H(p)
for a in J(R/inp['canonical_path_aliases']['file'])['aliases'].values():required[a['path']]=a['sha256']
for a in aliases.values():required[a['file']]=a['sha256']
for proof in inp['proof_files']:
 n=proof['source'];evidence={a['path']:a['sha256'] for p in proof['actual_paired_records'] for a in [p['actual_record'],p['raw_log'],p['source_snapshot']]}
 evidence.update({ref(inputpath)['file']:H(inputpath),reviewref['file']:reviewref['sha256'],aliases[str(binding)]['file']:aliases[str(binding)]['sha256'],actualref['file']:actualref['sha256'],out['actual_builder_raw_log']['file']:out['actual_builder_raw_log']['sha256'],ref(helper)['file']:H(helper)})
 out['proof_files'][n]={'sha256':proof['sha256'],'declarations':proof['public_declarations'],'evidence_sha256':evidence,'actual_paired_records':proof['actual_paired_records'],'proof_selection_owner':'Modules23','standalone_compile_status':'passed','evidence_scope':'Genuine source-exact canonical standalone and named0, original full source peer and distinct canonical evidence supplement. Aggregate23 remains required.'}
assert len(out['proof_files'])==6 and sum(len(p['declarations']) for p in out['proof_files'].values())==64
assert {n:r for n,r in out['proof_files'].items() if n not in [p['source'] for p in inp['proof_files']]}==old['proof_files']
for n,d in required.items():assert H(R/n)==d,n
p=B/'modules-audit23-candidate-source51-lft-additions-v2.json';assert not p.exists();p.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'offer':ref(p),'candidate':ref(candidate),'counts':out['counts'],'scope':'Isolated combined candidate offer only, pending final independent delta mechanics. Actual candidate construction and canonical compiles remain distinct from any live/global integration.'}))
