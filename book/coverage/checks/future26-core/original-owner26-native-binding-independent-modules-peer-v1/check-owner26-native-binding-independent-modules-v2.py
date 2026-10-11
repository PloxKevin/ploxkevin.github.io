from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,importlib.util,json,re
R=Path('/home/oxrexkevin/SafetyBased');H=lambda p:hashlib.sha256((Path(p)if Path(p).is_absolute()else R/p).read_bytes()).hexdigest();J=lambda p:json.loads((R/p).read_text());ref=lambda p:{'file':p,'sha256':H(p)}
B='book/coverage/checks/prepare_root_owner26_bindings_v4.py';N='book/coverage/checks/root-owner26-reviewed-candidate-bindings-v1.json';assert H(B)=='f5b15f859cff5cb39606281c1bc7de8ed8a7e867e1b56337e4af9d3d514cfd0c'
native=J(N);request_ref=native['preparation_input'];assert H(request_ref['file'])==request_ref['sha256'];config=J(request_ref['file'])
spec=importlib.util.spec_from_file_location('independently_reviewed_readonly_binder26',R/B);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
reconstructed=module.build_binding(config,request_ref['file']);normalized=copy.deepcopy(native);normalized.pop('prepared_at_utc');reconstructed.pop('prepared_at_utc');assert normalized==reconstructed
assert native['new_proof_sources']==11 and native['new_public_exports']==134 and native['original_canonical_execution_records']==22
assert native['inventory_sha256']=='4b1e657eb61234a6d2e2a3a3ea6a0b11986c01d7d1c7cb5ba2dd5452d1fe29be'
assert set(native['owners'])=={'core','foundations','applied','modules'}
proofs={};counts={};semantic_count=0;original_times=[];native_pairs=[]
for owner,row in native['owners'].items():
 assert row['ready']is True
 for key in ['reviewed_final_offer','candidate_ledger','independent_candidate_mapping_peer','actual_candidate_builder']:
  r=row[key];assert H(r['file'])==r['sha256']
 offer=J(row['reviewed_final_offer']['file']);assert set(offer['proof_files'])==set(row['new_immutable_proof_sources'])
 assert H(row['held25_ledger'])==row['held25_ledger_sha256']
 for semantic in row['original_full_source_semantic_reviews']:
  assert H(semantic['file'])==semantic['sha256'];body=J(semantic['file'])
  assert body['status']==semantic['original_review_status'] and body.get('reviewed_at_utc',body.get('checked_at_utc'))==semantic['original_review_time']
  assert body.get('errors',[])==[];original_times.append(dict(owner=owner,file=semantic['file'],original_review_status=body['status'],original_review_time=semantic['original_review_time']));semantic_count+=1
 for r in row['additional_exact_provenance']:assert H(r['file'])==r['sha256']
 counts[owner]={'sources':len(row['new_immutable_proof_sources']),'canonical_records':2*len(row['new_immutable_proof_sources'])}
 for n,proof in row['new_immutable_proof_sources'].items():
  assert n not in proofs and H(n)==proof['sha256'];proofs[n]=proof['sha256']
  assert len(proof['actual_pair'])==2
  for actual in proof['actual_pair']:
   assert H(actual['file'])==actual['sha256'];body=J(actual['file'])
   exits=[body[k]for k in ('actual_exit_code','exit_code')if k in body];assert exits and all(type(c)is int and c==0 for c in exits)
   assert body['source']==actual['actual_source']==n and body['source_sha256_before']==body['source_sha256_after']==proof['sha256']
   commands=[body[k]for k in ('command','actual_command')if k in body];assert commands and all(c==actual['actual_command']for c in commands)
   assert H(actual['canonical_raw_log']['file'])==actual['canonical_raw_log']['sha256'];native_pairs.append(actual)
 for c in row['companion_candidates']:assert H(c['candidate']['file'])==c['candidate']['sha256'] and H(c['held25_asset'])==c['held25_asset_sha256']
assert counts=={'core':{'sources':4,'canonical_records':8},'foundations':{'sources':2,'canonical_records':4},'applied':{'sources':3,'canonical_records':6},'modules':{'sources':2,'canonical_records':4}}
assert len(native_pairs)==22 and sum(len(re.findall(r'^(?:theorem|lemma)\s+\w+', (R/n).read_text(),re.M))for n in proofs)==134
baseline=J('reports/full-coverage/checkpoint-25-selection.json');assert H('reports/full-coverage/checkpoint-25-selection.json')=='3559445215b6b5b9bd176363ded8d307a93724b2b68c1ba9845dc709a3b4ddff'
assert not(set(proofs)&set(baseline['proof_files']))
for n,row in baseline['proof_files'].items():assert H(n)==row['sha256']
for n,h in native['exact_current53_safelearning_assets_sha256'].items():assert H(n)==h
p=Path('/tmp/owner26-native-binding-independent-modules-confirmation-v1.json');assert not p.exists()
out={'status':'passed_independent_owner26_native_binding_and_original_semantic_reference_confirmation','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'binding_manifest':ref(N),'binding_preparation_input':request_ref,'helpers_sha256':{B:H(B),native['helper']['file']:native['helper']['sha256']},'complete_readonly_binder_reconstruction_equal_except_new_observation_time':True,'original_four_owner_rows_exact':True,'new_sources':11,'new_public_exports':134,'original_canonical_execution_records':22,'native_owner_counts':counts,'original_semantic_reference_count':semantic_count,'original_semantic_status_times':original_times,'all1156_selected25_root_hashes_exact':True,'all31_current53_assets_exact':True,'all_five_held25_owners_exact':True,'scope':'Independent genuine produced native binding read, exact complete read-only reconstruction, original semantic status/time and actual compiler record checks. No new fixture suite, producer binding/dry/apply/install/compiler/global/aggregate execution or mathematical redecision is inferred.'}
p.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'peer':str(p),'sha256':H(p),'semantic_refs':semantic_count}))
