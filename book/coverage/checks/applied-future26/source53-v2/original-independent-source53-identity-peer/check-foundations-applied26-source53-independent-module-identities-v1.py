from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json
R=Path('/home/oxrexkevin/SafetyBased')
def P(p):return Path(p)if Path(p).is_absolute()else R/p
def H(p):return hashlib.sha256(P(p).read_bytes()).hexdigest()
def J(p):return json.loads(P(p).read_text())
def ref(p):return {'file':str(p),'sha256':H(p)}
def checked(x):assert set(x)>={'file','sha256'} and H(x['file'])==x['sha256'];return J(x['file'])if x['file'].endswith('.json')else None
def zero(d):
 k=[k for k in ('actual_exit_code','exit_code')if k in d];assert k and all(type(d[t])is int and d[t]==0 for t in k)
def original_refs(d):
 if isinstance(d,dict):
  if isinstance(d.get('file'),str)and 'sha256'in d:assert H(d['file'])==d['sha256'],d['file']
  for v in d.values():original_refs(v)
 elif isinstance(d,list):
  for v in d:original_refs(v)
I52='book/coverage/inventory-after-correction52.json';I53='book/coverage/inventory-after-correction53.json';ISH='4b1e657eb61234a6d2e2a3a3ea6a0b11986c01d7d1c7cb5ba2dd5452d1fe29be';assert H(I53)==H('book/coverage/inventory.json')==ISH
oldinv,newinv=J(I52),J(I53);assert oldinv['counts']==newinv['counts']
M='reports/full-coverage/checkpoint-25-manifest.json';manifest=J(M);assert len(manifest['proof_files'])==1156
owners={p:manifest['working_inputs_sha256'][p]for p in ['book/coverage/'+n+'.json'for n in ['core','foundations','applied','modules','applied-promotions']]}
for p,h in owners.items():assert H(p)==h
for p,row in manifest['proof_files'].items():assert H(p)==H('reports/full-coverage/checkpoint-25/'+p)==row['sha256']
app='reports/full-coverage/source53-correction-application-v1.json';assert H(app)=='fbc298db9520fb9eae49997fe7955062b1bb373605a3af81f40801fd317da548';application=J(app);assert application['inventory_after']==ref(I53)
act='reports/full-coverage/source53-correction-application-execution-v1.json';rootactual=J(act);zero(rootactual);assert H(rootactual['log'])==rootactual['log_sha256']
assets={p:h for p,h in manifest['working_inputs_sha256'].items()if p.startswith('SafeLearning/')};assert len(assets)==31
for p,h in assets.items():
 assert H('reports/full-coverage/checkpoint-25/'+p)==h
 assert H(p)==(application['source_after']['sha256']if p==application['source_after']['file']else h)
B='book/coverage/checks/foundations-future26/source53';F=B+'/foundations-audit26-candidate-source53-additions-draft-with-actual-v1.json';assert H(F)=='1ee9addeeee1fcbdaf9fc50814dfebc878dae220076312690502177877b892a3'
f=J(F);fr=f['current53_identity_rebase'];fo=checked(fr['original_source52_final_offer']);fc=J(f['mapped_ledger']);assert H(f['mapped_ledger'])==f['mapped_ledger_sha256'];oldfc=J(fo['mapped_ledger']);inv=copy.deepcopy(fc);binding=inv.pop('current53_owner_identity');assert inv==oldfc
inv=copy.deepcopy(f);r=inv.pop('current53_identity_rebase');inv.update(r['original_source52_outer_fields']);inv['additional_frozen_inputs']=r['original_additional_frozen_inputs'];assert inv==fo
assert set(fr['original_source52_outer_fields'])=={'status','mapped_ledger','mapped_ledger_sha256','current_inventory','current_inventory_sha256','current_owner_builder','current_owner_builder_sha256','actual_builder_record','actual_builder_record_sha256','actual_builder_raw_log'}
assert f['current_inventory']==I53 and f['current_inventory_sha256']==ISH
fs=checked(fr['identity_sidecar']);checked(fr['integrity']);assert binding['identity_sidecar']==fr['identity_sidecar'];assert fs['entire_owned_inventory_records']['exercises']==[x for x in newinv['exercises']if x['source']in oldfc['scope_pages']]
for sec,count in [('exercises',119),('material_source_units',1756)]:
 x=[r for r in oldinv[sec]if r['source']in oldfc['scope_pages']];y=[r for r in newinv[sec]if r['source']in oldfc['scope_pages']];assert x==y==fs['entire_owned_inventory_records'][sec]and len(y)==count
assert f['proof_files']==fo['proof_files']and len(f['proof_files'])==2 and f['new_theorem_or_lemma_count']==15
for p,h in f['additional_frozen_inputs'].items():assert H(p)==h
for p,row in f['proof_files'].items():
 assert H(p)==row['sha256']
 for ep,eh in row['evidence_sha256'].items():assert H(ep)==eh
for p,h in f['actual_canonical_execution_records_sha256'].items():
 assert H(p)==h;d=J(p);zero(d);assert H(d['source'])==d['source_sha256_before']==d['source_sha256_after'];assert H(d['log'])==d.get('log_sha256',d.get('raw_log_sha256'))
fa=J(f['actual_builder_record']);zero(fa);assert H(f['actual_builder_record'])==f['actual_builder_record_sha256'];assert fa['actual_command']==['python3',f['current_owner_builder'],'--root-authorized-source53-identity-rebase','--inventory-sha256',ISH];assert fa['helper_sha256_before']==fa['helper_sha256_after']==H(f['current_owner_builder']);assert H(fa['log'])==fa['log_sha256'];assert H(fa['actual_runner'])==fa['actual_runner_sha256'];assert fa['finished_at_utc']>=fa['started_at_utc'];original_refs(fr)
A='book/coverage/checks/applied-future26/source53-v2/applied-audit26-candidate-source53-additions-draft-v1.json';assert H(A)=='18d3353de0cb9e60b8ba02a3eaae4c6849802e2afaaff15cceebe4b57700bb87'
a=J(A);ar=a['source53_identity_rebase'];ao=checked(ar['original_source52_reviewed_offer']);ac=checked(a['candidate']);ap=checked(a['candidate_promotions']);oldac=J(ao['mapped_ledger']);oldap=J(ao['mapped_promotions'])
for current,previous in [(ac,oldac),(ap,oldap)]:
 inv=copy.deepcopy(current);inv.pop('current53_owner_identity');assert inv==previous
inv=copy.deepcopy(a);r=inv.pop('source53_identity_rebase');inv.pop('preserved_initial_source53_identity_preparation_failure');inv.update(r['original_source52_outer_fields']);assert inv==ao
as_=checked(ar['identity_sidecar']);checked(ar['identity_integrity']);assert a['inventory']==I53 and a['inventory_sha256']==ISH
for sec,count in [('exercises',128),('material_source_units',2059)]:
 x={r['key']:r for r in oldinv[sec]if r['source']in oldac['scope_pages']};y={r['key']:r for r in newinv[sec]if r['source']in oldac['scope_pages']};assert x==y==as_['entire_owned_inventory_records'][sec]and len(y)==count
assert len(ac['proof_files'])==312 and len(ac['material_claims'])==1954 and sum(len(e['claims'])for e in ac['exercises'])==468
assert a['proof_files']==ao['proof_files']and len(a['proof_files'])==3
for p,h in a['required_evidence_artifacts_sha256'].items():assert H(p)==h
original_refs(ar);original_refs(a['preserved_initial_source53_identity_preparation_failure']);failed=checked(a['preserved_initial_source53_identity_preparation_failure']['actual_execution']);assert type(failed['actual_exit_code'])is int and failed['actual_exit_code']==1
AA='book/coverage/checks/applied-future26/source53-v2/source53-identity-preparation-actual-v2.json';aa=J(AA);zero(aa);assert aa['actual_command']==['python3',a['candidate_builder']['file'],'--root-authorized-source53-identity-rebase','--inventory-sha256',ISH];assert aa['helper_sha256_before']==aa['helper_sha256_after']==a['candidate_builder']['sha256']==H(a['candidate_builder']['file']);assert H(aa['raw_log'])==aa['raw_log_sha256'];assert aa['finished_at_utc']>=aa['started_at_utc']
for p,h in owners.items():assert H(p)==h
for name,path,offer,oldoffer,cand,identity,actual,counts in [('foundations',F,f,fr['original_source52_final_offer'],{'file':f['mapped_ledger'],'sha256':f['mapped_ledger_sha256']},fr['identity_sidecar'],ref(f['actual_builder_record']),{'entire_exercises':119,'entire_material_units':1756,'sources':2,'public_exports':15,'actual_pairs':4}),('applied',A,a,ar['original_source52_reviewed_offer'],a['candidate'],ar['identity_sidecar'],ref(AA),{'entire_exercises':128,'entire_material_units':2059,'exercise_claims':468,'material_claims':1954,'proof_metadata_rows':312,'sources':3,'public_exports':23,'actual_pairs':6})]:
 out={'status':'passed_independent_exact_source53_unchanged_owner_identity_confirmation','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'independent_modules','reviewed_offer':ref(path),'candidate_ledger':cand,'original_source52_reviewed_offer':oldoffer,'identity_sidecar':identity,'immutable_inventory_after':ref(I53),'actual_identity_preparation':actual,'exact_inverse_restores_entire_prior_candidate_and_offer':True,'all_owned_entire_inventory_records_unchanged':True,'all_original_math_bodies_hypotheses_decisions_times_and_actual_pairs_preserved':True,'all1156_selected_and_frozen25_sources_exact':True,'all31_frozen25_assets_and_single_authorized_current53_delta_exact':True,'unchanged_five_live25_owner_sha256':owners,'counts':counts,'scope':'Independent read-only identity/evidence mechanics only; no semantic redecision, compiler execution, live installation or aggregate26 claim.','checker':ref('/tmp/check-foundations-applied26-source53-independent-module-identities-v1.py')}
 if name=='applied':out['candidate_promotions']=a['candidate_promotions'];out['preserved_original_identity_preparation_failure']=a['preserved_initial_source53_identity_preparation_failure']
 dest=Path('/tmp/'+name+'26-source53-identity-independent-modules-confirmation-v1.json');assert not dest.exists();dest.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'owner':name,'peer':ref(dest)}))
