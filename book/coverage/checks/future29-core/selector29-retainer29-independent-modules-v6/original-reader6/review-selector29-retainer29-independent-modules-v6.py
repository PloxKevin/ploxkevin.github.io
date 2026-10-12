from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,ast,difflib
R=Path('/home/oxrexkevin/SafetyBased');D=R/'book/coverage/checks/future29-core/selector29-retainer29-independent-modules-v6';assert not D.exists()
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
J=lambda p:json.loads(Path(p).read_bytes())
def ref(p):return {'file':Path(p).relative_to(R).as_posix(),'sha256':H(p)}
expected={'book/coverage/prepare_checkpoint29_selection_v5.py':'f431dadf04ffa3a4208d5823317dc53405878d9381e5d4429cce3c261641421b','book/coverage/retain_baseline_inputs29_v3.py':'6f1ca761425d65cd040b886178cb57c663030b205707fbf1d72c32423f8a18c5','book/coverage/lean_names.py':'9e00c114c57a2bb05939a21bee09679188aa97c855a8d10e61b160f31e10f07d'}
for n,h in expected.items():assert H(R/n)==h;ast.parse((R/n).read_text())
base=R/'reports/full-coverage/checkpoint-28-selection.json';man=R/'reports/full-coverage/checkpoint-28-manifest.json';audit=R/'reports/full-coverage/lean-checkpoint-28/verification-original.json'
assert H(base)=='e954d6a3f22139ec6ebafbe4164c46f184fe5e2c672860c9fce5829f73424632'and H(man)=='7aae00ecb663b2b12d8938a26f8f67141abc20b94efb4fc9145ff7aab1290466'and H(audit)=='7f12161869033e85af7927332eddee77cf62cdefbc5bb351150adec6b300adf8'
b,m,a=map(J,[base,man,audit]);assert len(b['proof_files'])==1186 and m['proof_files']==b['proof_files']and len(m['frozen_inputs_sha256'])==50797 and a['status']=='passed'and a['proof_file_count']==1186 and a['theorem_count']==9896 and a['proof_sha256']=={n:x['sha256']for n,x in b['proof_files'].items()}
for row in a['checks']:
 codes=[v for k,v in row.items()if k in ['actual_exit_code','exit_code','actual_runner_exit_code']];assert codes and all(type(v)is int and v==0 for v in codes)
assert H(R/'book/coverage/inventory.json')==H(R/'book/coverage/inventory-after-correction65.json')=='5f68ee3c68c1da1275a0a2667fe43b42263b8fc31800a834371de5bfbed01b68'
oldsel=R/'book/coverage/prepare_checkpoint28_selection_v4.py';oldret=R/'book/coverage/retain_baseline_inputs28_v3.py';v1=R/'book/coverage/prepare_checkpoint29_selection_v1.py';v2=R/'book/coverage/prepare_checkpoint29_selection_v5.py'
assert H(v1)=='161f3e5229afefcfb9b56812a152cf60bf20c3c303764d2ea85c3344c47ea653'
retast=ast.parse((R/'book/coverage/retain_baseline_inputs29_v3.py').read_text());aliases=ast.literal_eval(next(x.value for x in retast.body if isinstance(x,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='HISTORICAL_EVIDENCE_ALIASES'for t in x.targets)))
assert set(aliases)=={'book/coverage/material-corrections.json','book/coverage/inventory.json','SafeLearning/lipsdp.html'}
conflicts=[]
for n,row in b['proof_files'].items():
 for original,h in row['evidence_sha256'].items():
  if original in aliases:
   a=aliases[original];assert n=='verification/lean/SafeLearning/BookApplications.lean'and a['sha256']==h==H(R/a['file'])and H(R/original)!=h and (R/a['file']).resolve().is_relative_to(R);conflicts.append({'proof_file':n,'historical_original_path':original,'actual_immutable_alias':a})
assert len(conflicts)==3
prior=R/'book/coverage/checks/future29-core/selector29-retainer29-independent-modules-v1/checkpoint29-selector-retainer-full-independent-modules29-closed-peer-v2.json';assert H(prior)=='e9a510a5c258ea29c649901cdf926a1ba141fc090011b8754fe89680c72cb34e'
v3=R/'book/coverage/prepare_checkpoint29_selection_v3.py'
assert H(v3)=='d9fb62d6a6a7a37913903d3441854d0f195848750f7b63ee8fe786b521a1cb70'
v4=R/'book/coverage/prepare_checkpoint29_selection_v4.py';assert H(v4)=='8922df9d3a1b1f5d1313f1f893f6e190e7c3249ff161f10bacaf50ee1d6f8e52'
assert v4.read_text()==v3.read_text().replace("row['original27_byte_copy']","row['original28_byte_copy']")
assert v3.read_text().count("row['original27_byte_copy']")==1
integration_path=R/'reports/full-coverage/owner29-reviewed-candidate-integration-v1.json'
integration=J(integration_path)
assert integration['status']=='four_exact_reviewed_owner29_candidate_bytes_integrated_pending_fresh_current65_global_integrity_and_aggregate29_audit'
assert integration['applied'] is True and integration['inventory_sha256']==H(R/'book/coverage/inventory.json')
execution_path=R/'reports/full-coverage/owner29-reviewed-candidate-integration-execution-v1.json'
execution=J(execution_path);assert execution['actual_exit_code']==0 and execution['status']=='passed'
assert H(R/execution['log'])==execution['log_sha256']
binding_path=R/integration['binding_manifest'];assert H(binding_path)==integration['binding_manifest_sha256'];binding=J(binding_path)
assert binding['helper']==integration['actual_helper']
assert execution['actual_command']==['python3',integration['actual_helper']['file'],'--binding',integration['binding_manifest'],'--binding-sha256',integration['binding_manifest_sha256'],'--apply']
assert execution['actual_workdir']==str(R) and execution['helper_sha256_before']==execution['helper_sha256_after']=={integration['actual_helper']['file']:integration['actual_helper']['sha256']}
assert H(R/integration['actual_helper']['file'])==integration['actual_helper']['sha256']
assert len(integration['exact_replacements'])==5
for row in integration['exact_replacements']:
 assert set(row)=={'destination','before_sha256','candidate','original28_byte_copy'}
 assert H(R/row['destination'])==H(R/row['candidate']['file'])==row['candidate']['sha256']
 assert H(R/row['original28_byte_copy'])==row['before_sha256']
global_path=R/'reports/full-coverage/root-source65-final-owner-integration29-v1.json';g=J(global_path)
assert g['integrity_status']=='passed'and g['errors']==[]and g['mathematical_coverage_complete']is False
for n,h in g['source_sha256'].items():assert H(R/n)==h,n
assert g['inventory_sha256']==H(R/'book/coverage/inventory.json')and g['counts']['material_review_statuses']=={'reviewed':4663,'pending':8111}
assert g['counts']['statuses']['exercise:complete_math']==526 and g['counts']['statuses']['exercise:partial']==11 and g['counts']['statuses']['exercise:pending']==19
failed_path=R/'reports/full-coverage/selection29-preflight-execution-v1.json';failure=J(failed_path)
assert failure['actual_exit_code']==1 and failure['status']=='failed'and H(R/failure['log'])==failure['log_sha256']
assert "original27_byte_copy" in (R/failure['log']).read_text()
assert not(R/'reports/full-coverage/checkpoint-29-selection.json').exists()and not(R/'book/coverage/checks/frozen28-input-content-bindings29-v1.json').exists()
new_sources={};native_pair_count=0
for batch in binding['canonical_pair_batches']:
 rp=R/batch['readiness']['file'];assert H(rp)==batch['readiness']['sha256'];ready=J(rp)
 assert ready['status']==batch['expected_readiness_status']and ready['errors']==[]
 native_pair_count+=len(ready['actual_paired_records'])
 for row in ready['sources']:
  n=row['canonical_source'];assert n not in new_sources;new_sources[n]=row['original_tmp_source']['sha256'];assert H(R/n)==new_sources[n]
 for pair in ready['actual_paired_records']:
  for key in ['actual_record','raw_log','source_snapshot']:
   rr=pair[key];assert H(R/rr['file'])==rr['sha256']
  nn=J(R/pair['actual_record']['file']);codes=[nn[k]for k in ['exit_code','actual_exit_code','actual_runner_exit_code']if k in nn];assert codes and all(type(c)is int and c==0 for c in codes)and nn['status']=='passed';assert nn['source']==pair['source']['file'];assert nn['source_sha256_before']==nn['source_sha256_after']==pair['source']['sha256'];command=['lake','env','lean','SafeLearning/'+Path(nn['source']).name]if pair['kind']=='standalone'else['lake','build','SafeLearning.'+Path(nn['source']).stem];commands=[nn[k]for k in ['command','actual_command']if k in nn];assert commands and all(c==command for c in commands);assert nn['actual_workdir']==str(R/'verification/lean')
assert len(new_sources)==11 and native_pair_count==22
sys_path=__import__('sys').path;sys_path.insert(0,str(R/'book/coverage'));from lean_names import declarations
selected_sources=set(b['proof_files'])|set(new_sources);assert len(selected_sources)==1197
all_declarations=[d for n in selected_sources for d in declarations((R/n).read_text())]
all_names=[d['name']for d in all_declarations];assert len(all_names)==len(set(all_names))
assert sum(d['kind']in{'theorem','lemma'}for d in all_declarations)==10114
assert sum(d['kind']in{'theorem','lemma'}for n in new_sources for d in declarations((R/n).read_text()))==218
for n in selected_sources:
 for line in __import__('re').findall(r'^import[^\n]*',(R/n).read_text(),__import__('re').M):
  for dep in line.split()[1:]:
   if dep.startswith('SafeLearning.'):assert 'verification/lean/'+dep.replace('.','/')+'.lean' in selected_sources

plan2_path=R/'book/coverage/checks/future29-core/checkpoint29-installed-owner-selection-plan-v2.json';plan2=J(plan2_path)
assert len(b['extra_frozen_inputs'])==11454 and len(plan2['additional_frozen_inputs'])==320
extra_conflicts=[]
for collection_name,rows in [('original_selected28_extras',b['extra_frozen_inputs']),('actual_plan2_additional_extras',plan2['additional_frozen_inputs'])]:
 for name,row in rows.items():
  p=R/name;assert p.resolve().is_relative_to(R.resolve())and not p.is_symlink(),name
  current=H(p)
  if current!=row['sha256']:extra_conflicts.append({'collection':collection_name,'original_path':name,'original_entire_row':row,'actual_current_sha256':current})
assert len(extra_conflicts)==1 and extra_conflicts[0]['original_path']=='book/coverage/material-corrections.json'
assert extra_conflicts[0]['original_entire_row']['sha256']=='90097eba3c8b954074285ee91010745685c5f3e27cc99caf966c76d9ae7a1d81'
assert extra_conflicts[0]['actual_current_sha256']=='5c3a871bbc5782a02c5b19bfa33a8fa6e4dc311a9e72c525d76fcc526f37eafd'
extra_alias=aliases['book/coverage/material-corrections.json'];assert H(R/extra_alias['file'])==extra_conflicts[0]['original_entire_row']['sha256']
ret3_source=(R/'book/coverage/retain_baseline_inputs29_v3.py').read_text();sel5_source=v2.read_text()
assert "assert set(extra_replacements)=={'book/coverage/material-corrections.json'}"in ret3_source and "assert set(extra_replacements)=={'book/coverage/material-corrections.json'}"in sel5_source
assert "assert row['sha256']==alias['sha256']==sha(alias['file']) and n not in extras"in ret3_source
assert "assert extras.get(alias['file'])==row"in ret3_source
assert "'original_replaced_extra_frozen_input_rows':{p:baseline['extra_frozen_inputs'][p] for p in extra_replacements}"in sel5_source and "'original_replaced_extra_frozen_input_rows':{p:baseline['extra_frozen_inputs'][p] for p in extra_replacements}"in ret3_source
root_fail2_path=R/'reports/full-coverage/selection29-preflight-execution-v2.json';root_fail2=J(root_fail2_path);assert root_fail2['actual_exit_code']==1 and H(R/root_fail2['log'])==root_fail2['log_sha256']

D.mkdir(parents=True)
deltas=D/'selector29-retainer29-full-original-deltas-v1.json';deltas.write_text(json.dumps({'selector':list(difflib.unified_diff(oldsel.read_text().splitlines(True),v2.read_text().splitlines(True),fromfile=str(oldsel),tofile=str(v2))),'retainer':list(difflib.unified_diff(oldret.read_text().splitlines(True),(R/'book/coverage/retain_baseline_inputs29_v3.py').read_text().splitlines(True),fromfile=str(oldret),tofile=expected.keys().__iter__().__next__()))},indent=2)+'\n')
peer={'status':'passed_independent_checkpoint29_selection_and_baseline_retainer_full_code_review','errors':[],'reviewer':'/root/modules_finish28','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':ref(v2),'reviewed_helpers_sha256':expected,'entire_selector_and_retainer_original_source_read':True,'entire_old28_v4_and_retainer_v3_deltas_read':True,'reviewed_old_helpers':{'selector':ref(oldsel),'retainer':ref(oldret)},'preserved_unexecuted_new_selector_v1_status_literal_typo':ref(v1),'full_literal_deltas':ref(deltas),'baseline_selection':ref(base),'baseline_manifest':ref(man),'baseline_actual_audit':ref(audit),'inventory_sha256':'5f68ee3c68c1da1275a0a2667fe43b42263b8fc31800a834371de5bfbed01b68','original_v2_v1_code_peer_body_and_time_preserved':ref(prior),'original_v3_actual_failure':ref(failed_path),'original_v3_actual_failure_log':ref(R/failure['log']),'original_v3_code':ref(v3),'actual_owner29_installed_schema':ref(integration_path),'actual_owner29_integration_execution':ref(execution_path),'actual_current65_owner29_global_integrity':ref(global_path),'actual_new_source_count':11,'actual_selected_union_count':1197,'actual_theorem_union_count':10114,'exact_one_field_delta_original27_to_original28':True,'original_v4_retainer2_true_failed_preflight':ref(root_fail2_path),'original_v4_retainer2_true_failed_preflight_raw':ref(R/root_fail2['log']),'actual11774_extra_inputs_checked':11774,'exact_one_stale_extra_input':extra_conflicts,'exact_one_extra_input_historical_alias':extra_alias,'original_v4_code':ref(v4),'original_v4_fullcode_peer':ref(R/'book/coverage/checks/future29-core/selector29-retainer29-independent-modules-v5/checkpoint29-selector-retainer-full-independent-modules29-closed-peer-v2.json'),'own_original_reader4_native_schema_failure':{'file':'/tmp/selector29-retainer29-independent-modules-actual-v4.json','sha256':H('/tmp/selector29-retainer29-independent-modules-actual-v4.json')},'own_original_reader4_failure_reason':'Reader4 passed actual five-row original28_byte_copy schema and stopped before peer writes because it assumed actual_exit_code on compiler records whose authentic field is exit_code. New5 checks all literal native code/command aliases exactly, retaining original records unchanged.','own_original_reader3_old_context_failure':{'file':'/tmp/selector29-retainer29-independent-modules-actual-v3.json','sha256':H('/tmp/selector29-retainer29-independent-modules-actual-v3.json')},'own_original_reader3_failure_reason':'The read-only first new reader still used the original Source65-owner28 context pins; it stopped on now-installed owner29 core.json before peer writes. New4 authenticates actual installed owner29/source65/global records and fresh before/after hashes. Original helper/native/raw/time remains unchanged.','actual_three_historical_Source60_retrieval_conflicts_and_exact_archives':conflicts,'concrete_review_findings':['The entire new v5/v3 delta and full retainer were read. Exactly one stale extra corrections key moves to its actual source60 original-byte alias, with the original entire row and replacement map explicit in selection and provenance; all11454 original and320 plan2 extra files were independently hashed, with exactly that one mismatch and no physical-containment failures. The preceding entire v4/v2 code was read, including the exact one-field original28_byte_copy correction after the preserved genuine v3 preflight failure. The earlier review missed that access; current five actual installed rows and original archive bytes were checked directly. The earlier v3/v2 delta remains exact: only the three pinned historical retrieval keys are retargeted for BookApplications.lean; its full original row is stored verbatim and retainer validates exactly the same mapping and all old fields. No earlier native body, semantic scope or timestamp is rewritten.','The selector authenticates current65 inventory, installed five exact candidate bytes, independent mapping/helper peers, actual native compiler pairs and closure before selecting eleven additions.','Native standalone and named command/cwd/source-before-after/log/snapshot identities are checked; digest-string and typed evidence-map schemas preserve actual receipts.','Namespace-aware complete public declarations are checked globally for duplicate names, exact10114 theorem/lemma count and218 additions, all owner declaration references and selected SafeLearning import closure.','The retainer preserves all1186 old proof rows fieldwise, permits only evidence-map extension, preserves existing extras and all50797 original frozen path/hash pairs by exact current content or immutable snapshot aliases, with original bodies/time unchanged.','Both outputs are fresh exclusive-create files, bounded below100MB, and publication/coverage completion remain separate.','Direct full code review and pinned baseline/current65 guard suffice for this exact phase delta; no selector/retainer execution or mirror fixtures were performed.'],'scope':'Full code and exact actual installed-owner29 schema review only. Real producer preparation/selection writes and fresh aggregate audit remain Root work.','production_selector_or_retainer_invoked':False,'synthetic_fixtures_run':False,'compiler_started':False,'current_source_or_owner_mutated':False,'coverage_complete':False,'actual_finalizer':None}
p=D/'checkpoint29-selector-retainer-full-independent-modules29-peer-v1.json';p.write_text(json.dumps(peer,indent=2)+'\n');print(json.dumps({'peer':ref(p),'status':peer['status']}))
