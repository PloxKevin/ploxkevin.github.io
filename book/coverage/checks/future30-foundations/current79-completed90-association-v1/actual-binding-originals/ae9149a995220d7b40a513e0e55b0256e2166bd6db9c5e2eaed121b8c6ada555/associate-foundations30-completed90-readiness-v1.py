from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,copy
R=Path('/home/oxrexkevin/SafetyBased');D=R/'book/coverage/checks/future30-foundations/current79-completed90-association-v1';assert not D.exists()
OLD=R/'book/coverage/checks/future30-foundations/current79-real54-pair-bound-v2/foundations30-current79-real54-pair-bound-closed-offer-v3.json'
READY=R/'book/coverage/checks/future30-core/current79-canonical-pairs45-v1/actual-reviewed30-canonical-paired-readiness-v1.json';NATIVE=R/'reports/full-coverage/current79-canonical-pairs45-application30-execution-v1.json'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):return {'file':p.relative_to(R).as_posix(),'sha256':sha(p),'bytes':p.stat().st_size}
def data(x):return (json.dumps(x,indent=2)+'\n').encode()
assert sha(OLD)=='0cd7f33bd7688e215f7261497d68203151b0d5ef4559c4f0dced60020d9c523d' and sha(READY)=='4ce14955fe77d0cc9447ff9963e79631ce8dbff3110683d261eb3c89eaa2cf7e' and sha(NATIVE)=='8e3e384891e52794a493d078350abe282c8d215ff7f883eae6a3861c4eda77ee'
o=json.loads(OLD.read_bytes());p=R/o['candidate']['file'];before=json.loads(p.read_bytes());c=copy.deepcopy(before);ready=json.loads(READY.read_bytes());a=json.loads(NATIVE.read_bytes())
assert ready['status']=='passed_actual_reviewed30_canonical_standalone_and_named_pairs_unselected' and ready['errors']==[] and (ready['source_count'],ready['public_theorem_count'],ready['public_name_count'],ready['actual_compiler_command_count'])==(45,966,1273,90) and ready['coverage_complete'] is False and ready['selection_aggregate_owner_or_publication_claimed'] is False
assert a['status']=='passed' and type(a['actual_exit_code']) is int and a['actual_exit_code']==0 and a['actual_command']==['python3','book/coverage/checks/run_root30_reviewed_canonical_pairs_v2.py','--plan','book/coverage/checks/future30-core/current79-canonical-plan45-v2.json','--plan-sha256','4a2c2ab8e877d098f243562adc2112c116aa93062b40757c2d5e0cd57f90b09d','--apply'] and a['actual_workdir']==str(R) and a['helper_sha256_before']==a['helper_sha256_after'] and sha(R/a['log'])==a['log_sha256']
pairs={(r['source']['file'],r['kind']):r for r in ready['actual_paired_records']};assert len(pairs)==90
for dest,row in o['proof_files'].items():
 for r in row['actual_pair']:
  rr=pairs[(dest,r['kind'])]
  for fld in ['source','actual_record','raw_log','source_snapshot']:
   assert all(rr[fld][k]==r[fld][k] for k in ['file','sha256'])
  assert rr['actual_exit_code']==r['actual_exit_code']==0
changes=[]
def change(keys,v):
 d=c
 for k in keys[:-1]:d=d[k]
 exists=keys[-1] in d;old=copy.deepcopy(d.get(keys[-1]));d[keys[-1]]=copy.deepcopy(v);changes.append({'path':keys,'before_present':exists,'before':old,'after':copy.deepcopy(v)})
base=D.relative_to(R).as_posix();ifile=base+'/foundations30-completed90-current79-association-exact-inverse-v1.json';cfile=base+'/foundations30-completed90-current79-pair-bound-candidate-v1.json';ofile=base+'/foundations30-completed90-current79-pair-bound-offer-v4.json'
change(['current30_material_mapping','common90_final_readiness_and_global_review_pending'],False)
change(['current30_material_mapping','actual_common90_readiness'],ref(READY));change(['current30_material_mapping','actual_common90_outer_execution'],ref(NATIVE));change(['current30_material_mapping','selected_aggregate30_and_owner_installation_pending'],True)
change(['current30_material_mapping','exact_interface'],{'file':ifile})
change(['current30_canonical_bindings','common90_final_runner_and_readiness_pending'],False)
change(['current30_canonical_bindings','actual_common90_readiness'],ref(READY));change(['current30_canonical_bindings','actual_common90_outer_execution'],ref(NATIVE))
reverse=copy.deepcopy(c)
for ch in reversed(changes):
 cur=reverse
 for k in ch['path'][:-1]:cur=cur[k]
 assert cur[ch['path'][-1]]==ch['after']
 if ch['before_present']:cur[ch['path'][-1]]=copy.deepcopy(ch['before'])
 else:del cur[ch['path'][-1]]
assert reverse==before and data(reverse)==p.read_bytes() and c['material_claims']==before['material_claims'] and c['exercises']==before['exercises'] and c['counts']==before['counts']
i={'status':'passed_exact_completed90_readiness_metadata_association_only','errors':[],'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'original_real54_candidate':o['candidate'],'original_real54_offer':ref(OLD),'original_real54_full_inverse':o['exact_interface'],'actual90_readiness':ref(READY),'actual90_native':ref(NATIVE),'exact_metadata_changes':changes,'hash_finalization_reverse_rule':'Restore current30_material_mapping.exact_interface to the SHA-absent after value recorded here, then reverse changes. This recovers exact original real54 candidate bytes; the existing42d ande2cd interfaces restore the entire original rawowner29 bytes.','exact_reverse_restores_original_real54_candidate_bytes':True,'all_math_source_correspondence_rows_counts_and_original_body_times_unchanged':True,'no_new_whole_or_component_semantic_decision':True,'owner_installation_and_selected_aggregate_pending':True,'coverage_complete':False}
ib=data(i);ir={'file':ifile,'sha256':hashlib.sha256(ib).hexdigest(),'bytes':len(ib)};c['current30_material_mapping']['exact_interface']=ir;cb=data(c);cr={'file':cfile,'sha256':hashlib.sha256(cb).hexdigest(),'bytes':len(cb)}
out=copy.deepcopy(o);req=dict(o['required_evidence_artifacts_sha256']);req.update({ref(OLD)['file']:sha(OLD),ref(READY)['file']:sha(READY),ref(NATIVE)['file']:sha(NATIVE),a['log']:a['log_sha256'],ifile:ir['sha256'],cfile:cr['sha256']})
out.update(status='prepared_completed90_current79_Foundation27_actual54_pair_bound_candidate_pending_full_independent_mapping',prepared_at_utc=datetime.now(timezone.utc).isoformat(),candidate=cr,mapped_ledger=cfile,mapped_ledger_sha256=cr['sha256'],exact_interface=ir,original_real54_pair_bound_offer=ref(OLD),original_real54_binding_exact_interface=o['exact_interface'],actual_common90_readiness=ref(READY),actual_common90_outer_execution=ref(NATIVE),common90_outer_runner_and_final_readiness_pending=False,selected_aggregate30_and_owner_installation_pending=True,completed90_association_preparation_actual_pending=True,required_evidence_artifacts_sha256=req,additional_frozen_inputs=req)
for n,h in ready['protected_inputs_sha256'].items():assert sha(R/n)==h
for q,b in [(R/ifile,ib),(R/cfile,cb),(R/ofile,data(out))]:q.parent.mkdir(parents=True,exist_ok=True);assert not q.exists();q.write_bytes(b)
print(json.dumps({'offer':ref(R/ofile),'candidate':cr,'exact_interface':ir,'actual90_public_sources_commands':[45,966,90],'own_source_public_commands':[27,370,54],'literal_and_count_deltas':0,'errors':[]}))
