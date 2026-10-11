from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,ast
ROOT=Path('/home/oxrexkevin/SafetyBased');BASE=Path('/tmp/root27-eight-source141-canonical-pair-draft-v1');assert not BASE.exists()
def path(n):return Path(n) if Path(n).is_absolute() else ROOT/n
def sha(n):return hashlib.sha256(path(n).read_bytes()).hexdigest()
def ref(n):return {'file':str(n),'sha256':sha(n)}
def checked(v):assert set(v)=={'file','sha256'} and sha(v['file'])==v['sha256'];return json.loads(path(v['file']).read_text())
module_plan=ref('/tmp/modules27-current55-two-whole-mapping-draft-v1/modules27-current55-four-source-canonical-pair-planning-request-v1.json')
foundation_plan=ref('/tmp/foundations27-source55-three-source43-five-whole-unit-draft-v2/foundations27-three-source43-canonical-pair-plan-unexecuted-v1.json')
foundation_interface=ref('/tmp/foundations27-source55-three-source43-five-whole-unit-draft-v2/foundations27-current55-five-whole-unit-interface-draft-v1.json')
root_packet=ref('/tmp/root-first-successor11-original-byte-preparation27-v1/root-first-successor11-original-byte-preparation27-v1.json')
conformal_packet=ref('/tmp/modules-conformal45-canonical-byte-history27-v3/conformal45-reviewed-source-and-history-preparation27-v3.json')
viability_packet=ref('/tmp/applied-viability16-canonical-preparation27-v2/viability16-42-source-original-whole-review-canonical-preparation-v2.json')
inputs=[module_plan,foundation_plan,foundation_interface,root_packet,conformal_packet,viability_packet]
m=checked(module_plan);f=checked(foundation_plan);fi=checked(foundation_interface);r=checked(root_packet);c=checked(conformal_packet);v=checked(viability_packet)
assert module_plan['sha256']=='bca767b0a7f2b1c24a502ed81a3c84cae34940e0c80bc7537a7c52653a2bb71b'
assert foundation_plan['sha256']=='cfa5e5aaf7a32bdbbb4493ec87cc2232ae0141fba970af8974073dfc95147eca'
assert root_packet['sha256']=='d4965663962f013f18fdb8797a2d8e82682bc61a3da44a562470daf54a75de5a'
rows=[]
for a in m['source_plans']:
 rows.append({'canonical_source':a['canonical_source'],'source':a['exact_original_tmp_source'],'public_theorem_count':a['public_theorem_count'],'all_public_declarations':a['all_public_declarations'],'original_semantic_peer':a['whole_peer'],'actual_original_tmp_standalone':a['original_true_tmp_standalone']['record'],'provider':a['source_provider']})
for n,a in f['planned_sources'].items():
 rows.append({'canonical_source':n,'source':a['exact_original_tmp_source'],'public_theorem_count':a['public_theorem_count'],'all_public_declarations':a['all_public_declarations'],'original_semantic_peer':a['original_full_source_semantic_peer'],'actual_original_tmp_standalone':a['actual_original_tmp_standalone'],'provider':'Foundations27'})
a=r['entire_original_full_component_peer_body_and_time']
rows.append({'canonical_source':'verification/lean/SafeLearning/CompleteCoreMPCFirstSuccessor27.lean','source':a['proof_source'],'public_theorem_count':a['public_theorem_count'],'all_public_declarations':a['all_public_theorem_names'],'original_semantic_peer':r['original_full_component_peer'],'actual_original_tmp_standalone':a['actual_standalone'],'provider':'Root Core27 precise components; whole parent remains pending'})
assert len(rows)==8 and sum(a['public_theorem_count'] for a in rows)==141
aliases={}
def add(original,digest,copyref):
 assert set(copyref)=={'file','sha256'} and copyref['sha256']==digest and sha(copyref['file'])==digest
 key=original+'::'+digest
 item={'original_file':original,'original_sha256':digest,'exact_existing_byte_copy':copyref}
 if key in aliases:assert aliases[key]['original_sha256']==digest
 else:aliases[key]=item
for packet in (r,c,v):
 for original,copyref in packet['original_closed_byte_aliases'].items():add(original,copyref['sha256'],copyref)
for a in fi['exact_original_byte_aliases'].values():add(a['original_path'],a['original_sha256'],a['immutable_byte_copy'])
for a in inputs+[m['candidate_mapping_draft'],m['source55_identity']]:add(a['file'],a['sha256'],a)
for a in rows:
 for key in ('source','original_semantic_peer','actual_original_tmp_standalone'):
  b=a[key];add(b['file'],b['sha256'],b)
 b=checked(a['actual_original_tmp_standalone']);codes=[b[k] for k in ('actual_exit_code','exit_code','actual_runner_exit_code') if k in b];assert codes and all(type(x) is int and x==0 for x in codes)
 for name,digest in [(b['raw_log'],b['raw_log_sha256']),(b['source_snapshot'],b['source_snapshot_sha256'])]:add(name,digest,{'file':name,'sha256':digest})
 assert b['source_sha256_before']==b['source_sha256_after']==a['source']['sha256']
 assert len(a['all_public_declarations'])==a['public_theorem_count']
 text=path(a['source']['file']).read_text();shorts=re.findall(r'^theorem\s+([A-Za-z0-9_]+)',text,re.M);assert sorted(shorts)==sorted(n.rsplit('.',1)[1] for n in a['all_public_declarations'])
 assert not (ROOT/a['canonical_source']).exists()
 body=checked(a['original_semantic_peer']);assert body['errors']==[] and 'passed' in body['status']
runner='/tmp/root_tmp_lean27_runner_v3.py';add(runner,sha(runner),ref(runner))
packet={'status':'planned_unexecuted_eight_exact_reviewed_sources16_real_compiler_commands_required','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'prepared_by':ref(str(Path(__file__))),'source_count':8,'public_theorem_count':141,'planned_real_compiler_commands':16,'source_rows':rows,'original_input_packets':inputs,'explicit_original_byte_alias_rows':list(aliases.values()),'current55_guard_runner':ref(runner),'actual_compiler_helpers':{'standalone':ref('book/coverage/check_core_standalone.py'),'named':ref('book/coverage/check_core_named_build.py')},'scope':'Canonical byte copies plus actual standalone/named compilation only. Original semantic decisions, actual commands, times, failed trials and raw logs are retained verbatim. No owner installation, promotion, selection, aggregate or publication is claimed.'}
BASE.mkdir();p=BASE/'eight-source141-reviewed-canonical-pair-inputs-v1.json';p.write_text(json.dumps(packet,indent=2)+'\n');print(json.dumps({'input':str(p),'sha256':sha(str(p)),'sources':8,'exports':141,'explicit_original_alias_rows':len(aliases),'status':'prepared_draft_only_no_compilation'}))
