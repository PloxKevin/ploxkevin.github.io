"""Read-only exact frozen-draft/current-executed-helper delta review."""
from pathlib import Path
from datetime import datetime,timezone
import ast,copy,hashlib,json
ROOT=Path('/home/oxrexkevin/SafetyBased')
BASE=ROOT/'book/coverage/checks/future25-core'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
ref=lambda n:{'file':n,'sha256':H(ROOT/n)}
read=lambda n:json.loads((ROOT/n).read_text())
name='book/coverage/checks/run_root_barrier_control25_canonical_pair_v1.py'
old_name='reports/full-coverage/checkpoint-24/'+name
old_hash='f98e1a5ed31c6641ee15b3ecb00af0f0268bb0518d1cf5f125447320b1554ca6'
current_hash='53d47e49148a10f3dca53fff80514219e814764f557ae8f809c0d3dd28221fc6'
assert H(ROOT/name)==current_hash and H(ROOT/old_name)==old_hash
manifest_name='reports/full-coverage/checkpoint-24-manifest.json'
manifest=read(manifest_name)
assert H(ROOT/manifest_name)=='5e0a58f71b685edbd3bbf7c965a2fda3ffd18f8edfde75c5bf810c7bb63d18e0'
assert manifest['frozen_inputs_sha256'][name]==manifest['working_inputs_sha256'][name]==old_hash
old_text=(ROOT/old_name).read_text()
current_text=(ROOT/name).read_text()
old_ast=ast.parse(old_text)
current_ast=ast.parse(current_text)
extra=['check-root-barrier-control-material25*','run-root-barrier-control-material25*','check-root-core25-case-study-guidance*','run-root-core25-case-study-guidance*']
lists=[n for n in ast.walk(current_ast)if isinstance(n,ast.List)and all(isinstance(x,ast.Constant)for x in n.elts)and [ast.literal_eval(x)for x in n.elts]==['root-barrier-control-material25*','root_compile_tmp_core25*','CompleteBarrierControlMaterial25*','root-core25-case-study-guidance*']+extra]
assert len(lists)==1
lists[0].elts=lists[0].elts[:-4]
assert ast.dump(current_ast)==ast.dump(old_ast),'No other helper/protection/source/compiler change is eligible'
outer_name='reports/full-coverage/root-core25-canonical-pair-execution-v1.json'
outer=read(outer_name)
assert type(outer['actual_exit_code'])is int and outer['actual_exit_code']==0
assert outer['actual_command']==['python3',name] and outer['actual_workdir']==str(ROOT)
assert outer['helper_sha256_before']==outer['helper_sha256_after']=={name:current_hash}
assert H(ROOT/outer['log'])==outer['log_sha256']
ready_name='book/coverage/checks/future25-core/barrier-control/root-barrier-control25-canonical-readiness-v1.json'
ready=read(ready_name)
assert 'passed'in ready['status'] and ready['public_theorem_count']==7
assert outer['started_at_utc']<=ready['prepared_at_utc']<=outer['finished_at_utc']
source=ready['source']
assert H(ROOT/source['file'])==source['sha256']=='b76e4f44209d8a75da1d3fd62aae6402ccf0e6d78e2a5c3e7e97507c71e517a8'
assert H(ROOT/ready['source_snapshot']['file'])==ready['source_snapshot']['sha256']==source['sha256']
assert len(ready['actual_canonical_pair'])==2
expected=[['lake','env','lean','SafeLearning/CompleteBarrierControlMaterial25.lean'],['lake','build','SafeLearning.CompleteBarrierControlMaterial25']]
pairs=[]
for p,command in zip(ready['actual_canonical_pair'],expected):
    assert H(ROOT/p['file'])==p['sha256']
    record=read(p['file'])
    exits=[record[k]for k in ('actual_exit_code','exit_code')if k in record]
    assert exits and all(type(x)is int and x==0 for x in exits)
    commands=[record[k]for k in ('actual_command','command')if k in record]
    assert commands and all(x==command for x in commands)
    assert record['source']==source['file']
    assert record['source_sha256_before']==record['source_sha256_after']==source['sha256']
    assert H(ROOT/p['log']['file'])==p['log']['sha256']==record['log_sha256']
    pairs.append({'original_record':{'file':p['file'],'sha256':p['sha256']},'entire_original_record_and_time':record,'raw_log':p['log']})
for absolute,alias in ready['original_TMP_byte_copies'].items():
    assert H(ROOT/alias['file'])==alias['sha256']==H(Path(absolute))
assert all(any(Path(a).name.startswith(prefix)for a in ready['original_TMP_byte_copies'])for prefix in ['check-root-barrier-control-material25','run-root-barrier-control-material25','check-root-core25-case-study-guidance','run-root-core25-case-study-guidance'])
observation_name='book/coverage/checks/future25-core/root-baseline24-current-working-input-difference-observation-v1.json'
observation=read(observation_name)
assert observation['baseline24_manifest']==ref(manifest_name) and observation['total_prior_working_inputs']==40484
assert observation['live_owner25_installation_done']is False
immutable_differences=[r for r in observation['different_rows']if r['file']!='book/coverage/progress.json']
assert immutable_differences==[{'file':name,'original_frozen24_sha256':old_hash,'current_working_sha256':current_hash,'original_frozen24_byte_copy':old_name}]
report={'status':'independent_exact_single_frozen24_draft_to_actual25_working_helper_archive_delta_review_passed','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'Independent Foundations agent; Root authored original canonical helper','helper_sha256':current_hash,'original_frozen24_helper':{'file':old_name,'sha256':old_hash},'current_actual_working_helper':{'file':name,'sha256':current_hash},'exact_working_input_hash_update':{'file':name,'original_frozen24_sha256':old_hash,'current_working_sha256':current_hash,'original_frozen24_byte_copy':{'file':old_name,'sha256':old_hash}},'baseline24_manifest':ref(manifest_name),'entire_old_frozen_helper_source':old_text,'entire_current_actual_helper_source':current_text,'only_source_change_four_added_original_history_archive_patterns':extra,'actual_canonical_pair_outer_execution':ref(outer_name),'entire_original_actual_outer_record_and_time':outer,'actual_canonical_pair_outer_raw_log':ref(outer['log']),'actual_canonical_pair_readiness':ref(ready_name),'entire_original_readiness_body_and_time':ready,'original_native_pairs':pairs,'all_original_TMP_aliases_exact':len(ready['original_TMP_byte_copies']),'complete_root_working_difference_observation':ref(observation_name),'scope':'This peer approves only eligibility of the one explicitly pinned frozen draft/current genuinely executed helper metadata update. The entire frozen24 original hash and byte copy remain authoritative history. No selected source, mathematical statement, compiler command/protection logic, raw evidence or original record/time changed. It does not waive any other immutable input or approve a future integrator/binding version or owner installation; those require separate code and actual checks.'}
report['original_first_reader_failure_preserved']={'reason': 'The first AST reader evaluated every list including variable-valued compiler command lists. The second reader restricts the archive pattern search to literal-valued lists; reviewed code and evidence unchanged.', 'closed_originals': [{'file': 'book/coverage/checks/future25-core/check-baseline24-one-working-helper-delta-independent-foundations-v1.py', 'sha256': '451b8b57670e020dc95a25537811b6bd101996677a533a29e98c6c81b3d249d1'}, {'file': 'book/coverage/checks/future25-core/run-baseline24-one-working-helper-delta-independent-foundations-v1.py', 'sha256': 'a6f9c9e1fb52847688fb7baa43ed45eb09e237b7b9cbde7c2f26b1481f5c3c61'}, {'file': 'book/coverage/checks/future25-core/baseline24-one-working-helper-delta-independent-foundations-actual-v1.json', 'sha256': '4066b3234f44698af00c78aee3ec7bbd917c1191cefd6f76d2ae4351165626e0'}, {'file': 'book/coverage/checks/future25-core/baseline24-one-working-helper-delta-independent-foundations-actual-v1.log', 'sha256': '0dbffacae0a5a2a8028c3233c304f0351edf02592bf136bff904c35c3d799e5a'}]}
out=BASE/'baseline24-one-working-helper-delta-independent-foundations-observations-v2.json'
assert not out.exists()
out.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'status':report['status'],'observation':ref(str(out.relative_to(ROOT))),'single_authorized_working_path':name,'original_hash':old_hash,'current_hash':current_hash}))
