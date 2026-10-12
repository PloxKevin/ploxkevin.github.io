from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,importlib.util,json
R=Path('/home/oxrexkevin/SafetyBased')
H='book/coverage/checks/root_prepare_monitoring29_canonical_plan_v1.py'
P='book/coverage/checks/future29-core/monitoring29-canonical-plan-v1/monitoring29-canonical-plan-v1.json'
C='/tmp/root_tmp_lean_current65_owner28_context_v1.json'
Q='book/coverage/checks/future29-core/current65-canonical-pairs10-v1/actual-reviewed29-canonical-paired-readiness-v1.json'
N='reports/full-coverage/current65-canonical-pairs10-application29-execution-v1.json'
A='reports/full-coverage/monitoring29-canonical-plan-preparation-execution-v1.json'
REQ='book/coverage/checks/future29-core/monitoring-fixed-selector29-v1/core-monitoring-fixed-selector29-full-semantic-review-request-v1.json'
PEER='book/coverage/checks/future29-applied/monitoring-fixed-selector29-full-independent-v1/monitoring-fixed-selector29-full-source-independent-applied29-peer-v1.json'
RUN='book/coverage/checks/run_root29_reviewed_canonical_pairs_v1.py'
def p(n):return Path(n) if Path(n).is_absolute() else R/n
def sha(n):return hashlib.sha256(p(n).read_bytes()).hexdigest()
def read(n):return json.loads(p(n).read_bytes())
def ref(n):return {'file':n,'sha256':sha(n)}
def checked(r):assert sha(r['file'])==r['sha256'];return read(r['file'])
def zero(x):
 v=[x[k] for k in ['exit_code','actual_exit_code','actual_runner_exit_code'] if k in x];assert v and all(type(k) is int and k==0 for k in v)
 assert x.get('protection_errors',[])==[]
def actual(x,cmd,cwd):
 zero(x);assert x['status']=='passed'
 cs=[x[k] for k in ['actual_command','command'] if k in x];assert cs and all(k==cmd for k in cs)
 ds=[x[k] for k in ['actual_workdir','working_directory','cwd','workdir'] if k in x];assert ds and all(k==cwd for k in ds)
pins={H:'4cfed65c92618209b9576f5054c08afc607d4db604e2b567329c056df3875539',P:'8b8c7c592ae988e998cd1238a17c840a8c2b604cb8e831ceb3c31ee38bd9ca14',C:'10ca7b21579a0fcd69454c1a2c211156607bd59301b2ba0bfea11e3f2dc71e78',Q:'69a560ae42809ecaf8a11e0b6492fd411691e4c928a83684ced9c29936492917',N:'ccd8d152e579e60a97b09cf0d1d4477414133ae79aef8622d28cd987a70305c4',A:'988798d31809d7a492496e673b4fc5df2abb568477d768d2ab820363cfc56ee0',REQ:'298fa499667b537f2e95c0655f4854e4870303baeba756f36066b75f2f4bfff4',PEER:'72df0b38c651812d6d985810ed460f08ebd24434b02f029af8554a22422c4229',RUN:'d1d4358d68e183ad3d4fee48735d2bd99572a5c640c8be5d9ea753abc61af141'}
original=read(C)
def guard():
 for n,h in pins.items():assert sha(n)==h,n
 for fld in ['pins_sha256','held_current_source_sha256','owners_sha256']:
  for n,h in original[fld].items():assert sha(n)==h,n
 return copy.deepcopy(original)
start=datetime.now(timezone.utc).isoformat();before=guard();plan=read(P);context=checked(plan['context']);pairs=read(Q);native=read(N);author=read(A);req=read(REQ);peer=read(PEER)
actual(author,['python3',H],str(R));assert author['helper_sha256_before']==author['helper_sha256_after']=={H:pins[H]};assert sha(author['log'])==author['log_sha256']
out=json.loads(p(author['log']).read_text().splitlines()[-1]);assert out['plan']==ref(P) and (out['sources'],out['public_names'],out['theorem_lemma_count'])==(1,29,16)
assert (pairs['source_count'],pairs['public_theorem_count'],pairs['actual_compiler_command_count'])==(10,202,20) and pairs['errors']==[]
actual(native,['python3',RUN,'--plan','book/coverage/checks/future29-core/current65-canonical-plan10-v1.json','--plan-sha256','c52479b0decac7ad29160ec198e4c6ebce8c42948603939c55080ce71bbdb49b','--apply'],str(R));assert native['helper_sha256_before']==native['helper_sha256_after']=={RUN:pins[RUN]};assert sha(native['log'])==native['log_sha256']
additions={Q:sha(Q),N:sha(N),native['log']:native['log_sha256'],RUN:sha(RUN),REQ:sha(REQ),PEER:sha(PEER)}
source_map={s['canonical_source']:s for s in pairs['sources']};assert len(source_map)==10
for n,s in source_map.items():assert sha(n)==s['original_tmp_source']['sha256'];additions[n]=sha(n)
seen=set()
for r in pairs['actual_paired_records']:
 zero(r);n=r['source']['file'];kind=r['kind'];assert n in source_map and kind in ['standalone','named'] and (n,kind) not in seen;seen.add((n,kind))
 h=source_map[n]['original_tmp_source']['sha256'];assert r['source']['sha256']==h
 a=checked(r['actual_record']);cmd=['lake','env','lean','SafeLearning/'+Path(n).name] if kind=='standalone' else ['lake','build','SafeLearning.'+Path(n).stem]
 actual(a,cmd,str(R/'verification/lean'));assert a['source']==n and a['source_sha256_before']==a['source_sha256_after']==h and a['source_unchanged'] is True
 assert sha(r['raw_log']['file'])==r['raw_log']['sha256']==a['log_sha256'] and r['raw_log']['file']==a['log']
 assert sha(r['source_snapshot']['file'])==r['source_snapshot']['sha256']==h
 for k in ['actual_record','raw_log','source_snapshot']:additions[r[k]['file']]=r[k]['sha256']
assert len(seen)==20
assert context['pins_sha256']=={**original['pins_sha256'],**additions}
unchanged=copy.deepcopy(context);unchanged['pins_sha256']=copy.deepcopy(original['pins_sha256']);unchanged.pop('original_source65_context');unchanged['prepared_at_utc']=original['prepared_at_utc'];unchanged['scope']=original['scope'];assert unchanged==original
assert context['original_source65_context']==ref(C)
for n,h in context['pins_sha256'].items():assert sha(n)==h,n
assert peer['request']==ref(REQ) and peer['proof_source']==req['final_actual_source'];assert peer['errors']==[] and peer['status'].startswith('passed_')
assert peer['whole_exercise21_or_node1141_approved'] is False and all(type(d['approved']) is bool and d['approved'] and d['missing_clauses']==[] for d in peer['components'])
assert plan['status']=='exact_reviewed_new_canonical_pair_plan29_only' and (plan['source_count'],plan['public_theorem_count'],plan['public_name_count'])==(1,16,29)
assert plan['coverage_complete'] is False and plan['canonical_owner_selection_aggregate_or_publication_claimed'] is False
assert plan['helper']==ref(H) and plan['original_scope_plans']==[ref(REQ)] and len(plan['sources'])==1
row=plan['sources'][0];assert row['canonical_source']=='verification/lean/SafeLearning/CompleteCoreMonitoringFixedSelector29.lean' and not p(row['canonical_source']).exists()
assert row['owner']=='core' and row['original_tmp_source']==req['final_actual_source'] and row['original_actual_tmp_trial']==req['original_actual_trial'] and row['independent_source_peers']==[ref(PEER)]
spec=importlib.util.spec_from_file_location('monitor_review_names',R/'book/coverage/lean_names.py');names=importlib.util.module_from_spec(spec);spec.loader.exec_module(names);decls=names.declarations(p(row['original_tmp_source']['file']).read_text())
assert decls==row['public_declarations']==req['source_level_public_declarations'] and len(decls)==29 and sum(d['kind'] in ['theorem','lemma'] for d in decls)==16
trial=checked(row['original_actual_tmp_trial']);zero(trial);assert trial['source_sha256_before']==trial['source_sha256_after']==trial['source_snapshot_sha256']==row['original_tmp_source']['sha256'];assert sha(trial['source_snapshot'])==trial['source_snapshot_sha256'] and sha(trial['raw_log'])==trial['raw_log_sha256']
assert row['original_review_time_and_TMP_command_cwd_status_retained'] is True and row['fresh_canonical_records_pending'] is True
assert guard()==before
output={'status':'passed_independent_full_monitoring29_supplemental_plan_native_context_binding_review_foundations','errors':[],'started_at_utc':start,'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewed_helper':ref(H),'plan':ref(P),'supplemental_context':plan['context'],'original65_context':ref(C),'actual_author_preparation':ref(A),'actual_ten_pair_readiness':ref(Q),'actual_ten_pair_outer_execution':ref(N),'request':ref(REQ),'original_full_source_peer':ref(PEER),'source_public_and_theorem_counts':[1,29,16],'all20_existing_native_commands_and_added_pins_verified':True,'all_original_context_fields_and_original_review_command_status_body_times_retained':True,'code_findings':[],'fresh_monitoring_canonical_execution_pending':True,'whole_exercise21_or_node1141_approved':False,'coverage_complete':False,'scope':'Full scoped helper/read-only generated plan/context and genuine author prerequisite chain; prior mathematical peer is bound unchanged, not redecided. No producer, compiler, source/owner or publication action.'}
Path('/tmp/monitoring29-supplemental-plan-independent-foundations-findings-v1.json').write_text(json.dumps(output,indent=2)+'\n');print(json.dumps(output))
