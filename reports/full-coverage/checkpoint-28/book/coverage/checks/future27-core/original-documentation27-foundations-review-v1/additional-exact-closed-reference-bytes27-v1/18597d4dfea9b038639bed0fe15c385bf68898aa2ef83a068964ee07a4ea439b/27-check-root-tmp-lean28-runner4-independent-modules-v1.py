from pathlib import Path
from datetime import datetime,timezone
from types import SimpleNamespace
import ast,hashlib,json,tempfile,copy,sys,contextlib,io,importlib.util
R=Path('/home/oxrexkevin/SafetyBased');H=Path('/tmp/root_tmp_lean28_runner_v4.py');O=Path('/tmp/modules-runner28-v4-independent-code-check-result-v1.json');assert not O.exists()
SHA=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert SHA(H)=='8fe26e9954800b4e104db5a079eb2e9295e3680064fe7ebaaa74b496e60ec49b'
v3=Path('/tmp/root_tmp_lean28_runner_v3.py');assert SHA(v3)=='d45c929dbc03191b38ae664d0a6021d2fccc58573b7d76e834d8080fc0c75130'
s=H.read_text();old=v3.read_text();assert s.replace("assert audit['checks']\nfor r in audit['checks']:zero(r)","assert audit['checks'] and all(type(r['exit_code']) is int and r['exit_code']==0 for r in audit['checks'])")==old
T=ast.parse(s);cut=next(i for i,n in enumerate(T.body) if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='runner_before' for t in n.targets));before_guard=next(i for i,n in enumerate(T.body) if isinstance(n,ast.Expr) and isinstance(n.value,ast.Call) and isinstance(n.value.func,ast.Name) and n.value.func.id=='guard');prefix=T.body[:cut];with_guard=T.body[:before_guard]
selectionn='reports/full-coverage/checkpoint-27-selection.json';selection=json.loads((R/selectionn).read_bytes());baseline=json.loads((R/'reports/full-coverage/checkpoint-26-selection.json').read_bytes());oldauditn='reports/full-coverage/checkpoint-26/reports/lean-verification/verification.json';oldaudit=json.loads((R/oldauditn).read_bytes());assert oldaudit['status']=='passed' and oldaudit['proof_file_count']==1167 and oldaudit['theorem_count']==9503
futureauditn='reports/full-coverage/checkpoint-27/reports/lean-verification/verification.json';futureactualn='reports/full-coverage/verify-checkpoint27-execution-v1.json';futurelogn='reports/full-coverage/verify-checkpoint27-execution-v1.log';verifyhelper='reports/full-coverage/checkpoint-27/verification/lean/verify.py';assert (R/verifyhelper).is_file()
spec=importlib.util.spec_from_file_location('runner28_fixture_names',R/'book/coverage/lean_names.py');names=importlib.util.module_from_spec(spec);spec.loader.exec_module(names)
newdecl=[d for n in set(selection['proof_files'])-set(baseline['proof_files']) for d in names.declarations((R/n).read_text()) if d['kind'] in ['theorem','lemma']];assert len(newdecl)==141
# Explicit synthetic pending-audit adapter only. The actual completed26 body
# remains unchanged; it supplies observed native field types, not a27 proof.
adapted=copy.deepcopy(oldaudit);adapted['proof_file_count']=1175;adapted['theorem_count']=9644;adapted['proof_sha256']={n:r['sha256'] for n,r in selection['proof_files'].items()};adapted['declarations']=copy.deepcopy(oldaudit['declarations'])+[{'name':d['name'],'kind':d['kind']} for d in newdecl]
for d in newdecl:adapted['axiom_dependencies'][d['name']]=[]
checks=[]
for d in oldaudit['checks']:
 if d.get('evidence_mode') in ['fresh_kernel_replay','reused_identical_module_and_transitive_local_imports']:
  q=copy.deepcopy(d);q['evidence_mode']='reused_identical_module_and_transitive_local_imports';checks.append(q)
assert len(checks)==1167
adapted['checks']=checks+[{'exit_code':0,'evidence_mode':'fresh_kernel_replay','source':'explicit synthetic additional27 audit fixture'} for _ in range(8)]
config_names=['verification/lean/lean-toolchain','verification/lean/lakefile.toml','verification/lean/lake-manifest.json']
assert all(SHA(R/n)==oldaudit['project_sha256'][n] for n in config_names)
virtual_log=b'EXPLICIT SYNTHETIC PENDING AUDIT CODE FIXTURE; NO LEAN EXECUTED\n'
virtual_actual={'actual_exit_code':0,'actual_command':['python3',verifyhelper,'--reuse-kernel-from',str(R/'reports/full-coverage/checkpoint-26')],'actual_workdir':str(R),'helper_sha256_before':{verifyhelper:SHA(R/verifyhelper)},'helper_sha256_after':{verifyhelper:SHA(R/verifyhelper)},'log':futurelogn,'log_sha256':hashlib.sha256(virtual_log).hexdigest()}
assert (R/futureauditn).is_file() and (R/futureactualn).is_file()
actual_audit=json.loads((R/futureauditn).read_bytes());actual_verify=json.loads((R/futureactualn).read_bytes());assert actual_audit['status']=='passed' and type(actual_verify['actual_exit_code']) is int and actual_verify['actual_exit_code']==0
# Negatives and mocked write-flow use copies of the real completed27 contracts.
adapted=copy.deepcopy(actual_audit);virtual_actual=copy.deepcopy(actual_verify);virtual_log=(R/futurelogn).read_bytes()
FIXTURES=[];base=Path(tempfile.mkdtemp(prefix='runner28v4-code-fixtures-'));sha_cache={}
def real_sha(p):
 if p not in sha_cache:sha_cache[p]=SHA(p)
 return sha_cache[p]
def fixture(name,result='passed'):FIXTURES.append({'name':name,'result':result,'scope':'isolated code fixture, no real Lean or aggregate proof'})
def case(name,mutate=None,run_flow=False,mode='success',expect_failure=False):
 folder=base/name;folder.mkdir();source=folder/'fixture-source.lean';source.write_text('-- EXPLICIT SYNTHETIC CODE FIXTURE\n');record=folder/'fixture-record.json';changes={futureauditn:copy.deepcopy(adapted),futureactualn:copy.deepcopy(virtual_actual)};vbytes={futurelogn:virtual_log};drift={'active':False};ns={'__name__':'isolated_runner28_code_fixture','__file__':str(H)}
 if mutate:mutate(changes,vbytes,source,record)
 def fake_read(n):return copy.deepcopy(changes[n]) if n in changes else json.loads((R/n).read_bytes())
 def fake_sha(p):
  p=Path(p)
  n=p.relative_to(R).as_posix() if p.is_relative_to(R) else None
  if drift['active'] and mode=='protected_changed' and n==next(iter(selection['proof_files'])):return '0'*64
  if drift['active'] and mode=='runner_changed' and p==H:return '0'*64
  if n in changes:return hashlib.sha256((json.dumps(changes[n],sort_keys=True,separators=(',',':'))+'\n').encode()).hexdigest()
  if n in vbytes:return hashlib.sha256(vbytes[n]).hexdigest()
  return real_sha(p) if p.is_relative_to(R) or p==H else SHA(p)
 def fake_run(command,**kwargs):
  assert command==['lake','env','lean',str(source)] and kwargs['cwd']==R/'verification/lean'
  kwargs['stdout'].write(b'EXPLICIT MOCK COMPILER OUTPUT FOR ISOLATED RUNNER WRITE-FLOW TEST\n');kwargs['stdout'].flush()
  if mode=='source_changed':source.write_text('-- changed isolated fixture source\n')
  drift['active']=True;return SimpleNamespace(returncode=1 if mode=='compiler_failure' else 0)
 saved=sys.argv;sys.argv=[str(H),str(source),str(record)];caught=None
 try:
  with contextlib.redirect_stdout(io.StringIO()):
   for node in (T.body if run_flow else with_guard):
    try:exec(compile(ast.Module(body=[node],type_ignores=[]),str(H),'exec'),ns)
    except SystemExit as e:
     if run_flow:caught=e.code;break
     raise
    if isinstance(node,ast.FunctionDef) and node.name=='read':ns['read']=fake_read
    if isinstance(node,ast.FunctionDef) and node.name=='sha':ns['sha']=fake_sha
    if isinstance(node,ast.Import):ns['subprocess']=SimpleNamespace(run=fake_run,STDOUT=-2)
   if not run_flow:ns['guard']()
 except(AssertionError,KeyError,ValueError,FileNotFoundError) as e:
  if not expect_failure:raise
  assert not record.exists() and not record.with_suffix('.log').exists() and not record.with_name(record.stem+'-source.lean').exists()
  fixture(name);return None
 finally:sys.argv=saved
 if expect_failure:raise AssertionError('fixture unexpectedly accepted: '+name)
 if run_flow:
  result=json.loads(record.read_bytes());assert result['protected_proof_sources']==1175 and result['unchanged_baseline26_selected_proof_sources']==1167 and result['unchanged_canonical_new27_proof_sources']==8 and result['unchanged_current55_book_assets']==31 and result['unchanged_installed27_live_owners']==5
  snap=Path(result['source_snapshot']);log=Path(result['raw_log']);assert SHA(snap)==result['source_snapshot_sha256'] and SHA(log)==result['raw_log_sha256']
  assert snap.read_bytes()==b'-- EXPLICIT SYNTHETIC CODE FIXTURE\n' and result['canonical_installation_or_aggregate_verification_claimed'] is False
  if mode=='success':assert caught==0 and result['actual_runner_exit_code']==0 and result['actual_exit_code']==0 and result['source_unchanged'] is True and result['protection_errors']==[]
  else:
   assert caught==1 and result['actual_runner_exit_code']==1 and result['status']=='failed_actual_tmp_lean_or_protection'
   if mode in ['protected_changed','runner_changed']:assert len(result['protection_errors'])==1
   if mode=='source_changed':assert result['source_unchanged'] is False and result['source_sha256_before']!=result['source_sha256_after']
   if mode=='compiler_failure':assert result['actual_exit_code']==1 and result['protection_errors']==[]
 fixture(name);return ns
ns=case('full_current_installed27_native_prefix_with_completed27_contract_copies')
for value in [False,True,0.0,'0',None,1,-1]:
 try:ns['zero']({'actual_exit_code':value})
 except AssertionError:fixture('strict_exit_reject_'+repr(value))
 else:raise AssertionError(value)
for d in [{'actual_exit_code':0,'exit_code':False},{'actual_exit_code':0,'exit_code':1},{'exit_code':0,'actual_exit_code':True},{}]:
 try:ns['zero'](d)
 except AssertionError:fixture('strict_all_present_exit_aliases_reject_'+repr(d))
 else:raise AssertionError(d)
ns['zero']({'actual_exit_code':0,'exit_code':0});fixture('strict_int0_exit_aliases_accept')
for fun,good,bad in [('native_command',['lake','build','x'],{'command':['wrong']}),('native_workdir',R,{'cwd':'/tmp/wrong'})]:
 d={'actual_command':good} if fun=='native_command' else {'actual_workdir':str(good)};d.update(bad)
 try:ns[fun](d,good)
 except AssertionError:fixture('conflicting_'+fun+'_aliases_reject')
 else:raise AssertionError(fun)
for n in ['/absolute','../escape','a/../b','a//b']:
 try:ns['safe'](n)
 except AssertionError:fixture('unsafe_relative_evidence_path_reject_'+n)
 else:raise AssertionError(n)
mutations=[('missing_completed27_original_audit',lambda d,b,s,r:d.__setitem__(futureauditn,{})),('future_audit_pending_status',lambda d,b,s,r:d[futureauditn].__setitem__('status','running')),('same_count_changed_audit_source_digest',lambda d,b,s,r:d[futureauditn]['proof_sha256'].__setitem__(next(iter(selection['proof_files'])),'0'*64)),('nonstandard_axiom_rejected',lambda d,b,s,r:d[futureauditn]['axiom_dependencies'].__setitem__(next(iter(d[futureauditn]['axiom_dependencies'])),['sorryAx'])),('bool_false_audit_check_exit',lambda d,b,s,r:d[futureauditn]['checks'][0].__setitem__('exit_code',False)),('conflicting_audit_check_exit_alias',lambda d,b,s,r:d[futureauditn]['checks'][0].__setitem__('actual_exit_code',1)),('wrong_actual_verification_command_alias',lambda d,b,s,r:d[futureactualn].__setitem__('command',['wrong'])),('conflicting_actual_verification_exit_alias',lambda d,b,s,r:d[futureactualn].__setitem__('exit_code',False)),('conflicting_actual_verification_workdir_alias',lambda d,b,s,r:d[futureactualn].__setitem__('cwd','/tmp/wrong')),('conflicting_actual_verification_log_alias',lambda d,b,s,r:d[futureactualn].__setitem__('raw_log','reports/full-coverage/other.log')),('conflicting_actual_verification_log_digest_alias',lambda d,b,s,r:d[futureactualn].__setitem__('raw_log_sha256','0'*64)),('existing_record_no_overwrite',lambda d,b,s,r:r.write_text('existing'))]
for name,mutate in mutations:
 if name=='existing_record_no_overwrite':
  # Initial existing-file rejection legitimately retains that existing record.
  folder=base/name;folder.mkdir();src=folder/'s.lean';src.write_text('--fixture');rec=folder/'r.json';rec.write_text('EXISTING UNCHANGED');argv=sys.argv;sys.argv=[str(H),str(src),str(rec)];n={ '__file__':str(H)}
  try:
   try:exec(compile(ast.Module(body=T.body[:next(i for i,node in enumerate(T.body) if isinstance(node,ast.FunctionDef) and node.name=='sha')],type_ignores=[]),str(H),'exec'),n)
   except AssertionError:pass
   else:raise AssertionError('overwrite guard accepted')
  finally:sys.argv=argv
  assert rec.read_text()=='EXISTING UNCHANGED';fixture(name)
 else:case(name,mutate=mutate,expect_failure=True)
for n in config_names:case('audit_project_identity_'+Path(n).name,mutate=lambda d,b,s,r,n=n:d[futureauditn]['project_sha256'].__setitem__(n,'0'*64),expect_failure=True)
for mode in ['success','compiler_failure','source_changed','protected_changed','runner_changed']:case('complete_mocked_writeflow_'+mode,run_flow=True,mode=mode)
# Honest native current prefix: it must wait for the real completed27 audit and
# actual wrapper. No synthetic adapter is described as a real result.
real_ready=False
if (R/futureactualn).is_file() and (R/futureauditn).is_file():
 a=json.loads((R/futureactualn).read_bytes());q=json.loads((R/futureauditn).read_bytes());real_ready=type(a.get('actual_exit_code')) is int and a['actual_exit_code']==0 and q.get('status')=='passed'
if real_ready:
 folder=base/'real_completed27_native_prefix';folder.mkdir();src=folder/'unused.lean';src.write_text('-- readonly prefix input');rec=folder/'unused.json';args=sys.argv;sys.argv=[str(H),str(src),str(rec)];n={'__file__':str(H),'__name__':'independent_actual_completed27_native_prefix'}
 try:
  for node in with_guard:exec(compile(ast.Module(body=[node],type_ignores=[]),str(H),'exec'),n)
  n['guard']()
 finally:sys.argv=args
 assert not rec.exists() and not rec.with_suffix('.log').exists() and not rec.with_name(rec.stem+'-source.lean').exists()
 real_status='passed_actual_completed27_native_prefix_and_all1175_current_protection_guards_no_compiler'
else:real_status='pending_actual_completed27_original_audit_and_actual_verification_wrapper_zero_not_yet_available'
findings=[Path('/tmp/root-tmp-lean28-runner1-static-findings-v1.json'),Path('/tmp/modules-runner28-v2-independent-static-findings-v1.json'),Path('/tmp/root-tmp-lean28-runner2-independent-static-findings-v1.json'),Path('/tmp/root-tmp-lean28-runner3-independent-static-findings-v1.json')]
closed={str(p):SHA(p) for p in [H,v3,Path('/tmp/root_tmp_lean28_runner_v2.py'),Path('/tmp/root_tmp_lean28_runner_v1.py'),*findings]};native_refs=[futureauditn,futureactualn,futurelogn,selectionn,'reports/full-coverage/checkpoint-26-selection.json','reports/full-coverage/root-source55-final-owner-integration27-v1.json','reports/full-coverage/owner27-reviewed-candidate-integration-v1.json','reports/full-coverage/owner27-reviewed-candidate-integration-execution-v1.json','book/coverage/checks/root-owner27-reviewed-candidate-bindings-v1.json','book/coverage/checks/future27-core/eight-source141-canonical-v1/eight-source141-actual-canonical-paired-readiness27-v1.json',oldauditn]
for n in native_refs:closed[n]=SHA(R/n)
result={'status':'passed_independent_runner28_v4_full_code_current_native_and_isolated_guard_fixture_review','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':{'file':str(H),'sha256':SHA(H)},'helper_sha256':SHA(H),'original_unexecuted_runner3':{'file':str(v3),'sha256':SHA(v3)},'entire_runner3_restored_by_one_strict_audit_exit_delta':True,'original_static_findings':[{'original':{'file':str(p),'sha256':SHA(p)},'entire_original_body_and_time':json.loads(p.read_bytes())} for p in findings],'native_completed27_prefix_status':real_status,'native_prefix_ready':real_ready,'fixtures':FIXTURES,'fixture_count':len(FIXTURES),'synthetic_adapter_scope':'Rejection fixtures use in-memory copies of the real completed27 audit/wrapper/log; the real unmodified native prefix is checked separately. No fixture result is aggregate proof evidence. Mock compiler returns execute no Lake or Lean; records lie in isolated TMP fixture directory and are not proof evidence.','fixture_directory':str(base),'protected_sources':1175,'baseline_sources':1167,'new_sources':8,'book_assets':31,'installed_owners':5,'closed_evidence_sha256':closed,'actual_lean_execution_claim':False,'release_condition':'Root must require separate real completed27 audit/native-prefix pass before compiler release; this code/fixture peer by itself authorizes no compiler launch.','scope':'Full independent source and current real installed27/selection/integration/16pair schemas read, strict guards and exact mocked snapshot/log/record writeflow tested. Root current55/owners/proofs remain untouched; old statuses/times and all unexecuted versions/findings preserved.'}
O.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':'passed','result':str(O),'sha256':SHA(O),'fixtures':len(FIXTURES),'native_prefix_status':real_status}))
