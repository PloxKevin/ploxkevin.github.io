from pathlib import Path
from datetime import datetime,timezone
import ast,copy,hashlib,importlib.util,json,sys,tempfile
R=Path('/home/oxrexkevin/SafetyBased');S=R/'book/coverage/prepare_checkpoint28_selection_v4.py';T=R/'book/coverage/retain_baseline_inputs28_v3.py';N=R/'book/coverage/lean_names.py'
OUT=Path('/tmp/selection28-selector4-independent-foundations-findings-v3.json')
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def j(p):return json.loads(p.read_bytes())
def ref(p):return {'file':str(p.relative_to(R))if p.is_relative_to(R)else str(p),'sha256':h(p)}
assert h(S)=='339984997eb673b1367431f2980ed92bbcfd496990ca5d30bb92d010eab85729'and h(T)=='e3014dd7e7951d74b7c87f082f0d7395825bc3d61b90e630709f71794dbc23e8'and h(N)=='9e00c114c57a2bb05939a21bee09679188aa97c855a8d10e61b160f31e10f07d'and not OUT.exists()
start=datetime.now(timezone.utc).isoformat();A=Path('/tmp/selection28-retainer3-independent-foundations-actual-v2.json');F=Path('/tmp/selection28-retainer3-independent-foundations-findings-v2.json')
a=j(A);f=j(F);assert a['status']=='passed'and type(a['actual_exit_code'])is int and a['actual_exit_code']==0 and a['protection_errors']==[]and a['checker_sha256_before']==a['checker_sha256_after']
assert h(Path(a['checker']['file']))==a['checker']['sha256']and h(Path(a['raw_log']))==a['raw_log_sha256']
assert f['errors']==[]and f['genuine_complete_baseline_retainer']['original_frozen_inputs']==48662 and f['genuine_complete_baseline_retainer']['original_sources']==1175 and f['genuine_complete_baseline_retainer']['production_or_review_contentmap_written']is False
assert f['retainer']==ref(T)and f['parser_dependency']==ref(N)and f['actual_source_name_index']['public_theorem_lemma_names']==9896
sys.path.insert(0,str(R/'book/coverage'));spec=importlib.util.spec_from_file_location('selection28_exact4_independent',S);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
obs=[]
def reject(name,fn):
 try:fn()
 except (AssertionError,KeyError,ValueError,TypeError):obs.append({'fixture':name,'rejected':True});return
 raise AssertionError('Expected rejection: '+name)
cmd=['lake','build','SafeLearning.Example'];cwd=str(R/'verification/lean')
good={'exit_code':0,'actual_exit_code':0,'actual_runner_exit_code':0,'command':cmd,'actual_command':cmd,'actual_workdir':cwd,'working_directory':cwd,'workdir':cwd,'cwd':cwd,'status':'passed'}
m.native_record(good,cmd,cwd);obs.append({'fixture':'selector4_all_native_aliases_positive','passed':True})
for key in ('exit_code','actual_exit_code','actual_runner_exit_code'):
 for v in (False,1,'0'):
  x=dict(good);x[key]=v;reject('selector4_'+key+'_'+repr(v),lambda x=x:m.native_record(x,cmd,cwd))
for key in ('command','actual_command'):
 x=dict(good);x[key]=['false'];reject('selector4_conflicting_'+key,lambda x=x:m.native_record(x,cmd,cwd))
for key in ('actual_workdir','working_directory','workdir','cwd'):
 x=dict(good);x[key]='/tmp/conflicting';reject('selector4_conflicting_'+key,lambda x=x:m.native_record(x,cmd,cwd))
x=dict(good);x['status']='failed';reject('selector4_failed_status',lambda:m.native_record(x,cmd,cwd))
ready=j(R/'book/coverage/checks/future28-core/current60-canonical-pairs-v1/actual-current60-canonical-paired-readiness28-v1.json');r2=j(R/'book/coverage/checks/future28-core/current60-commissioning17-canonical-pair-v1/actual-current60-commissioning17-canonical-paired-readiness28-v1.json')
foundation=j(R/'book/coverage/checks/future28-foundations/current60-owner28-v1/foundations28-current60-final-offer-v1.json');name=next(iter(foundation['proof_files']));pair=[p for p in ready['actual_paired_records']if p['source']['file']==name];proof=foundation['proof_files'][name]
assert m.proof_evidence(proof,pair,foundation['required_evidence_artifacts_sha256'])==proof['evidence_sha256'];obs.append({'fixture':'selector4_actual_foundation_original_full_dictionary_preserved','passed':True})
for key in ('actual_record','raw_log','source_snapshot'):
 bad=copy.deepcopy(proof);bad['evidence_sha256'].pop(pair[0][key]['file']);reject('selector4_dictionary_requires_original_'+key,lambda bad=bad:m.proof_evidence(bad,pair,foundation['required_evidence_artifacts_sha256']))
reject('selector4_empty_dictionary_not_silently_derived',lambda:m.proof_evidence({'evidence_sha256':{}},pair,foundation['required_evidence_artifacts_sha256']))
pair=r2['actual_paired_records'];closure={p[k]['file']:p[k]['sha256']for p in pair for k in ('actual_record','raw_log','source_snapshot')};nativeproof={'evidence_sha256':next(p['actual_record']['sha256']for p in pair if p['kind']=='standalone')}
assert m.proof_evidence(nativeproof,pair,closure)==closure;obs.append({'fixture':'selector4_actual_native_string_alone_derives_pair_references','passed':True})
for label,p in [('tuple',tuple(pair)),('missing_named',pair[:1]),('three_rows',pair+[pair[0]]),('duplicate_kind',[pair[0],pair[0]])]:reject('selector4_pair_'+label,lambda p=p:m.proof_evidence(nativeproof,p,closure))
reject('selector4_non_dictionary_closure',lambda:m.proof_evidence(nativeproof,pair,[]))
for key in ('actual_record','raw_log','source_snapshot'):
 missing=dict(closure);missing.pop(pair[0][key]['file']);reject('selector4_native_missing_closure_'+key,lambda missing=missing:m.proof_evidence(nativeproof,pair,missing))
wrong=dict(nativeproof,evidence_sha256='0'*64);reject('selector4_native_wrong_standalone_actual_sha',lambda:m.proof_evidence(wrong,pair,closure))
tree=ast.parse(S.read_text());prep=next(x for x in tree.body if isinstance(x,ast.FunctionDef)and x.name=='prepare')
depassert=next(x for x in ast.walk(prep)if isinstance(x,ast.Assert)and "plan['helpers_sha256']"in ast.unparse(x.test))
depcode=compile(ast.Expression(depassert.test),'<exact-selector4-dependency-assert>','eval');deps={str(p.relative_to(R)):h(p)for p in (S,T,N)}
assert eval(depcode,{'plan':{'helpers_sha256':deps},'peer':{'reviewed_helpers_sha256':deps},'dependencies':deps})
obs.append({'fixture':'exact_selector4_retainer3_parser_dependency_set_positive','passed':True})
for label,bad in [('missing_parser',{n:s for n,s in deps.items()if n!=str(N.relative_to(R))}),('wrong_retainer',dict(deps,**{str(T.relative_to(R)):'0'*64})),('extra_dependency',dict(deps,**{'book/coverage/unreviewed.py':'0'*64}))]:
 assert not eval(depcode,{'plan':{'helpers_sha256':bad},'peer':{'reviewed_helpers_sha256':bad},'dependencies':deps});obs.append({'fixture':'dependency_'+label,'rejected':True})
bad=dict(deps,**{str(S.relative_to(R)):'0'*64});assert not eval(depcode,{'plan':{'helpers_sha256':deps},'peer':{'reviewed_helpers_sha256':bad},'dependencies':deps});obs.append({'fixture':'dependency_peer_different_selector_sha','rejected':True})
destination_asserts=[x for x in prep.body if isinstance(x,ast.Assert)and 'safe(DESTINATION).exists()'in ast.unparse(x.test)]
assert len(destination_asserts)==2
with tempfile.TemporaryDirectory(prefix='selector4-isolated-output-guards-')as td:
 ctx=Path(td);safe=lambda n:ctx/n
 scope={'safe':safe,'DESTINATION':'selection.json','CONTENT_MAP':'contentmap.json'}
 for x in destination_asserts:
  code=compile(ast.fix_missing_locations(ast.Module(body=[x],type_ignores=[])),'<exact-selector4-output-collision-assert>','exec')
  exec(code,scope)
  for label in ('DESTINATION','CONTENT_MAP'):
   p=safe(scope[label]);p.write_text('exact existing fixture bytes')
   reject('selector4_output_collision_'+str(x.lineno)+'_'+label,lambda code=code:exec(code,scope));assert p.read_text()=='exact existing fixture bytes';p.unlink()
sizes=[x for x in prep.body if isinstance(x,ast.Assert)and ('len(payload)'in ast.unparse(x.test)or 'len(retained' in ast.unparse(x.test))]
assert len(sizes)==2
class Length:
 def __init__(self,n):self.n=n
 def __len__(self):return self.n
for x in sizes:
 code=compile(ast.fix_missing_locations(ast.Module(body=[x],type_ignores=[])),'<exact-selector4-size-assert>','exec')
 exec(code,{'payload':Length(99_999_999),'retained':{'payload':Length(99_999_999)}})
 reject('selector4_payload_size_limit_line_'+str(x.lineno),lambda code=code:exec(code,{'payload':Length(100_000_000),'retained':{'payload':Length(100_000_000)}}))
readonly=next(x for x in prep.body if isinstance(x,ast.If)and ast.unparse(x.test)=='not apply');retention=next(x for x in prep.body if isinstance(x,ast.Assign)and isinstance(x.value,ast.Call)and ast.unparse(x.value.func)=='retain')
assert retention.lineno<readonly.lineno and all(x.lineno<readonly.lineno for x in sizes)
assert all(x.lineno>readonly.lineno for x in ast.walk(prep)if isinstance(x,ast.Call)and isinstance(x.func,ast.Attribute)and x.func.attr in ('open','mkdir','write'))
sourceasserts=[x for x in prep.body if isinstance(x,ast.For)and ast.unparse(x.iter)=='selected.items()'];assert len(sourceasserts)==2 and sourceasserts[-1].lineno<readonly.lineno
obs.append({'fixture':'selector4_full_preflight_pure_payload_source_sha_and_output_checks_precede_readonly_return','passed_static_control_flow':True})
out={'status':'passed_full_independent_selection28_selector4_retainer3_native_guards_and_complete_pure_baseline_retention_review','errors':[],'reviewer':'/root/foundations_recovery28','reader_started_at_utc':start,'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':ref(S),'retainer':ref(T),'parser_dependency':ref(N),'reviewed_helpers_sha256':deps,'full_source_lines_read':{str(p.relative_to(R)):len(p.read_text().splitlines())for p in (S,T,N)},'fresh_selector4_fixture_count':len(obs),'fresh_selector4_fixture_observations':obs,'prior_common_native_guard_and_real_retainer_fixture_count':f['fixture_count'],'prior_common_fixture_findings':ref(F),'actual_genuine_pure_retention_reader_execution':ref(A),'actual_genuine_pure_retention_reader_log':ref(Path(a['raw_log'])),'genuine_complete_baseline_retainer':f['genuine_complete_baseline_retainer'],'actual_source_name_index':f['actual_source_name_index'],'prior_actual_original_reader1_interruption':f['original_reader1_interrupted_for_own_masked_negative_fixture'],'complete_genuine_production_selection_plan_preflight_executed':False,'fresh_actual_plan_preflight_pending_root_owner28_integration_and_global_integrity':True,'production_selector_or_retainer_writer_executed':False,'coverage_complete':False,'scope':'Full selector4/retainer3/parser code review; fresh strict selector4 guards, dictionary preservation, native string derivation, exact dependencies, output collisions and sizes. Genuine unmodified complete1175/48662 pure retainer3 execution and actual1186 source-name/hash guard are bound to separate original reader2 native times; not retimed. A fresh unmodified prepare(False) with the eventual real Root production plan remains required.'}
with OUT.open('x')as file:json.dump(out,file,indent=2);file.write('\n')
print(json.dumps({'findings':ref(OUT),'fresh_selector4_fixture_count':len(obs),'bound_genuine_pure_retention':ref(A),'actual_production_plan_preflight_pending':True}))
