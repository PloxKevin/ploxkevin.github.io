from pathlib import Path
from types import SimpleNamespace
from datetime import datetime, timezone
import ast, copy, hashlib, importlib.util, json, tempfile, traceback
R=Path('/home/oxrexkevin/SafetyBased')
H=R/'book/coverage/checks/root_prepare_tmp_source65_owner29_context_v2.py'
D=R/'book/coverage/checks/future29-core/source65-owner29-context-producer-independent-modules-v1'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
ref=lambda p:{'file':str(p.relative_to(R)),'sha256':sha(p)}
assert sha(H)=='7dee4b9d8689d71d2bae7bdd91bd7599e624a2b1ea547b0932b4c8d6bab2ee07'
text=H.read_text(); tree=ast.parse(text)
spec=importlib.util.spec_from_file_location('isolated_context_producer_independent_modules',H); m=importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
assert sha(m.OLD_CONTEXT)==m.OLD_CONTEXT_SHA and sha(m.OLD_RUNNER)==m.OLD_RUNNER_SHA
actual=[]
for n,h,cmd in [
 ('reports/full-coverage/owner29-reviewed-candidate-integration-execution-v1.json','968004cf251bf5f0748e9fcb1070c79ccef79f766abe7e3851d3fe4c028b0439',['python3','book/coverage/checks/root_integrate_owner29_candidates_v1.py','--binding','book/coverage/checks/future29-core/current65-owner29-binding-v1.json','--binding-sha256','32b1b6780b083f0383ebc01f720a92bf9d3addb7799cccba6d4f857d5c67be2c','--apply']),
 ('reports/full-coverage/root-source65-final-owner-integration29-execution-v1.json','19b058e68decfa3bf5773ca7b5b1b8efcdde63da24de2bf0a342de92d4fc997c',['python3','book/coverage/validate.py','--output','reports/full-coverage/root-source65-final-owner-integration29-v1.json'])]:
 d=m.zero(n,h,cmd); actual.append(ref(R/n))
# Execute only the transformation statements, never main/prepare or the runner.
main=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='main')
start=next(i for i,n in enumerate(main.body) if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='template' for t in n.targets))
end=next(i for i,n in enumerate(main.body) if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='all_held' for t in n.targets))
ns=dict(vars(m)); ns['context_sha']='c'*64
exec(compile(ast.Module(body=main.body[start:end],type_ignores=[]),str(H)+'::isolated-render-only','exec'),ns)
rendered=ns['template']; ast.parse(rendered)
assert "command=['lake','env','lean',str(source)]" in rendered
assert "protected_selected29_proof_sources':1197" in rendered
assert "**context['held_current_source_sha256'],**context['owners_sha256']}" in rendered
assert "actual_installed29_selection" in rendered and "actual_frozen29_original_audit" in rendered
assert 'owner28 context' not in rendered and str(m.OLD_CONTEXT) not in rendered
fixtures=[]
def reject(label,fn):
 try: fn()
 except (AssertionError,KeyError,FileNotFoundError) as e:
  fixtures.append({'label':label,'scope':'isolated synthetic negative adapter only','rejected':True,'exception':type(e).__name__}); return
 raise AssertionError('negative guard accepted: '+label)
original_root=m.ROOT; original_zero=m.zero
with tempfile.TemporaryDirectory(prefix='modules-context29-negative-') as td:
 T=Path(td); m.ROOT=T
 (T/'helper.py').write_text('synthetic fixture helper, never executed\n'); (T/'raw.log').write_text('synthetic isolated output, no production evidence\n')
 (T/'outside-link').symlink_to('/etc/hosts')
 for label,n in [('absolute_path','/etc/hosts'),('parent_escape','../outside'),('noncanonical_path','a//b'),('symlink_outside','outside-link')]: reject(label,lambda n=n:m.safe(n))
 cmd=['python3','helper.py']; row={'status':'passed','actual_exit_code':0,'actual_command':cmd,'actual_workdir':str(T),'helper_sha256_before':{'helper.py':sha(T/'helper.py')},'helper_sha256_after':{'helper.py':sha(T/'helper.py')},'log':'raw.log','log_sha256':sha(T/'raw.log')}
 def zero_row(d):
  q=T/'synthetic-record.json';q.write_text(json.dumps(d));return original_zero('synthetic-record.json',sha(q),cmd)
 assert zero_row(row)==row
 changes=[('failed_status',{'status':'failed'}),('nonzero_exit',{'actual_exit_code':1}),('bool_exit_not_int',{'actual_exit_code':False}),('conflicting_exit_alias',{'exit_code':1}),('wrong_literal_command',{'actual_command':['python3','other.py']}),('conflicting_command_alias',{'command':['python3','other.py']}),('wrong_cwd',{'actual_workdir':str(T/'other')}),('conflicting_cwd_alias',{'cwd':str(T/'other')}),('helper_changed_after',{'helper_sha256_after':{'helper.py':'0'*64}}),('helper_string_schema',{'helper_sha256_before':'0'*64,'helper_sha256_after':'0'*64}),('stale_helper_digest',{'helper_sha256_before':{'helper.py':'0'*64},'helper_sha256_after':{'helper.py':'0'*64}}),('stale_raw_digest',{'log_sha256':'0'*64}),('conflicting_raw_alias',{'raw_log':'raw.log','raw_log_sha256':'0'*64}),('missing_raw_hash',{'log_sha256':None})]
 for label,delta in changes: reject(label,lambda delta=delta:zero_row({**row,**delta}))
 reject('empty_merged_map',lambda:m.merge({},{}))
 reject('conflicting_merged_hash',lambda:m.merge({'helper.py':'0'*64},{'helper.py':sha(T/'helper.py')}))
 reject('stale_merged_file',lambda:m.merge({}, {'helper.py':'0'*64}))
 # Baseline below is synthetic metadata ONLY. The sentinel stops before any
 # real verify/export native is read and before any context can be returned.
 proofs={f'verification/lean/SafeLearning/Fixture{i}.lean':{'sha256':str(i).zfill(64)} for i in range(1197)}
 selection={'proof_file_count':1197,'proof_files':proofs,'new_file_count':11}
 declarations=[{'name':f'Synthetic.fixture{i}'} for i in range(10114)]
 checks=[{'command':['lake','build'],'exit_code':0},{'command':['synthetic','other1'],'exit_code':0},{'command':['synthetic','other2'],'exit_code':0}]+[{'command':['lake','env','leanchecker',f'SafeLearning.Fixture{i}'],'exit_code':0,**({'reused_from':'synthetic prior receipt'} if i<1186 else {})} for i in range(1197)]
 audit={'status':'passed','proof_file_count':1197,'proof_sha256':{n:r['sha256'] for n,r in proofs.items()},'theorem_count':10114,'declarations':declarations,'axiom_dependencies':{d['name']:[] for d in declarations},'allowed_standard_axioms':['Classical.choice','Quot.sound','propext'],'checks':checks}
 def install(sel,au,mut_manifest=None):
  sp=T/m.SELECTION;ap=T/m.AUDIT;mp=T/m.MANIFEST
  for p in [sp,ap,mp]:p.parent.mkdir(parents=True,exist_ok=True)
  sp.write_text(json.dumps(sel));ap.write_text(json.dumps(au))
  manifest={'selection':m.SELECTION,'selection_sha256':sha(sp),'snapshot':m.SNAPSHOT,'proof_files':sel['proof_files'],'status':'formal_verification_passed_partial_coverage','successful_verification':{'proof_file_count':1197,'theorem_count':10114,'all_check_exit_codes':0,'report':m.AUDIT,'report_sha256':sha(ap)}}
  if mut_manifest: mut_manifest(manifest)
  mp.write_text(json.dumps(manifest));snap=T/(m.SNAPSHOT+'/reports/lean-verification/verification.json');snap.parent.mkdir(parents=True,exist_ok=True);snap.write_bytes(ap.read_bytes())
  return SimpleNamespace(selection_sha256=sha(sp),manifest_sha256=sha(mp),audit_sha256=sha(ap),verify_execution_sha256='0'*64,export_execution_sha256='0'*64)
 class Boundary(Exception):pass
 def stop_native(*a):raise Boundary('isolated pre-native boundary reached; no production preparation')
 m.zero=stop_native
 args=install(selection,audit)
 try:m.prepare(args)
 except Boundary:fixtures.append({'label':'synthetic baseline reaches mandatory native boundary','scope':'isolated adapter, NOT actual audit/context success','mandatory_boundary_reached':True})
 else:raise AssertionError('isolated baseline unexpectedly prepared context')
 cases=[
 ('wrong_selected_count',lambda s,a:s.update(proof_file_count=1196)),('wrong_new_count',lambda s,a:s.update(new_file_count=12)),('failed_audit_status',lambda s,a:a.update(status='failed')),('wrong_theorem_count',lambda s,a:a.update(theorem_count=10113)),('proof_digest_mismatch',lambda s,a:a['proof_sha256'].update({next(iter(a['proof_sha256'])):'f'*64})),('duplicate_declaration',lambda s,a:a['declarations'].__setitem__(0,copy.deepcopy(a['declarations'][1]))),('axiom_name_mismatch',lambda s,a:a['axiom_dependencies'].pop(next(iter(a['axiom_dependencies'])))),('forbidden_axiom',lambda s,a:a['axiom_dependencies'].__setitem__(next(iter(a['axiom_dependencies'])),['sorryAx'])),('wrong_standard_axioms',lambda s,a:a['allowed_standard_axioms'].append('sorryAx')),('wrong_check_count',lambda s,a:a['checks'].pop()),('failed_check',lambda s,a:a['checks'][0].update(exit_code=1)),('bool_check_code',lambda s,a:a['checks'][0].update(exit_code=False)),('missing_lake_build',lambda s,a:a['checks'][0].update(command=['lake','other'])),('duplicate_kernel_target',lambda s,a:a['checks'][3].update(command=a['checks'][4]['command'])),('wrong_reuse_split',lambda s,a:a['checks'][-1].update(reused_from='synthetic wrong reuse'))]
 for label,mut in cases:
  ss=copy.deepcopy(selection);aa=copy.deepcopy(audit);mut(ss,aa);args=install(ss,aa);reject(label,lambda args=args:m.prepare(args))
 args=install(selection,audit,lambda mm:mm['successful_verification'].update(theorem_count=10113));reject('false_manifest_verification_summary',lambda:m.prepare(args))
 m.ROOT=original_root;m.zero=original_zero
assert len(fixtures)==38, len(fixtures)
assert not m.CONTEXT.exists() and not m.RUNNER.exists()
D.mkdir(exist_ok=False)
(D/'isolated-rendered-owner29-runner-never-executed.py').write_text(rendered)
(D/'isolated-negative-fixture-decisions-v1.json').write_text(json.dumps({'synthetic_only':True,'not_production_evidence':True,'decisions':fixtures},indent=2)+'\n')
peer={'status':'passed_independent_source65_owner29_tmp_context_producer_full_code_and_guard_review','errors':[],'reviewer':'/root/modules_finish28','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':ref(H),'helper_sha256':sha(H),'entire_helper_and_original_runner_full_source_read':True,'unexecuted_v1_to_v2_delta_full_read':True,'actual_existing_owner29_native_guards_checked':actual,'isolated_negative_fixture_decisions':ref(D/'isolated-negative-fixture-decisions-v1.json'),'isolated_rendered_runner_ast_only':ref(D/'isolated-rendered-owner29-runner-never-executed.py'),'actual_future29_audit_or_export_inferred':False,'producer_prepare_or_apply_invoked':False,'compiler_started':False,'current_sources_or_owners_mutated':False,'coverage_complete':False,'actual_finalizer':None,'findings':['The producer requires exact real selected29 manifest, original audit, verify and export receipts before preparation; 1197 proofs/10114 distinct theorem names/1200 zero checks and exact 1186 reused plus11 fresh named kernels are checked.','Existing actual owner29 replacement schemas, original28 archives, native integration and global source65 count/status records were read and their real native zero guards checked.','Raw installed owners are held from working_inputs_sha256 and separately audited against exact integration candidates; frozen owner bytes remain separately pinned, permitting explicitly pruned frozen Applied metadata without replacing working raw bytes.','All31 current assets include29 HTML plusCSS/JS; source/project/snapshot/rawcheck-output/nativehelper/log pins are conflict checked before rendering.','The exact original approved runner invocation remains lake env lean without output/cache writes; rendered guard binds all pins, current source and owner maps before/after, with unused TMP source/snapshot/log/record and banned proof tokens.','38 isolated negative/boundary decisions exercise path escape, contradictory native aliases, stale helpers/logs, merged map conflict, audit counts/names/axioms/kernel targets/reuse and manifest success; no fixture is claimed as actual29 verification or production context.']}
P=D/'source65-owner29-context-producer-full-independent-modules-peer-v1.json';P.write_text(json.dumps(peer,indent=2)+'\n');print(json.dumps({'peer':ref(P),'fixture_count':len(fixtures),'status':peer['status']}))
