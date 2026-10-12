from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,copy,sys,importlib.util
sys.dont_write_bytecode=True
EXPECTED_ACTUAL29_ORIGINAL_AUDIT_SHA256='PENDING_ROOT_REAL29_ORIGINAL_AUDIT_HASH'
R=Path('/home/oxrexkevin/SafetyBased');S=R/'reports/full-coverage/checkpoint-29';E=R/'reports/full-coverage/lean-checkpoint-29';B=Path('/tmp/actual29-export-kernel-provenance-independent-modules-v1');assert not B.exists();B.mkdir();cache={}
def sha(p):
 p=Path(p)
 if str(p)not in cache:cache[str(p)]=hashlib.sha256(p.read_bytes()).hexdigest()
 return cache[str(p)]
def ref(p):return {'file':str(Path(p).relative_to(R))if Path(p).is_relative_to(R)else str(p),'sha256':sha(p)}
def read(p):return json.loads(Path(p).read_bytes())
originalpath=S/'reports/lean-verification/verification.json';original=read(originalpath);exportpath=E/'verification.json';export=read(exportpath);original_export=E/'verification-original.json';assert originalpath.read_bytes()==original_export.read_bytes();assert sha(originalpath)==EXPECTED_ACTUAL29_ORIGINAL_AUDIT_SHA256
selection=read(R/'reports/full-coverage/checkpoint-29-selection.json');proofs={n:v['sha256']for n,v in selection['proof_files'].items()};assert len(proofs)==original['proof_file_count']==1197 and original['theorem_count']==10114
assert original['status']=='passed'and original['proof_sha256']==proofs and len(original['checks'])==1200
allowed={'propext','Classical.choice','Quot.sound'};assert set(original['allowed_standard_axioms'])==allowed
assert len(original['declarations'])==len(original['axiom_dependencies'])==10114;assert {x['name']for x in original['declarations']}==set(original['axiom_dependencies'])
assert all(type(x['exit_code'])is int and x['exit_code']==0 for x in original['checks'])
assert all(set(x)<=allowed for x in original['axiom_dependencies'].values())
# Exact relocation changes only the current report/output paths and appends audit_origin.
def relocate(report):
 d=copy.deepcopy(report)
 for c in d['checks']:
  for obj,key in [(c,'output_file'),(c.get('reused_from',{}),'report')]:
   v=obj.get(key)
   if isinstance(v,str)and v.startswith('reports/lean-verification/'):obj[key]=v.replace('reports/lean-verification/','reports/full-coverage/lean-checkpoint-29/',1)
 return d
def exact_export(d):
 x=copy.deepcopy(d);origin=x.pop('audit_origin');assert x==relocate(original)
 assert origin=={'original_report':'reports/full-coverage/lean-checkpoint-29/verification-original.json','original_report_sha256':sha(originalpath),'actual_workdir':str(S/'verification/lean'),'relocation':'Only report/output locations relocated; source hashes and original execution provenance retained.'}
exact_export(export)
outputs={}
for c in original['checks']:
 name=c['output_file'];assert name.startswith('reports/lean-verification/');a=S/name;b=E/Path(name).relative_to('reports/lean-verification');assert sha(a)==sha(b)
 if 'log_sha256'in c:assert sha(a)==c['log_sha256']
 outputs[str(b.relative_to(R))]=sha(b)
 u=c.get('reused_from',{})
 if u:
  a=S/u['report'];b=E/Path(u['report']).relative_to('reports/lean-verification');assert sha(a)==sha(b)==u['report_sha256'];outputs[str(b.relative_to(R))]=sha(b)
assert len(outputs)==len({c['output_file']for c in original['checks']})+1
root_integrity=read(E/'export-output-integrity-v1.json');assert root_integrity['status']=='passed'and root_integrity['paths_sha256']==outputs and root_integrity['actual_check_count']==len(original['checks']) and root_integrity['output_count']==len(outputs) and root_integrity['fresh_kernel_replays']==11 and root_integrity['exact_original_kernel_replays_reused']==1186
# Check every original audit output file was exported, including progress and unchanged prior report.
original_export_file_count=0
for p in (S/'reports/lean-verification').rglob('*'):
 if p.is_file():
  rel=p.relative_to(S/'reports/lean-verification');target=E/rel
  if str(rel)=='verification.json':target=original_export
  elif str(rel)=='kernel-progress.json':continue
  assert sha(p)==sha(target);original_export_file_count+=1
priorpath=S/'reports/lean-verification/reused-verification-original.json';prior=read(priorpath);assert priorpath.read_bytes()==(R/'reports/full-coverage/checkpoint-28/reports/lean-verification/verification.json').read_bytes()
assert prior['status']=='passed'and prior['proof_file_count']==1186 and prior['theorem_count']==9896
for key in ['lean_version','dependency_revisions','dependency_environment_identity']:assert prior[key]==original[key]
for key in ['verification/lean/lean-toolchain','verification/lean/lakefile.toml','verification/lean/lake-manifest.json']:assert prior['project_sha256'][key]==original['project_sha256'][key]
assert all(x['git_worktree_clean']is True for x in original['dependency_environment_identity'].values())
# Current source/exact-transitive-local-import closures are rebuilt independently from snapshot bytes.
source_text={}
for field in ['source_sha256','proof_sha256','project_sha256']:
 for n,h in original[field].items():assert sha(S/n)==h
for n in proofs:source_text[n]=(S/n).read_text()
def closure(module):
 seen={}
 def visit(m):
  key='verification/lean/'+m.replace('.','/')+'.lean';assert key in proofs
  if key in seen:return
  seen[key]=proofs[key]
  for line in re.findall(r'^import[^\n]*',source_text[key],re.M):
   for dep in line.split()[1:]:
    assert dep!='SafeLearning'
    if dep.startswith('SafeLearning.'):visit(dep)
 visit(module);return dict(sorted(seen.items()))
priorchecks={c['module']:c for c in prior['checks']if 'module'in c};currentchecks={c['module']:c for c in original['checks']if 'module'in c};assert len(currentchecks)==1197
fresh=[];reused=[]
def valid_reuse(c):
 u=c['reused_from'];cl=closure(c['module']);assert u['verified_local_import_sha256']==cl
 assert all(prior['proof_sha256'].get(n)==h for n,h in cl.items())
 older=priorchecks[c['module']];execution=older
 while execution.get('reused_from',{}).get('original_check'):execution=execution['reused_from']['original_check']
 assert u['original_check']==execution
 for key in ['command','exit_code','elapsed_seconds','module','log_sha256']:assert c[key]==execution[key]
 assert c['command']==['lake','env','leanchecker','-v',c['module']]and c['exit_code']==0
 assert c['actual_workdir']==u['actual_workdir']==execution.get('actual_workdir',str(R/'reports/full-coverage/checkpoint-28/verification/lean'))
 assert u['prior_report_workdir']==str(R/'reports/full-coverage/checkpoint-28/verification/lean')
 assert u['report']=='reports/lean-verification/reused-verification-original.json'and u['report_sha256']==sha(priorpath)
 assert u['prior_check_evidence_mode']==older.get('evidence_mode')
for module,c in currentchecks.items():
 assert c['command']==['lake','env','leanchecker','-v',module]
 if c['evidence_mode']=='fresh_kernel_replay':
  assert c['actual_workdir']==str(S/'verification/lean')and 'reused_from'not in c;fresh.append(module)
 elif c['evidence_mode']=='reused_identical_module_and_transitive_local_imports':valid_reuse(c);reused.append(module)
 else:raise AssertionError(c['evidence_mode'])
newfiles=set(proofs)-set(prior['proof_sha256']);assert len(newfiles)==11 and set(fresh)=={'SafeLearning.'+Path(n).stem for n in newfiles};assert len(reused)==1186
progress_original=read(S/'reports/lean-verification/kernel-progress.json');progress_export=read(E/'kernel-progress.json');assert progress_original['checks']==currentchecks
expectedprogress=copy.deepcopy(progress_original)
for c in expectedprogress['checks'].values():
 for obj,key in [(c,'output_file'),(c.get('reused_from',{}),'report')]:
  v=obj.get(key)
  if isinstance(v,str)and v.startswith('reports/lean-verification/'):obj[key]=v.replace('reports/lean-verification/','reports/full-coverage/lean-checkpoint-29/',1)
assert progress_export==expectedprogress
identity=progress_original['identity'];assert identity['dependency_environment_identity']==original['dependency_environment_identity']and identity['dependency_revisions']==original['dependency_revisions']and identity['lean_version']==original['lean_version']
assert identity['input_sha256']=={**original['source_sha256'],**original['proof_sha256'],**original['project_sha256'],'book/coverage/lean_names.py':sha(S/'book/coverage/lean_names.py')}
# Independently reconstruct all10114 public theorem/lemma names from exact selected source bytes.
spec=importlib.util.spec_from_file_location('actual29_independent_names',S/'book/coverage/lean_names.py');names=importlib.util.module_from_spec(spec);spec.loader.exec_module(names);declarations=[]
for n in sorted(proofs):
 declarations.extend({'name':x['name'],'file':n}for x in names.declarations(source_text[n])if x['kind']in {'theorem','lemma'})
assert declarations==original['declarations']
aggregate=(S/'verification/lean/SafeLearning.lean').read_text();assert sorted(aggregate.splitlines())==sorted('import SafeLearning.'+Path(n).stem for n in proofs)
axiom_source=S/'verification/lean/AxiomAudit.lean';assert axiom_source.read_text()=='import SafeLearning\n\n'+'\n'.join('#print axioms '+d['name']for d in declarations)+'\n'
def axiom_map(text):
 d={n:[x.strip()for x in deps.split(',')if x.strip()]for n,deps in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",text)}
 for n in re.findall(r"'([^']+)' does not depend on any axioms",text):d[n]=[]
 return d
assert axiom_map((E/'axioms.log').read_text())==original['axiom_dependencies'];assert (E/'lean-version.txt').read_text().strip()==original['lean_version']
# Three actual29 native outer executions are checked literally without substituting prior metadata.
natives={}
commands={'verify-checkpoint29-execution-v1.json':['python3','reports/full-coverage/checkpoint-29/verification/lean/verify.py','--reuse-kernel-from',str(R/'reports/full-coverage/checkpoint-28')],'export-checkpoint29-execution-v1.json':['python3','book/coverage/export_audit28_v1.py','--snapshot','reports/full-coverage/checkpoint-29','--output','reports/full-coverage/lean-checkpoint-29'],'export-integrity28-execution-v1.json':['python3','book/coverage/checks/root_check_export28_integrity_v1.py']}
for name,cmd in commands.items():
 p=R/'reports/full-coverage'/name;d=read(p);assert d['status']=='passed';codes=[d[k]for k in ['actual_exit_code','exit_code','actual_runner_exit_code']if k in d];assert codes and all(type(c)is int and c==0 for c in codes);assert d['actual_command']==cmd and d['actual_workdir']==str(R);assert d['helper_sha256_before']==d['helper_sha256_after']
 for n,h in d['helper_sha256_before'].items():assert sha(R/n)==h
 assert sha(R/d['log'])==d['log_sha256'];assert d['started_at_utc']<d['finished_at_utc']and d['elapsed_seconds']>0;natives[name]=ref(p)
# Direct actual-byte/native/schema review; no fixtures or producer invocation.
report={'status':'passed_independent_actual29_original_export_kernel_reuse_and_axiom_provenance_review','errors':[],'reviewer':'/root/modules_finish28','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'original_snapshot_report':ref(originalpath),'unchanged_exported_original_report':ref(original_export),'relocated_report':ref(exportpath),'current29_selection':ref(R/'reports/full-coverage/checkpoint-29-selection.json'),'original_prior28_report':ref(priorpath),'actual_outer_native_executions':natives,'native_current29_authority_is_report_proofSHA_and_selection_not_retained29_native_schema':True,'proof_file_count':1197,'public_names_reconstructed_and_raw_axiom_reparsed':10114,'fresh_kernel_modules':fresh,'original_kernel_checks_reused_exact':1186,'all_reused_transitive_local_import_closures_recomputed':True,'original_dependency_compiled_environment_identity_equals_current_identity':True,'compiled_dependency_environment_not_rehashed_again_by_peer':True,'native_verify_full_read_confirms_dependency_worktree_and_artifacts_checked_beforeafter':True,'checks':1200,'exported_raw_and_prior_report_outputs_checked':len(outputs),'all_original_export_files_checked_except_exactly_relocated_progress':original_export_file_count,'kernel_progress_exact_relocation_approved':True,'native_all_three_actual_exit_codes':0,'synthetic_fixtures_run':False,'actual_axiom_audit_source':ref(axiom_source),'all_standard_axioms_only':sorted(allowed),'raw_outputs_sha256':outputs,'no_compiler_or_audit_rerun':True,'no_source_owner_selection_export_pub_changes':True,'coverage_complete':False}
P=B/'actual29-export-kernel-provenance-independent-modules-peer-v1.json';P.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'peer':ref(P),'checked_outputs':len(outputs),'proof_files':1197,'theorems':10114,'fresh':11,'reused':1186,'synthetic_fixtures_run':False}))
