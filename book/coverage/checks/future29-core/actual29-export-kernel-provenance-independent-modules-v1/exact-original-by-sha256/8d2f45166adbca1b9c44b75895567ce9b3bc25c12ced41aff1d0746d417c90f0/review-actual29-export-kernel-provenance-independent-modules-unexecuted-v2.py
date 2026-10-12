from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,copy,sys,importlib.util
sys.dont_write_bytecode=True
EXPECTED_ACTUAL29_ORIGINAL_AUDIT_SHA256='PENDING_ROOT_REAL29_ORIGINAL_AUDIT_HASH'
R=Path('/home/oxrexkevin/SafetyBased');S=R/'reports/full-coverage/checkpoint-29';E=R/'reports/full-coverage/lean-checkpoint-29';B=Path('/tmp/actual29-export-kernel-provenance-independent-modules-v2');assert not B.exists();B.mkdir();cache={}
def sha(p):
 p=Path(p)
 if str(p)not in cache:cache[str(p)]=hashlib.sha256(p.read_bytes()).hexdigest()
 return cache[str(p)]
def ref(p):return {'file':str(Path(p).relative_to(R))if Path(p).is_relative_to(R)else str(p),'sha256':sha(p)}
def read(p):return json.loads(Path(p).read_bytes())
originalpath=S/'reports/lean-verification/verification.json';original=read(originalpath);exportpath=E/'verification.json';export=read(exportpath);original_export=E/'verification-original.json';assert originalpath.read_bytes()==original_export.read_bytes();assert sha(originalpath)==EXPECTED_ACTUAL29_ORIGINAL_AUDIT_SHA256
selectionpath=R/'reports/full-coverage/checkpoint-29-selection.json';selection=read(selectionpath);proofs={n:v['sha256']for n,v in selection['proof_files'].items()};proofcount=len(proofs);namecount=len(original['declarations']);checkcount=len(original['checks'])
manifestpath=R/'reports/full-coverage/checkpoint-29-manifest.json';manifest=read(manifestpath);assert {n:v['sha256']for n,v in manifest['proof_files'].items()}==proofs
assert proofcount==original['proof_file_count']==1197 and namecount==original['theorem_count']==10114 and checkcount==proofcount+3
assert original['status']=='passed'and original['proof_sha256']==proofs
assert manifest['status']=='formal_verification_passed_partial_coverage'and manifest['successful_verification']=={'proof_file_count':proofcount,'theorem_count':namecount,'all_check_exit_codes':0,'report':str(original_export.relative_to(R)),'report_sha256':sha(originalpath)}
allowed={'propext','Classical.choice','Quot.sound'};assert set(original['allowed_standard_axioms'])==allowed
assert len(original['axiom_dependencies'])==namecount;assert len({x['name']for x in original['declarations']})==namecount;assert {x['name']for x in original['declarations']}==set(original['axiom_dependencies'])
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
assert len(outputs)==len({c['output_file']for c in original['checks']}|{c['reused_from']['report']for c in original['checks']if c.get('reused_from')})
root_integrity=read(E/'export-output-integrity-v1.json');assert root_integrity['status']=='passed'and root_integrity['paths_sha256']==outputs and root_integrity['actual_check_count']==len(original['checks']) and root_integrity['output_count']==len(outputs) and root_integrity['original_report_sha256']==sha(originalpath)
# Check every original audit output file was exported, including progress and unchanged prior report.
original_export_file_count=0
for p in (S/'reports/lean-verification').rglob('*'):
 if p.is_file():
  rel=p.relative_to(S/'reports/lean-verification');target=E/rel
  if str(rel)=='verification.json':target=original_export
  elif str(rel)=='kernel-progress.json':continue
  assert sha(p)==sha(target);original_export_file_count+=1
priorpath=S/'reports/lean-verification/reused-verification-original.json';prior=read(priorpath);baseline_audit=R/'reports/full-coverage/checkpoint-28/reports/lean-verification/verification.json';assert sha(baseline_audit)=='7f12161869033e85af7927332eddee77cf62cdefbc5bb351150adec6b300adf8';assert priorpath.read_bytes()==baseline_audit.read_bytes()
assert prior['status']=='passed'and prior['proof_file_count']==1186 and prior['theorem_count']==9896
for key in ['lean_version','dependency_revisions','dependency_environment_identity']:assert prior[key]==original[key]
for key in ['verification/lean/lean-toolchain','verification/lean/lakefile.toml','verification/lean/lake-manifest.json']:assert prior['project_sha256'][key]==original['project_sha256'][key]
assert original['dependency_revisions']==[{'name':p['name'],'revision':p['rev']}for p in read(S/'verification/lean/lake-manifest.json')['packages']]
assert original['mathlib_revision']==next(p['revision']for p in original['dependency_revisions']if p['name']=='mathlib')
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
priorchecks={c['module']:c for c in prior['checks']if 'module'in c};currentchecks={c['module']:c for c in original['checks']if 'module'in c};assert len(currentchecks)==proofcount and len(priorchecks)==prior['proof_file_count']
nonkernel=[c for c in original['checks']if 'module'not in c];assert [c['command']for c in nonkernel]==[['lean','--version'],['lake','build'],['lake','env','lean',str(S/'verification/lean/AxiomAudit.lean')]]
assert all(type(c['elapsed_seconds'])in {int,float}and c['elapsed_seconds']>=0 for c in original['checks'])
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
 expected_u={'report':'reports/lean-verification/reused-verification-original.json','report_sha256':sha(priorpath),'actual_workdir':c['actual_workdir'],'prior_report_workdir':str(R/'reports/full-coverage/checkpoint-28/verification/lean'),'original_check':execution,'prior_check_evidence_mode':older.get('evidence_mode'),'verified_local_import_sha256':cl};assert u==expected_u
 expected_c=copy.deepcopy(execution);expected_c.update(output_file=c['output_file'],actual_workdir=c['actual_workdir'],evidence_mode='reused_identical_module_and_transitive_local_imports',reused_from=expected_u);assert c==expected_c
for module,c in currentchecks.items():
 assert c['command']==['lake','env','leanchecker','-v',module]
 if c['evidence_mode']=='fresh_kernel_replay':
  assert c['actual_workdir']==str(S/'verification/lean')and 'reused_from'not in c;fresh.append(module)
 elif c['evidence_mode']=='reused_identical_module_and_transitive_local_imports':valid_reuse(c);reused.append(module)
 else:raise AssertionError(c['evidence_mode'])
newfiles=set(proofs)-set(prior['proof_sha256']);assert len(newfiles)==len(fresh)==11 and set(fresh)=={'SafeLearning.'+Path(n).stem for n in newfiles};assert len(reused)==len(priorchecks)==1186;assert root_integrity['fresh_kernel_replays']==len(fresh)and root_integrity['exact_original_kernel_replays_reused']==len(reused)
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
commands={'verify-checkpoint29-execution-v1.json':['python3','reports/full-coverage/checkpoint-29/verification/lean/verify.py','--reuse-kernel-from',str(R/'reports/full-coverage/checkpoint-28')],'export-checkpoint29-execution-v1.json':['python3','book/coverage/export_audit29_v1.py','--snapshot','reports/full-coverage/checkpoint-29','--output','reports/full-coverage/lean-checkpoint-29'],'export-integrity29-execution-v1.json':['python3','book/coverage/checks/root_check_export29_integrity_v1.py']}
for name,cmd in commands.items():
 p=R/'reports/full-coverage'/name;d=read(p);assert d['status']=='passed';codes=[d[k]for k in ['actual_exit_code','exit_code','actual_runner_exit_code']if k in d];assert codes and all(type(c)is int and c==0 for c in codes);assert d['actual_command']==cmd and d['actual_workdir']==str(R);assert d['helper_sha256_before']==d['helper_sha256_after']and set(d['helper_sha256_before'])=={cmd[1]}
 for n,h in d['helper_sha256_before'].items():assert sha(R/n)==h
 assert sha(R/d['log'])==d['log_sha256'];assert d['started_at_utc']<d['finished_at_utc']and d['elapsed_seconds']>0
 assert d['baseline_selection']=={'file':'reports/full-coverage/checkpoint-28-selection.json','sha256':'e954d6a3f22139ec6ebafbe4164c46f184fe5e2c672860c9fce5829f73424632'}
 assert d['selection29_before']==d['selection29_after']==ref(selectionpath)
 assert sha(R/d['recorder']['file'])==d['recorder']['sha256'];natives[name]=ref(p)
# Direct actual-byte/native/schema review; no fixtures or producer invocation.
report={'status':'passed_independent_actual29_original_export_kernel_reuse_and_axiom_provenance_review','errors':[],'reviewer':'/root/modules_finish28','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'original_snapshot_report':ref(originalpath),'unchanged_exported_original_report':ref(original_export),'relocated_report':ref(exportpath),'current29_selection':ref(R/'reports/full-coverage/checkpoint-29-selection.json'),'original_prior28_report':ref(priorpath),'actual_outer_native_executions':natives,'native_current29_authority_is_report_proofSHA_and_actual_selection':True,'actual_export_updated_manifest':ref(manifestpath),'proof_file_count':proofcount,'public_names_reconstructed_and_raw_axiom_reparsed':namecount,'fresh_kernel_modules':fresh,'original_kernel_checks_reused_exact':len(reused),'all_reused_transitive_local_import_closures_recomputed':True,'original_dependency_compiled_environment_identity_equals_current_identity':True,'compiled_dependency_environment_not_rehashed_again_by_peer':True,'native_verify_full_read_confirms_dependency_worktree_and_artifacts_checked_beforeafter':True,'checks':checkcount,'exported_raw_and_prior_report_outputs_checked':len(outputs),'all_original_export_files_checked_except_exactly_relocated_progress':original_export_file_count,'kernel_progress_exact_relocation_approved':True,'native_all_three_actual_exit_codes':0,'synthetic_fixtures_run':False,'actual_axiom_audit_source':ref(axiom_source),'all_standard_axioms_only':sorted(allowed),'raw_outputs_sha256':outputs,'no_compiler_or_audit_rerun':True,'no_source_owner_selection_export_pub_changes':True,'coverage_complete':False}
P=B/'actual29-export-kernel-provenance-independent-modules-peer-v1.json';P.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'peer':ref(P),'checked_outputs':len(outputs),'proof_files':proofcount,'theorems':namecount,'fresh':len(fresh),'reused':len(reused),'synthetic_fixtures_run':False}))
