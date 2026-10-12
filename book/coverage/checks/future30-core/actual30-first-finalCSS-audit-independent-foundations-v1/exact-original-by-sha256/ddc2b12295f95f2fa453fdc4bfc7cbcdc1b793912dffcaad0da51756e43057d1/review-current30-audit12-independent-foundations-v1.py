from pathlib import Path
from datetime import datetime,timezone
from collections import Counter
import hashlib,json,re,sys,subprocess,copy
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased');OUT=Path('/tmp/current30-audit12-independent-foundations-findings-v1.json');assert not OUT.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def path(n):p=Path(n);return p if p.is_absolute() else R/p
def ref(n):p=path(n);return {'file':str(p),'sha256':sha(p),'bytes':p.stat().st_size}
closed={}
def add(n,h=None):
 p=path(n);actual=sha(p);assert h is None or actual==h,str(p);assert p.is_file()
 if p.is_relative_to(R):assert not p.is_symlink() and p.resolve().is_relative_to(R)
 closed[str(p)]=actual;return json.loads(p.read_bytes()) if p.suffix=='.json' else p.read_bytes()
def native(n,expected):
 d=add(n);assert d['status']=='passed' and type(d['actual_exit_code']) is int and d['actual_exit_code']==0 and d['actual_command']==expected and d['actual_workdir']==str(R) and d['helper_sha256_before']==d['helper_sha256_after'];add(d['log'],d['log_sha256'])
 for k,h in d['helper_sha256_before'].items():add(k,h)
 return d
p1='reports/full-coverage/lean-checkpoint-30/verification-original.json';p2='reports/full-coverage/lean-checkpoint-30-final-css-v1/verification-original.json'
a1=add(p1,'202ad21aa4a9f8e87a9dcebfdcec7a1a0ba415cf23eb37d794e65eef67a25a4c');a2=add(p2,'78915d21ec383430a5abea1c4b3cc9753dcfd5b2f94adb4834471459a3e2b00c')
runtimes=[R/'reports/full-coverage/runtime-checkpoint-30',R/'reports/full-coverage/runtime-checkpoint-30-final-css-v1'];exports=[R/'reports/full-coverage/lean-checkpoint-30',R/'reports/full-coverage/lean-checkpoint-30-final-css-v1']
sel=add('reports/full-coverage/checkpoint-30-selection.json','21c101dece9c614941e28174a5ff5ad6ead0fb271479f0c65cb732d10acdd196');assert len(sel['proof_files'])==1242 and sel['new_file_count']==45
assert a1['proof_sha256']==a2['proof_sha256']=={n:r['sha256'] for n,r in sel['proof_files'].items()}
assert a1['declarations']==a2['declarations'] and a1['axiom_dependencies']==a2['axiom_dependencies'] and a1['project_sha256']==a2['project_sha256']
assert [n for n in a1['source_sha256'] if a1['source_sha256'][n]!=a2['source_sha256'][n]]==['SafeLearning/style.css']
assert a1['lean_version']==a2['lean_version'] and a1['mathlib_revision']==a2['mathlib_revision'] and a1['dependency_revisions']==a2['dependency_revisions'] and a1['dependency_environment_identity']==a2['dependency_environment_identity']
ready=add('book/coverage/checks/future30-core/current79-canonical-pairs45-v1/actual-reviewed30-canonical-paired-readiness-v1.json','4ce14955fe77d0cc9447ff9963e79631ce8dbff3110683d261eb3c89eaa2cf7e');newmodules={'SafeLearning.'+Path(x['canonical_source']).stem for x in ready['sources']}
assert len(newmodules)==45
sys.path.insert(0,str(R/'book/coverage'));import lean_names;add('book/coverage/lean_names.py');declarations=[];imports={}
for n,h in a2['proof_sha256'].items():
 body=path(n).read_text();assert sha(path(n))==h;add(runtimes[1]/n,h);bare=lean_names.without_comments(body)
 assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by|run_elab|ofReduceBool|sorryAx)\b',bare)
 declarations += [{'name':x['name'],'file':n} for x in lean_names.declarations(body) if x['kind'] in ['theorem','lemma']]
 imports['SafeLearning.'+Path(n).stem]=[m for line in re.findall(r'^import[^\n]*',body,re.M) for m in line.split()[1:] if m.startswith('SafeLearning.')]
assert declarations==a2['declarations'] and len(declarations)==11080 and len({x['name'] for x in declarations})==11080
def closure(module):
 seen=set()
 def visit(m):
  if m in seen:return
  assert m in imports;mkey='verification/lean/'+m.replace('.','/')+'.lean';assert mkey in a2['proof_sha256'];seen.add(m)
  for dep in imports[m]:visit(dep)
 visit(module);return {'verification/lean/'+m.replace('.','/')+'.lean':a2['proof_sha256']['verification/lean/'+m.replace('.','/')+'.lean'] for m in sorted(seen)}
warning_counts=[];all_checks=[]
for index,(a,runtime,export) in enumerate(zip([a1,a2],runtimes,exports),1):
 assert a['status']=='passed' and a['proof_file_count']==len(a['proof_sha256'])==1242 and a['theorem_count']==len(a['axiom_dependencies'])==11080 and len(a['checks'])==1245
 assert set(a['allowed_standard_axioms'])=={'propext','Classical.choice','Quot.sound'} and all(set(ds)<={'propext','Classical.choice','Quot.sound'} for ds in a['axiom_dependencies'].values())
 for field in ['source_sha256','proof_sha256','project_sha256']:
  for n,h in a[field].items():add(runtime/n,h)
 agg=add(runtime/'verification/lean/SafeLearning.lean').decode();assert agg==''.join('import '+m+'\n' for m in sorted(imports))
 kchecks={c['module']:c for c in a['checks'] if 'module' in c};assert len(kchecks)==1242 and set(kchecks)==set(imports)
 fresh={m for m,c in kchecks.items() if c['evidence_mode']=='fresh_kernel_replay'};reused={m for m,c in kchecks.items() if c.get('reused_from')};assert len(fresh)==(45 if index==1 else 0) and len(reused)==(1197 if index==1 else 1242)
 if index==1:assert fresh==newmodules
 parent=add(runtime/'reports/lean-verification/reused-verification-original.json');parenthash=sha(runtime/'reports/lean-verification/reused-verification-original.json');assert parenthash==('4cf89c6cfb19ab13cea59ef2e775b6b8b2c1432d83f56f79b7547e91c772d8d3' if index==1 else sha(path(p1)))
 assert parent['dependency_revisions']==a['dependency_revisions'] and parent['lean_version']==a['lean_version'] and parent['dependency_environment_identity']==a['dependency_environment_identity']
 parentchecks={c['module']:c for c in parent['checks'] if 'module' in c}
 for m,c in kchecks.items():
  assert c['command']==['lake','env','leanchecker','-v',m] and type(c['exit_code']) is int and c['exit_code']==0
  raw=add(runtime/c['output_file'],c['log_sha256']);assert add(export/Path(c['output_file']).name,c['log_sha256'])==raw
  if m in reused:
   rf=c['reused_from'];assert rf['report_sha256']==parenthash and rf['prior_check_evidence_mode']==parentchecks[m]['evidence_mode'] and rf['verified_local_import_sha256']==closure(m)
   assert all(parent['proof_sha256'].get(n)==h for n,h in rf['verified_local_import_sha256'].items())
   execution=parentchecks[m]
   while execution.get('reused_from',{}).get('original_check'):execution=execution['reused_from']['original_check']
   assert rf['original_check']==execution and c['actual_workdir']==rf['actual_workdir']==execution['actual_workdir']
   assert c['command']==execution['command'] and c['elapsed_seconds']==execution['elapsed_seconds'] and c['log_sha256']==execution['log_sha256']
  else:assert c['actual_workdir']==str(runtime/'verification/lean')
  all_checks.append({'audit':index,'module':m,'evidence_mode':c['evidence_mode'],'original_elapsed_seconds':c['elapsed_seconds'],'actual_workdir':c['actual_workdir'],'original_log_sha256':c['log_sha256']})
 for c in a['checks']:
  assert type(c['exit_code']) is int and c['exit_code']==0 and type(c['elapsed_seconds']) in [int,float] and c['elapsed_seconds']>=0
  raw=add(runtime/c['output_file']);assert add(export/Path(c['output_file']).name)==raw
  if 'module' not in c:
   text=raw.decode();warning_counts.append({'audit':index,'command':c['command'],'location_first_warning_headers':len(re.findall(r'^.*:\d+:\d+: warning:',text,re.M)),'Lake_warning_first_headers':len(re.findall(r'^warning: .*:\d+:\d+:',text,re.M)),'full_raw_log':ref(runtime/c['output_file']),'original_elapsed_seconds':c['elapsed_seconds']})
 axiomraw=(runtime/'reports/lean-verification/axioms.log').read_text();parsed={n:[x.strip() for x in ds.split(',') if x.strip()] for n,ds in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",axiomraw)}
 parsed.update({n:[] for n in re.findall(r"'([^']+)' does not depend on any axioms",axiomraw)});assert parsed==a['axiom_dependencies']
 relocated=add(export/'verification.json');original=copy.deepcopy(relocated);origin=original.pop('audit_origin');assert origin['original_report_sha256']==sha(path(p1 if index==1 else p2))
 for c in original['checks']:
  if c['output_file'].startswith(str(export.relative_to(R))+'/'):c['output_file']=c['output_file'].replace(str(export.relative_to(R))+'/', 'reports/lean-verification/',1)
  rf=c.get('reused_from',{})
  if isinstance(rf.get('report'),str) and rf['report'].startswith(str(export.relative_to(R))+'/'):rf['report']=rf['report'].replace(str(export.relative_to(R))+'/', 'reports/lean-verification/',1)
 assert original==a
native1=native('reports/full-coverage/verify-runtime-checkpoint30-execution-v1.json',['python3','reports/full-coverage/runtime-checkpoint-30/verification/lean/verify.py','--reuse-kernel-from',str(R/'reports/full-coverage/checkpoint-29')])
native2=native('reports/full-coverage/verify-runtime-checkpoint30-final-css-execution-v1.json',['python3','reports/full-coverage/runtime-checkpoint-30-final-css-v1/verification/lean/verify.py','--reuse-kernel-from',str(runtimes[0])])
prep2=add('reports/full-coverage/checkpoint30-runtime-final-css-preparation-v1.json','3439419a18f91845e307318a61e618f2424e511e87c021ec247327267327f87e');assert prep2['copied_lake_build_artifact_count']==prep2['copied_earlier_snapshot_tree_count']==0 and prep2['selected_source_count']==1242 and prep2['site_asset_count']==31
native('reports/full-coverage/checkpoint30-runtime-final-css-preparation-execution-v1.json',['python3','book/coverage/checks/root_prepare_checkpoint30_runtime_v4.py','--selection-sha256','21c101dece9c614941e28174a5ff5ad6ead0fb271479f0c65cb732d10acdd196'])
native('reports/full-coverage/export-runtime-checkpoint30-final-css-execution-v1.json',['python3','book/coverage/export_runtime_audit30_v2.py','--actual-report-sha256','78915d21ec383430a5abea1c4b3cc9753dcfd5b2f94adb4834471459a3e2b00c'])
manifest=json.loads((runtimes[1]/'verification/lean/lake-manifest.json').read_bytes());assert [{'name':x['name'],'revision':x['rev']} for x in manifest['packages']]==a2['dependency_revisions']
for p in manifest['packages']:
 checkout=R/'verification/lean'/manifest['packagesDir']/p['name'];rev=subprocess.check_output(['git','-C',str(checkout),'rev-parse','HEAD'],text=True).strip();tree=subprocess.check_output(['git','-C',str(checkout),'rev-parse','HEAD^{tree}'],text=True).strip();dirty=subprocess.check_output(['git','-C',str(checkout),'status','--porcelain'],text=True);assert rev==p['rev'] and not dirty and tree==a2['dependency_environment_identity'][p['name']]['git_tree']
installed=add('reports/full-coverage/owner30-reviewed-candidate-integration-v2.json','34dc308f520cb6b866f7e17e17f6426a25df3a3677420be29df4b65794166963');aliases={}
for x in installed['exact_replacements']:
 assert sha(path(x['destination']))==x['candidate']['sha256'];add(x['candidate']['file'],x['candidate']['sha256']);add(x['original29_byte_copy']['file'],x['before_sha256']);aliases[str(path(x['destination']))]=x['candidate']
ledger=add('reports/full-coverage/lean-checkpoint-30/ledger-audit-working-v1.json');assert ledger['integrity_status']=='passed' and ledger['errors']==[] and ledger['mathematical_coverage_complete'] is False and ledger['counts']['material_review_statuses']=={'reviewed':4770,'pending':8004}
assert {k:ledger['counts']['statuses'][k] for k in ['exercise:complete_math','exercise:partial','exercise:pending']}=={'exercise:complete_math':535,'exercise:partial':8,'exercise:pending':13}
native('reports/full-coverage/owner30-global-ledger-execution-v1.json',['python3','book/coverage/validate.py','--output','reports/full-coverage/lean-checkpoint-30/ledger-audit-working-v1.json'])
find={'status':'passed_independent_actual_first_and_final_CSS_checkpoint30_source_proof_project_dependency_kernel_native_warning_and_installed_owner30_identity_review','reviewer':'/root/foundations_recovery28','review_finished_at_utc':datetime.now(timezone.utc).isoformat(),'original_first_actual_report':ref(p1),'original_final_CSS_actual_report':ref(p2),'full_original_native1':ref('reports/full-coverage/verify-runtime-checkpoint30-execution-v1.json'),'full_original_native2':ref('reports/full-coverage/verify-runtime-checkpoint30-final-css-execution-v1.json'),'both_original_reports_and_relocation_inverses_entire_dictionary_exact':True,'same1242_proof_sources_and11080_actual_public_names_and_axiom_sets':True,'current31assets_match_final_CSS_sourceonly_runtime_and_report':True,'only_current_site_asset_delta_between_audits':'SafeLearning/style.css','dependency_revisions_and_compiled_environment_identities_equal_in_prior29_first30_finalCSS30':True,'all_nine_dependency_actual_current_git_revisions_trees_and_clean_worktrees_checked':True,'dependency_artifact_full_rehash_not_repeated_by_reviewer':'Actual verifier1 and2 already hash complete dependency artifact environments before and after; this review independently reads their exact identities, verifies equality for all reused chains, and checks current dependency Git pins. No separate all-artifact rehash or compiler invocation.','first45_fresh_and1197_reused_kernel_checks':True,'final1242_reused_and0_fresh_kernel_checks':True,'all2484_kernel_raw_logs_exact_and_reused_original_command_cwd_elapsed_and_transitive_local_imports_read':True,'old_deleted_checkpoint_cwds_remain_historical_not_recopied_or_claimed_current':True,'both_normal_build_and_all11080_theorem_axiom_audits_genuinely_fresh_in_their_original_commands':True,'standard_axioms_only':['propext','Classical.choice','Quot.sound'],'full_non_kernel_raw_logs_and_actual_warning_headers':warning_counts,'original_actual_Root_times_preserved':{'audit1_seconds':native1['elapsed_seconds'],'audit2_seconds':native2['elapsed_seconds']},'exact_installed30_owner_aliases':aliases,'installed30_integration':ref('reports/full-coverage/owner30-reviewed-candidate-integration-v2.json'),'installed30_global_ledger':ref('reports/full-coverage/lean-checkpoint-30/ledger-audit-working-v1.json'),'partial_coverage_counts':ledger['counts'],'new_context_is_derived_from_actual_final_report_and_installed_receipts_not_old_d06':True,'compiler_source_parser_producer_or_publication_invoked_by_reviewer':False,'old_snapshot_or_lake_tree_copied':False,'live_source_owner_or_canonical_mutation':False,'coverage_complete':False,'errors':[],'required_evidence_artifacts_sha256':closed}
OUT.write_text(json.dumps(find,ensure_ascii=False,indent=2)+'\n');print(json.dumps({'findings':ref(OUT),'proofs':1242,'theorems':11080,'kernel_checks_verified':2484,'first_fresh':45,'final_fresh':0,'current_CSS_only_delta':True,'errors':[]}))
