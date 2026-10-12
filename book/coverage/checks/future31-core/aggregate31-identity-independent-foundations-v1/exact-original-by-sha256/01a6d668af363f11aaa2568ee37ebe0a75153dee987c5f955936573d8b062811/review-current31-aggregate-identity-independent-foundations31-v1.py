from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json,re,subprocess,sys
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased');OUT=Path('/tmp/current31-aggregate-identity-independent-foundations31-findings-v1.json')
RT=R/'reports/full-coverage/runtime-checkpoint-31-source81-v1';REPORT=RT/'reports/lean-verification/verification.json'
def path(n):return Path(n) if Path(n).is_absolute() else R/n
def sha(p):return hashlib.sha256(path(p).read_bytes()).hexdigest()
def ref(p):
 p=path(p);return {'file':str(p.relative_to(R)) if p.is_relative_to(R) else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
closed={}
def add(p,h=None):
 p=path(p);actual=sha(p);assert h is None or actual==h,str(p)
 assert p.is_file();closed[str(p.relative_to(R)) if p.is_relative_to(R) else str(p)]=actual
 return json.loads(p.read_bytes()) if p.suffix=='.json' else p.read_bytes()
a=add(REPORT,'91e60eb646bc337f09bbab93631cdbf73f67fb5affb5b11da397ad0b8bf4c344')
sel=add('reports/full-coverage/checkpoint-31-selection.json','cfe49bb94bf13fe8e464df60213a6639ffb99e63383f2f9300b93ef8a21d33da')
old=add('reports/full-coverage/lean-checkpoint-30-final-css-v1/verification-original.json','78915d21ec383430a5abea1c4b3cc9753dcfd5b2f94adb4834471459a3e2b00c')
priorpeer=add('book/coverage/checks/future30-core/actual30-first-finalCSS-audit-independent-foundations-v1/actual30-first45fresh-and-finalCSS1242reuse-source-project-dependency-native-and-owner30-identity-independent-foundations30-closed-peer-v1.json')
assert priorpeer['status'].startswith('passed') and priorpeer['errors']==[]
assert a['status']=='passed' and a['proof_file_count']==len(a['proof_sha256'])==1248 and a['theorem_count']==len(a['declarations'])==len(a['axiom_dependencies'])==11184 and len(a['checks'])==1251
assert a['proof_sha256']=={n:x['sha256'] for n,x in sel['proof_files'].items()}
assert sel['new_file_count']==6 and all(a['proof_sha256'][n]==h for n,h in old['proof_sha256'].items())
ready=add('book/coverage/checks/future31-core/current81-canonical-pairs6-v1/actual-reviewed31-canonical-paired-readiness-v1.json','c18752bbf4b29ef8218cb28d990aad7edfcf0220babe2bacbafb3101bde43520')
newfiles={x['canonical_source'] for x in ready['sources']};assert newfiles==set(a['proof_sha256'])-set(old['proof_sha256']) and len(newfiles)==6
assert sum(x['public_theorem_count'] for x in ready['sources'])==104
assert a['allowed_standard_axioms']==old['allowed_standard_axioms'] and set(a['allowed_standard_axioms'])=={'propext','Classical.choice','Quot.sound'}
assert all(set(v)<={'propext','Classical.choice','Quot.sound'} for v in a['axiom_dependencies'].values())
assert all(a['axiom_dependencies'][n]==v for n,v in old['axiom_dependencies'].items())
assert a['lean_version']==old['lean_version'] and a['mathlib_revision']==old['mathlib_revision'] and a['dependency_revisions']==old['dependency_revisions'] and a['dependency_environment_identity']==old['dependency_environment_identity']
for field in ['source_sha256','proof_sha256','project_sha256']:
 for n,h in a[field].items():assert sha(n)==h;add(RT/n,h)
assert len(a['source_sha256'])==31
source_changes={n: {'before':h,'after':a['source_sha256'][n]} for n,h in old['source_sha256'].items() if a['source_sha256'][n]!=h}
assert set(source_changes)=={'SafeLearning/primer-linalg.html','SafeLearning/nn-in-the-loop.html'}
sys.path.insert(0,str(R/'book/coverage'));import lean_names
add('book/coverage/lean_names.py');public=[];imports={}
for n,h in a['proof_sha256'].items():
 text=path(n).read_text();masked=lean_names.without_comments(text)
 assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by|run_elab|ofReduceBool|sorryAx)\b',masked)
 public += [{'name':x['name'],'file':n} for x in lean_names.declarations(text) if x['kind'] in ['theorem','lemma']]
 imports['SafeLearning.'+Path(n).stem]=[m for line in re.findall(r'^import[^\n]*',text,re.M) for m in line.split()[1:] if m.startswith('SafeLearning.')]
assert public==a['declarations'] and len({x['name'] for x in public})==11184
assert (RT/'verification/lean/SafeLearning.lean').read_text()==''.join('import '+m+'\n' for m in sorted(imports))
assert {x['name'] for x in old['declarations']}<={x['name'] for x in public}
newnames=[x for x in public if x['file'] in newfiles];assert len(newnames)==104
assert {x['name'] for x in newnames}=={d['name'] for r in ready['sources'] for d in r['public_declarations'] if d['kind'] in ['theorem','lemma']}
def closure(module):
 seen=set()
 def visit(m):
  if m in seen:return
  assert m in imports;seen.add(m)
  for dep in imports[m]:visit(dep)
 visit(module)
 return {'verification/lean/'+m.replace('.','/')+'.lean':a['proof_sha256']['verification/lean/'+m.replace('.','/')+'.lean'] for m in sorted(seen)}
kchecks={c['module']:c for c in a['checks'] if 'module' in c};assert len(kchecks)==1248 and set(kchecks)==set(imports)
fresh={m for m,c in kchecks.items() if c['evidence_mode']=='fresh_kernel_replay'};reused={m for m,c in kchecks.items() if c.get('reused_from')}
assert len(fresh)==6 and len(reused)==1242 and fresh=={'SafeLearning.'+Path(n).stem for n in newfiles}
parentp=RT/'reports/lean-verification/reused-verification-original.json';parent=add(parentp);parenthash=sha(parentp)
assert parent==old and parenthash=='78915d21ec383430a5abea1c4b3cc9753dcfd5b2f94adb4834471459a3e2b00c'
parentchecks={c['module']:c for c in parent['checks'] if 'module' in c};kernel_details=[]
for m,c in kchecks.items():
 assert type(c['exit_code']) is int and c['exit_code']==0 and c['command']==['lake','env','leanchecker','-v',m]
 assert isinstance(c['elapsed_seconds'],(int,float)) and c['elapsed_seconds']>=0
 raw=add(RT/c['output_file'],c['log_sha256'])
 if m in reused:
  rf=c['reused_from'];assert rf['report_sha256']==parenthash and rf['prior_check_evidence_mode']==parentchecks[m]['evidence_mode']
  assert rf['verified_local_import_sha256']==closure(m)
  assert all(parent['proof_sha256'].get(n)==h for n,h in rf['verified_local_import_sha256'].items())
  actual=parentchecks[m]
  while actual.get('reused_from',{}).get('original_check'):actual=actual['reused_from']['original_check']
  assert rf['original_check']==actual
  assert c['actual_workdir']==rf['actual_workdir']==actual['actual_workdir'] and c['elapsed_seconds']==actual['elapsed_seconds'] and c['command']==actual['command'] and c['log_sha256']==actual['log_sha256']
 else:assert c['actual_workdir']==str(RT/'verification/lean')
 kernel_details.append({'module':m,'mode':c['evidence_mode'],'original_elapsed_seconds':c['elapsed_seconds'],'actual_workdir':c['actual_workdir'],'raw_log':ref(RT/c['output_file']),'current_transitive_local_import_sha256':closure(m)})
nonkernel=[]
for c in a['checks']:
 assert type(c['exit_code']) is int and c['exit_code']==0
 if 'module' in c:continue
 raw=add(RT/c['output_file']);text=raw.decode()
 nonkernel.append({'command':c['command'],'full_raw_log':ref(RT/c['output_file']),'original_elapsed_seconds':c['elapsed_seconds'],'location_first_warning_headers':len(re.findall(r'^.*:\d+:\d+: warning:',text,re.M)),'Lake_warning_first_headers':len(re.findall(r'^warning: .*:\d+:\d+:',text,re.M))})
assert len(nonkernel)==3 and [x['command'] for x in nonkernel]==[['lean','--version'],['lake','build'],['lake','env','lean',str(RT/'verification/lean/AxiomAudit.lean')]]
axiomraw=(RT/'reports/lean-verification/axioms.log').read_text();parsed={n:[x.strip() for x in ds.split(',') if x.strip()] for n,ds in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",axiomraw)}
parsed.update({n:[] for n in re.findall(r"'([^']+)' does not depend on any axioms",axiomraw)});assert parsed==a['axiom_dependencies']
manifest=json.loads((RT/'verification/lean/lake-manifest.json').read_bytes());assert [{'name':x['name'],'revision':x['rev']} for x in manifest['packages']]==a['dependency_revisions']
for p in manifest['packages']:
 checkout=R/'verification/lean'/manifest['packagesDir']/p['name']
 rev=subprocess.check_output(['git','-C',str(checkout),'rev-parse','HEAD'],text=True).strip();tree=subprocess.check_output(['git','-C',str(checkout),'rev-parse','HEAD^{tree}'],text=True).strip();dirty=subprocess.check_output(['git','-C',str(checkout),'status','--porcelain'],text=True)
 assert rev==p['rev'] and not dirty and tree==a['dependency_environment_identity'][p['name']]['git_tree']
np='reports/full-coverage/verify-runtime-checkpoint31-source81-execution-v1.json';native=add(np)
assert native['status']=='passed' and type(native['actual_exit_code']) is int and native['actual_exit_code']==0
assert native['actual_command']==['python3',str((RT/'verification/lean/verify.py').relative_to(R)),'--reuse-kernel-from',str(R/'reports/full-coverage/runtime-checkpoint-30-final-css-v1')]
assert native['actual_workdir']==str(R) and native['helper_sha256_before']==native['helper_sha256_after']
for n,h in native['helper_sha256_before'].items():add(n,h)
add(native['log'],native['log_sha256'])
prep=add('reports/full-coverage/checkpoint31-runtime-source81-preparation-v1.json','bdb0aa3c1d124ffbf434909f7b70b1c7072a413418cd3ec1b4658e0abd33490a')
assert prep['selected_source_count']==1248 and prep['site_asset_count']==31 and prep['copied_lake_build_artifact_count']==prep['copied_earlier_snapshot_tree_count']==0
assert all(sha(RT/n)==h for n,h in prep['source_hashes'].items())
find={'status':'passed_independent_actual_checkpoint31_Source81_selected1248_11184_axiom_and1251_native_identity_review','errors':[],'reviewer':'/root/foundations_recovery28','review_finished_at_utc':datetime.now(timezone.utc).isoformat(),'original_actual_report':ref(REPORT),'original_Root_actual_native':ref(np),'original_Root_elapsed_seconds':native['elapsed_seconds'],'actual_proof_selection31':ref('reports/full-coverage/checkpoint-31-selection.json'),'actual_new6_paired_readiness':ref('book/coverage/checks/future31-core/current81-canonical-pairs6-v1/actual-reviewed31-canonical-paired-readiness-v1.json'),'prior_full30_identity_peer':ref('book/coverage/checks/future30-core/actual30-first-finalCSS-audit-independent-foundations-v1/actual30-first45fresh-and-finalCSS1242reuse-source-project-dependency-native-and-owner30-identity-independent-foundations30-closed-peer-v1.json'),'all1248_current_and_runtime_proof_SHA_and31_Source81_assets_and5_project_SHA_exact':True,'all11184_actual_public_theorem_names_and_axiom_raw_lists_exact_standard_only':True,'all1251_actual_check_records_and_full_raw_logs_read':True,'six_true_fresh_kernel_replays_and1242_actual_original_kernel_chains_reused':True,'all_reused_command_cwd_elapsed_raw_SHA_original_native_and_transitive_local_imports_exact':True,'deleted_old_checkpoint_cwds_remain_historical_not_claimed_current_or_recopied':True,'all9_current_dependency_git_revisions_trees_clean_and_actual_compiled_environment_identities_match_parent30':True,'dependency_full_artifact_rehash_not_repeated_by_reviewer':'Actual verifier records its full dependency identities; reviewer reads exact identities, reused equality and current Git pins. No compiler or new full-cache artifact replay is claimed.','normal_build_and_all11184_axiom_lists_are_true_new31_commands':True,'actual_nonkernel_native_logs_and_warning_counts':nonkernel,'source80_81_asset_delta_from_original30_finalCSS':source_changes,'kernel_individual_native_and_import_chain_details':kernel_details,'source_only_preparation_no_earlier_snapshot_or_lake_tree_copy':True,'new104_public_theorem_rows':newnames,'owner31_or_future32_math_whole_scope_inferred_from_aggregate_integrity':False,'compiler_parser_producer_source_owner_canonical_publication_mutation_by_reviewer':False,'coverage_complete':False,'required_evidence_artifacts_sha256':closed}
assert not OUT.exists();OUT.write_text(json.dumps(find,indent=2)+'\n');print(json.dumps({'status':'passed','errors':[],'proofs':1248,'theorems':11184,'actual_checks':1251,'fresh':6,'reused':1242,'Root_actual_seconds':native['elapsed_seconds']}))
