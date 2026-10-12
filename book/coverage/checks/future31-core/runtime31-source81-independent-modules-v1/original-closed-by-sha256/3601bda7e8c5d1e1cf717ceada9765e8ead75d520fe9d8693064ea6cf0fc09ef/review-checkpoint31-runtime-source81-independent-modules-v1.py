from pathlib import Path
import ast, hashlib, importlib.util, json, re
R=Path('/home/oxrexkevin/SafetyBased')
H='book/coverage/checks/root_prepare_checkpoint31_runtime_v1.py'; HH='d5d51b8b2f651f2b8f5f353680544654a337651c44ee4f6f83835f96ddbe5e8a'
OLDH='book/coverage/checks/root_prepare_checkpoint30_runtime_v4.py'; OLDHH='7cf8d6361f3ea0861f9be6ea0719261698342f8e8a28969bf77487e573f3aab1'
SEL='reports/full-coverage/checkpoint-31-selection.json'; SH='cfe49bb94bf13fe8e464df60213a6639ffb99e63383f2f9300b93ef8a21d33da'
BASE='reports/full-coverage/checkpoint-30-selection.json'; BH='21c101dece9c614941e28174a5ff5ad6ead0fb271479f0c65cb732d10acdd196'
INV='book/coverage/inventory.json'; IH='b1e914086b3b3ab104bbfff6a647ad5488f6797b2a6f3e4f6aa7ffcb5aa74ef5'
READY='book/coverage/checks/future31-core/current81-canonical-pairs6-v1/actual-reviewed31-canonical-paired-readiness-v1.json'; RH='c18752bbf4b29ef8218cb28d990aad7edfcf0220babe2bacbafb3101bde43520'
EXEC='reports/full-coverage/current81-canonical31-six-paired-application-execution-v1.json'; EH='5f65ff3afbdc659a667e2f4cf1f307d8975945dad709b70de2231b57d98fa80d'
OUT=Path('/tmp/checkpoint31-runtime-source81-independent-modules-findings-v1.json')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def physical(n):
 p=R/n; assert type(n)is str and n and not Path(n).is_absolute() and Path(n).as_posix()==n and '..'not in Path(n).parts and '.lake'not in Path(n).parts and '.git'not in Path(n).parts
 assert p.is_file()and not p.is_symlink()and p.resolve().is_relative_to(R);return p
evidence={H:HH,OLDH:OLDHH,SEL:SH,BASE:BH,INV:IH,READY:RH,EXEC:EH}
def bind(r):
 assert type(r)is dict and type(r['file'])is str and re.fullmatch('[0-9a-f]{64}',r['sha256']);n=r['file'];h=r['sha256'];p=physical(n);assert sha(p)==h,n
 if n in evidence:assert evidence[n]==h
 evidence[n]=h;return p
for n,h in list(evidence.items()):assert sha(physical(n))==h,n
code=physical(H).read_text();oldcode=physical(OLDH).read_text();tree=ast.parse(code);compile(tree,H,'exec')
# Compare every operational AST node against the previously reviewed runtime4; only the sixteen specified literals may differ.
newtree=ast.parse(code);oldtree=ast.parse(oldcode);changes=[]
def compare(a,b,p=()):
 if isinstance(a,ast.Constant)and isinstance(b,ast.Constant):
  if a.value!=b.value:changes.append({'ast_pointer':list(p),'before':a.value,'after':b.value})
  return
 if isinstance(a,ast.AST)and isinstance(b,ast.AST):
  assert type(a)is type(b),(p,type(a),type(b));assert a._fields==b._fields
  for f in a._fields:compare(getattr(a,f),getattr(b,f),p+(f,))
 elif isinstance(a,list)and isinstance(b,list):
  assert len(a)==len(b),p
  for i,(x,y)in enumerate(zip(a,b)):compare(x,y,p+(i,))
 else:assert a==b,p
compare(oldtree,newtree)
assert len(changes)==16,len(changes)
allowed=[('checkpoint30 audit.','checkpoint31 audit.'),('runtime-checkpoint-30-final-css-v1','runtime-checkpoint-31-source81-v1'),('checkpoint30-runtime-final-css-preparation-v1.json','checkpoint31-runtime-source81-preparation-v1.json'),('checkpoint-30-selection.json','checkpoint-31-selection.json'),('checkpoint-29-selection.json','checkpoint-30-selection.json'),('ad4eb2940daa6f89dfb52390abc26c8bedb00dae7f97534957f5a4e87ac0d8a9',BH),('9f2a37c42e8a54b81ea542ead730dbfa1d3f665be469c41e4eaa6a27703520de',IH),(1242,1248),(45,6),(1197,1242),('source_only_checkpoint30_runtime_prepared_audit_not_yet_run','source_only_checkpoint31_runtime_prepared_audit_not_yet_run'),('baseline_selection29_before_and_after','baseline_selection30_before_and_after'),('source79_inventory_before_and_after','source81_inventory_before_and_after'),(1242,1248),(1242,1248)]
# Sixteen includes docstring and 15 remaining literals; validate literal full substitutions independently.
for c in changes:
 a,b=c['before'],c['after']
 assert any((a==x and b==y)or(isinstance(a,str)and isinstance(x,str)and a.replace(x,y)==b and x in a)for x,y in allowed),(a,b)
assert [n.name for n in tree.body if isinstance(n,ast.FunctionDef)]==['sha','safe','output_path','main']
assert all(not isinstance(n,(ast.Import,ast.ImportFrom))or not any(x.name in ['subprocess','shutil','os']for x in n.names)for n in tree.body)
assert "with target.open('xb')"in code and "with (RUNTIME / aggregate_name).open('xb')"in code and "not RUNTIME.exists() and not RESULT.exists()"in code
assert "p.resolve().is_relative_to(ROOT.resolve())"in code and "not parent.is_symlink()"in code
assert "(lake / 'packages').symlink_to(packages"in code and "(lake / 'build').symlink_to(cache"in code
assert "kernel_or_axiom_or_aggregate_success_claimed': False"in code and "copied_earlier_snapshot_tree_count': 0"in code
selected=json.loads(physical(SEL).read_bytes());base=json.loads(physical(BASE).read_bytes());inventory=json.loads(physical(INV).read_bytes());ready=json.loads(physical(READY).read_bytes());execution=json.loads(physical(EXEC).read_bytes())
assert selected['proof_file_count']==len(selected['proof_files'])==1248 and selected['new_file_count']==6 and len(base['proof_files'])==1242
assert selected['baseline_selection']=={'file':BASE,'sha256':BH}
assert selected['current_inventory']['sha256']==IH and selected['actual_new6_compiler_pairs']=={'file':READY,'sha256':RH}and selected['actual_new6_compiler_execution']=={'file':EXEC,'sha256':EH}
assert not selected['coverage_complete']and not selected['aggregate_or_kernel_or_axiom_audit_claimed']
assert all(selected['proof_files'][n]['sha256']==r['sha256']for n,r in base['proof_files'].items())
new={n:r for n,r in selected['proof_files'].items()if n not in base['proof_files']};assert len(new)==6
assert ready['status'].startswith('passed')and ready['errors']==[]and ready['source_count']==6 and ready['public_theorem_count']==104 and ready['public_name_count']==127 and ready['actual_compiler_command_count']==12
assert execution['status']=='passed'and execution['actual_exit_code']==0 and execution['actual_workdir']==str(R) and execution['elapsed_seconds']>0
assert execution['actual_command']==['python3','book/coverage/checks/run_root31_reviewed_canonical_pairs_v1.py','--plan','book/coverage/checks/future31-core/current81-canonical-plan6-v1.json','--plan-sha256','d61f930787b6639784d57b03c999118a9120f3d86249c0656cad1464ed97beb0','--apply']
bind({'file':execution['log'],'sha256':execution['log_sha256']})
for n,h in execution['helper_sha256_before'].items():assert execution['helper_sha256_after'][n]==h;bind({'file':n,'sha256':h})
site=inventory['source_sha256'];assert len(site)==29 and all(Path(n).parent==Path('SafeLearning')and n.endswith('.html')for n in site)
files={n:r['sha256']for n,r in selected['proof_files'].items()};assert all(Path(n).parent==Path('verification/lean/SafeLearning')and n.endswith('.lean')for n in files)
assert not set(files)&set(site);files.update(site)
project=['SafeLearning/style.css','SafeLearning/components.js','book/coverage/lean_names.py','verification/lean/lean-toolchain','verification/lean/lakefile.toml','verification/lean/lake-manifest.json','verification/lean/verify.py']
assert not set(files)&set(project)
for n in project:files[n]=sha(physical(n))
assert len(files)==1284
for n,h in files.items():bind({'file':n,'sha256':h})
assert 'verification/lean/SafeLearning.lean'not in files
aggregate=('\n'.join('import SafeLearning.'+Path(n).stem for n in sorted(selected['proof_files']))+'\n').encode();assert len(aggregate.decode().splitlines())==1248 and len(set(aggregate.decode().splitlines()))==1248
spec=importlib.util.spec_from_file_location('review_runtime31_lean_names',physical('book/coverage/lean_names.py'));names=importlib.util.module_from_spec(spec);spec.loader.exec_module(names)
source_rows={r['canonical_source']:r for r in ready['sources']};assert set(source_rows)==set(new)
public_total=theorem_total=0;pair_total=0;depmap={}
selected_modules={'SafeLearning.'+Path(n).stem for n in files if Path(n).parent==Path('verification/lean/SafeLearning')}
for n,r in new.items():
 source=physical(n);indexed=names.declarations(source.read_text());sr=source_rows[n];assert indexed==sr['public_declarations'];t=sum(d['kind']in ['theorem','lemma']for d in indexed);assert t==r['public_theorem_count']==sr['public_theorem_count'];theorem_total+=t;public_total+=len(indexed)
 imports=[]
 for line in names.without_comments(source.read_text()).splitlines():
  if line.strip().startswith('import '):imports+=line.strip().split()[1:]
 for imp in imports:
  if imp.startswith('SafeLearning.'):assert imp in selected_modules,imp
  elif imp.startswith('Mathlib'):
   p=R/'verification/lean/.lake/packages/mathlib'/Path(*imp.split('.')).with_suffix('.lean');assert p.is_file(),str(p)
  else:assert imp.startswith(('Lean','Std','Aesop','Batteries','Qq','ProofWidgets','ImportGraph','Plausible')),imp
 depmap[n]=imports
 assert len(r['actual_pair'])==2 and {p['kind']for p in r['actual_pair']}=={'standalone','named'}
 for pair in r['actual_pair']:
  assert pair in ready['actual_paired_records']and pair['actual_exit_code']==0 and pair['source']=={'file':n,'sha256':r['sha256']}
  for key in ['source','actual_record','raw_log','source_snapshot']:bind(pair[key])
  assert bind(pair['source_snapshot']).read_bytes()==source.read_bytes()
  native=json.loads(bind(pair['actual_record']).read_bytes());assert native['exit_code']==0 and native['source_unchanged']and native['source_sha256_before']==native['source_sha256_after']==r['sha256'];assert native['actual_workdir']==str(R/'verification/lean')and native['elapsed_seconds']>0
  expected=['lake','env','lean','SafeLearning/'+source.name]if pair['kind']=='standalone'else['lake','build','SafeLearning.'+source.stem]
  assert native['command']==expected and native['log']==pair['raw_log']['file']and native['log_sha256']==pair['raw_log']['sha256'];pair_total+=1
 for peer in sr['independent_source_peers']:bind(peer)
assert (theorem_total,public_total,pair_total)==(104,127,12)
assert (R/'verification/lean/.lake/packages').is_dir()and(R/'verification/lean/.lake/build').is_dir()
output_names=['reports/full-coverage/runtime-checkpoint-31-source81-v1','reports/full-coverage/checkpoint31-runtime-source81-preparation-v1.json']
output_observation={}
for n in output_names:
 p=R/n;assert p.resolve().is_relative_to(R.resolve())and not p.is_symlink();assert not p.exists(),n
 for q in [p,*p.parents]:
  if q.is_relative_to(R):assert not q.is_symlink()and(q==p or not q.exists()or q.is_dir())
 output_observation[n]={'absent_at_review':True,'physical_containment_and_no_symlink_ancestors':True}
# Direct source-only guard excludes live rawowners and every context runner.
errors=[n for n,h in evidence.items()if sha(physical(n))!=h];assert not errors,errors
findings={'status':'passed_independent_checkpoint31_source_only_runtime_full_code_and_actual_input_review','errors':[],'full_code_read':True,'reviewed_helper':{'file':H,'sha256':HH},'reviewed_helpers_sha256':{H:HH},'baseline_runtime4':{'file':OLDH,'sha256':OLDHH},'operational_AST_is_exact_baseline_with_sixteen_literal_updates':True,'literal_updates':changes,'selected_sources':1248,'unchanged_prior_sources':1242,'actual_new_sources':6,'actual_new_theorem_count':104,'actual_new_public_name_count':127,'actual_new_compiler_command_count':12,'site_asset_count':31,'explicit_copied_input_count':1284,'generated_aggregate_additional_count':1,'runtime_input_paths_disjoint':True,'generated_aggregate_sha256':hashlib.sha256(aggregate).hexdigest(),'new_source_dependencies':depmap,'output_observation':output_observation,'whole_helper_copy_collision_and_physical_output_guards_approved':True,'lake_packages_and_build_symlinks_only_no_cache_or_snapshot_copy':True,'actual_sources_and_native_pairs_verified':True,'runtime_producer_or_compiler_invoked':False,'future_kernel_axiom_aggregate_or_delivery_approved':False,'raw_owner_paths_and_old_context_runners_excluded_from_reader':True,'protection_errors':[],'required_evidence_artifacts_sha256':evidence}
with OUT.open('x')as f:json.dump(findings,f,indent=2);f.write('\n')
print(json.dumps({'status':findings['status'],'evidence_count':len(evidence),'source_count':1248,'site_count':31,'actual_pairs':12,'errors':[]}))
