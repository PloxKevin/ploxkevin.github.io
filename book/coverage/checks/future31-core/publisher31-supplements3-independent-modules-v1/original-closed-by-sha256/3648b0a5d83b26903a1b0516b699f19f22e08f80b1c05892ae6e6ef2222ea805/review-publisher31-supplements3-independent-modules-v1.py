from pathlib import Path
import ast,hashlib,json,re,subprocess
R=Path('/home/oxrexkevin/SafetyBased');P=R/'reports/book/publication-repo';H='book/coverage/prepare_publication31_source_only_v1.py';HH='538fd6fc838cc074ce99a939b827504127306205ed7e98575aee7f780257cbd7';S='book/coverage/checks/root_prepare_publication31_supplements_v3.py';SH='dd62ceb36207dade373b5b5007f731e34a2246d6da0cb0be53fb42a977ea98d8';M='reports/full-coverage/checkpoint-31-manifest.json';MH='f276f70a9719095fa6c1e525c705d61291a80a3aa1be270246ef62919308cce9';OLDH='book/coverage/prepare_publication30_source_only_v3.py';OLDHH='f1b8f6ab8c8cceaa0323de4097c2292ce78b1eecfa3ce0297f5cae4f8237e3bb';CTX=Path('/tmp/root_tmp_lean_current81_installed_owner31_context_v1.json');CH='0396f659bfeb3d380a53f7ca3ca3be9c77d04f56cfbee1a9be7c711ba188210c';OUT=Path('/tmp/publisher31-supplements3-independent-modules-findings-v1.json')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def git(*args):return subprocess.run(['git',*args],cwd=P,check=True,capture_output=True).stdout
def safe(n):
 assert type(n)is str and n and Path(n).as_posix()==n and not Path(n).is_absolute()and not any(c in n for c in '\0\r\n')
 assert not any(x in {'..','.git','.lake','__pycache__'}or re.fullmatch(r'checkpoint-\d+',x)for x in Path(n).parts[:-1]),n
 p=R/n;assert p.is_file()and not p.is_symlink()and p.resolve().is_relative_to(R)and all(not q.is_symlink()for q in p.parents if q.is_relative_to(R)),n;return p
ctx=json.loads(CTX.read_bytes());assert sha(CTX)==CH;guardmap={**ctx['pins_sha256'],**ctx['held_current_source_sha256'],**ctx['owners_sha256']}
def guard():
 assert sha(CTX)==CH
 for n,h in guardmap.items():assert sha(R/n)==h,n
 return []
guard();evidence={H:HH,S:SH,M:MH,OLDH:OLDHH}
for n,h in evidence.items():assert sha(safe(n))==h,n
pc=safe(H).read_text();sc=safe(S).read_text();pt=ast.parse(pc);st=ast.parse(sc);compile(pt,H,'exec');compile(st,S,'exec')
# Complete baseline publisher operational AST comparison; every changed constant is recorded and constrained, no producer call.
changes=[]
def diff(a,b,p=()):
 if isinstance(a,ast.Constant)and isinstance(b,ast.Constant):
  if a.value!=b.value:changes.append({'pointer':list(p),'before':a.value,'after':b.value})
 elif isinstance(a,ast.AST)and isinstance(b,ast.AST):
  assert type(a)is type(b)and a._fields==b._fields
  for k in a._fields:diff(getattr(a,k),getattr(b,k),p+(k,))
 elif isinstance(a,list)and isinstance(b,list):
  assert len(a)==len(b)
  for j,(x,y)in enumerate(zip(a,b)):diff(x,y,p+(j,))
 else:assert a==b,p
diff(ast.parse(safe(OLDH).read_text()),pt);assert len(changes)==10
for c in changes:
 a,b=c['before'],c['after'];assert (isinstance(a,str)and (a.replace('checkpoint30','checkpoint31').replace('source30','source31').replace('checkpoint-30','checkpoint-31')==b or(a,b)==('01b95073d2f78d066ef88c1aa3fd20af1d631e22','676db1f7d13ddbf65c2f0253d1fab79c44948a7e')))or(a,b)in[(1242,1248),(11080,11184),(1245,1251)],(a,b)
assert "'.git' not in Path(n).parts"in pc and 'original_index_sha256' in pc and "sha(index_path) == original_index_sha256"in pc
assert "re.fullmatch(r'checkpoint-\\d+', part)"in pc and "'.lake' not in Path(n).parts"in pc and "r['source'].stat().st_size < 100000000"in pc
assert "git(['rev-parse', 'HEAD'])"in pc and "git(['status', '--porcelain', '-z', '--untracked-files=all'])"in pc
assert not re.search(r"git\(\[\s*['\"](?:add|commit|push|reset|checkout)",pc)
assert "readiness['actual_paired_records']"in sc and "for key in ['actual_record','raw_log','source_snapshot']"in sc and "add(r['file'],r['sha256'])"in sc
assert "current_original_raw_applied_ledger_preserved_at_reviewed_candidate_and_not_substituted_for_pruned_publication"in sc and "n=='book/coverage/applied.json'"in sc
assert git('rev-parse','HEAD').decode().strip()=='676db1f7d13ddbf65c2f0253d1fab79c44948a7e'and git('status','--porcelain','-z','--untracked-files=all')==b''
index=(P/git('rev-parse','--git-path','index').decode().strip()).resolve();assert index.is_file()and index.is_relative_to(P/'.git');index_before=sha(index)
manifest=json.loads(safe(M).read_bytes());assert manifest['status']=='formal_verification_passed_partial_coverage'and manifest['coverage_complete']is False and manifest['source_only_snapshot']is True and manifest['old_snapshot_or_lake_tree_copied']is False
assert len(manifest['proof_files'])==1248 and len(manifest['frozen_inputs_sha256'])==1304
snapshot=R/manifest['snapshot'];assert snapshot.is_dir()and not snapshot.is_symlink()and snapshot.resolve().is_relative_to(R)
frozen=manifest['frozen_inputs_sha256'];working=manifest['working_inputs_sha256']
for n,h in frozen.items():
 p=snapshot/n;assert p.is_file()and not p.is_symlink()and sha(p)==h and p.stat().st_size<100000000,n
 # Source-only snapshot paths are read, never included in supplemental copy destinations or evidence leaves.
 if n!='book/coverage/applied.json':assert sha(R/n)==h,n
assert sha(R/'book/coverage/applied.json')==working['book/coverage/applied.json']and frozen['book/coverage/applied.json']!=working['book/coverage/applied.json']
ref=manifest['successful_verification'];assert sha(safe(ref['report']))==ref['report_sha256'];evidence[ref['report']]=ref['report_sha256'];audit=json.loads(safe(ref['report']).read_bytes());assert audit['status']=='passed'and audit['proof_file_count']==1248 and audit['theorem_count']==11184 and len(audit['checks'])==1251 and all(c['exit_code']==0 for c in audit['checks'])
assert audit['proof_sha256']=={n:r['sha256']for n,r in manifest['proof_files'].items()}and len(audit['source_sha256'])==31 and all(set(a)<= {'Classical.choice','Quot.sound','propext'}for a in audit['axiom_dependencies'].values())
closure={};raw_applied={};directories=[];peers=[]
def add(n,h=None):
 p=safe(n);actual=sha(p);assert h is None or actual==h,n
 if n in frozen:
  if actual!=frozen[n]:assert n=='book/coverage/applied.json'and actual==working[n];raw_applied[n]=actual
  return
 assert n not in closure or closure[n]==actual;closure[n]=actual

def tree(n):
 p=R/n;assert p.is_dir()and not p.is_symlink()and p.resolve().is_relative_to(R),n
 for f in sorted(p.rglob('*')):
  if f.is_file():add(f.relative_to(R).as_posix())
 directories.append(n)
def peer(n):
 d=json.loads(safe(n).read_bytes());assert d['status'].startswith('passed')and d.get('errors',[])==[],n;tree(Path(n).parent.as_posix())
 for name,h in d.get('required_evidence_artifacts_sha256',{}).items():add(name,h)
 peers.append({'file':n,'sha256':sha(safe(n))})
bindname='book/coverage/checks/future31-core/owner31-exact-reviewed-bindings-v1.json';binding=json.loads(safe(bindname).read_bytes());add(bindname)
for r in binding['replacements']:add(r['candidate']['file'],r['candidate']['sha256']);peer(r['independent_mapping_peer']['file'])
planname='book/coverage/checks/future31-core/current81-canonical-plan6-v1.json';plan=json.loads(safe(planname).read_bytes());add(planname)
for s in plan['sources']:
 for r in s['independent_source_peers']:peer(r['file'])
application=json.loads(safe('reports/full-coverage/source80-81-corrections-application-v3.json').read_bytes())
for r in application['applications']:peer(r['independent_semantic_review']['file'])
# Extract the producer's literal input lists as data, without importing/executing its code.
for node in st.body:
 if isinstance(node,ast.For)and isinstance(node.iter,ast.List):
  values=ast.literal_eval(node.iter)
  if isinstance(node.target,ast.Name)and node.target.id=='directory':
   for n in values:tree(n)
  elif isinstance(node.target,ast.Name)and node.target.id=='n':
   for n in values:add(n)
stems=ast.literal_eval(next(n.value for n in st.body if isinstance(n,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='stems'for t in n.targets)))
for stem in stems:
 for suffix in ['.json','.log']:add('reports/full-coverage/'+stem+suffix)
readyname='book/coverage/checks/future31-core/current81-canonical-pairs6-v1/actual-reviewed31-canonical-paired-readiness-v1.json';add(readyname,'c18752bbf4b29ef8218cb28d990aad7edfcf0220babe2bacbafb3101bde43520');ready=json.loads(safe(readyname).read_bytes());assert ready['status'].startswith('passed')and ready['errors']==[]and ready['source_count']==6 and len(ready['actual_paired_records'])==12
for pair in ready['actual_paired_records']:
 assert pair['actual_exit_code']==0
 for key in ['actual_record','raw_log','source_snapshot']:add(pair[key]['file'],pair[key]['sha256'])
extra='book/coverage/checks/future31-core/aggregate31-identity-independent-foundations-v1/actual31-selected1248-six-fresh1242-reused-all11184-axioms1251-checks-full-identity-independent-foundations31-closed-peer-v1.json';assert sha(safe(extra))=='b97e76df4bcf0ffb1fb66577bdf6e0aabf1dc6fac3424930498a952729f80efd';peer(extra)
# Configuration before-bytes are archived in the review folder; no historical old-SHA reference to mutable Root/PUB config enters the evidence map.
config=P/'_config.yml';cfg=config.read_bytes();assert cfg==(R/'_config.yml').read_bytes();archive=R/'reports/full-coverage/source-history/pages31-original-configuration-v1.yml';assert not archive.exists()
ex={line[4:]for line in cfg.decode().splitlines()if line.startswith('  - ')}|{'reports/full-coverage/lean-checkpoint-30','reports/full-coverage/lean-checkpoint-30-final-css-v1','reports/full-coverage/owner30-originals-before-owner31-integration-v4','reports/full-coverage/source-history','reports/full-coverage/source80-81-actual-application-parsers-v1','reports/full-coverage/publication31-extra-inputs-v1.json','reports/full-coverage/publication31-prepared-exact-files-v1.json','reports/full-coverage/checkpoint-30-manifest.json','reports/full-coverage/checkpoint-30-selection.json'}
for n in closure:
 if n.startswith('book/coverage/inventory-')and n.endswith('.json'):ex.add(n)
prospective=('# Preserve original audit evidence in Git; publish current readable site and audit.\nexclude:\n'+''.join('  - '+n+'\n'for n in sorted(ex))).encode()
D=R/'book/coverage/checks/future31-core/publisher31-supplements3-independent-modules-v1';D.mkdir(parents=True,exist_ok=False);cp=D/'actual-before-config-original-by-sha256'/hashlib.sha256(cfg).hexdigest()/'config-before31-original.yml';cp.parent.mkdir(parents=True,exist_ok=True)
with cp.open('xb')as f:f.write(cfg)
assert cp.read_bytes()==cfg;evidence[cp.relative_to(R).as_posix()]=sha(cp)
for n,h in closure.items():evidence[n]=h
for p in ['reports/full-coverage/publication31-extra-inputs-v1.json','reports/full-coverage/publication31-prepared-exact-files-v1.json']:assert not (R/p).exists()and not(P/p).exists()
assert sha(index)==index_before and git('rev-parse','HEAD').decode().strip()=='676db1f7d13ddbf65c2f0253d1fab79c44948a7e'and git('status','--porcelain','-z','--untracked-files=all')==b''and config.read_bytes()==cfg and (R/'_config.yml').read_bytes()==cfg
guard()
findings={'status':'passed_independent_publication31_publisher1_supplements3_full_code_actual_input_review','errors':[],'full_code_read':True,'reviewed_helpers_sha256':{H:HH,S:SH},'publisher_complete_operational_AST_equals_reviewed30v3_with_ten_literal_updates':True,'publisher_literal_updates':changes,'actual_manifest':{'file':M,'sha256':MH},'actual_sourceonly_frozen_file_count':1304,'actual1248_11184_1251_passed_audit_verified':True,'all_explicit_supplement_sources_peer_leaf_maps_and_twelve_paired_native_refs_physically_verified':True,'actual_original_raw_Applied_preservation':raw_applied,'preexecution_supplement_closure_paths_sha256':closure,'preexecution_closure_count':len(closure),'explicit_directories':sorted(set(directories)),'exact_peer_inputs':peers,'Foundation_actual_aggregate31_additional_peer':{'file':extra,'sha256':sha(safe(extra))},'this_peer_is_a_separate_required_additional_input_after_closure':True,'this_peer_own_future_alias_files_not_counted_in_preexecution_closure':True,'actual_before_config_stable_byte_alias':{'file':cp.relative_to(R).as_posix(),'sha256':sha(cp)},'proposed_config_sha256':hashlib.sha256(prospective).hexdigest(),'old_config_exclusions_preserved':True,'proposed_exclusion_count':len(ex),'no_old_snapshot_directory_lake_git_or_unplanned_source_copy_approved':True,'publication_baseline_head':'676db1f7d13ddbf65c2f0253d1fab79c44948a7e','actual_publication_index_sha256_before_and_after':index_before,'publication_clean_before_and_after':True,'working_Root_config_mutation_only_by_future_Root_supplement_producer':True,'actual_context_original':{'file':str(CTX),'sha256':CH},'protection_errors':[],'producer_or_Git_index_or_PUB_mutation_invoked':False,'actual_supplement_map_and_copy_preparation_still_future':True,'future_delivery_or_website_budget_success_approved':False,'coverage_complete':False,'required_evidence_artifacts_sha256':evidence}
with OUT.open('x')as f:json.dump(findings,f,indent=2);f.write('\n')
print(json.dumps({'status':findings['status'],'closure':len(closure),'evidence_count':len(evidence),'proposed_exclusions':len(ex),'proposed_config_sha256':findings['proposed_config_sha256'],'errors':[]}))
