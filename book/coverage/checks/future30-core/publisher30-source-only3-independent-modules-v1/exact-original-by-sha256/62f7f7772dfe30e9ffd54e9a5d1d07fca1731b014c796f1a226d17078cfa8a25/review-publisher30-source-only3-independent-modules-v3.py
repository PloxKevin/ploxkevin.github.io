from pathlib import Path
from datetime import datetime, timezone
import ast, hashlib, json, subprocess
R=Path('/home/oxrexkevin/SafetyBased')
O=Path('/tmp/publisher30-source-only3-independent-modules-findings-v3.json')
PINS={
 'book/coverage/prepare_publication30_source_only_v3.py':'f1b8f6ab8c8cceaa0323de4097c2292ce78b1eecfa3ce0297f5cae4f8237e3bb',
 'book/coverage/prepare_publication30_source_only_v2.py':'1bea76d58ad177966d04715bb68e0eb5f2414a124aadb581a8fd11d02a27fde2',
 'book/coverage/freeze_checkpoint30_source_only_v2.py':'b0019000f105ef923861437bbbe4ee6ae359cc42276351fdd7664d0164bed757',
 'reports/full-coverage/checkpoint-30-manifest.json':'74b7eb171018a762341ab671a21d2fd730d171eaa455fa2385b8619a6c9c999a',
 'reports/full-coverage/lean-checkpoint-30-final-css-v1/verification-original.json':'78915d21ec383430a5abea1c4b3cc9753dcfd5b2f94adb4834471459a3e2b00c',
}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(n):return {'file':n,'sha256':sha(R/n),'bytes':(R/n).stat().st_size}
assert not O.exists()
assert all(sha(R/n)==h for n,h in PINS.items())
s=(R/'book/coverage/prepare_publication30_source_only_v3.py').read_text();tree=ast.parse(s)
old=ast.parse((R/'book/coverage/prepare_publication30_source_only_v2.py').read_text())
# The exact new version adds the Git-directory exclusion and preserves HEAD/index bytes.
changed=[]
assert len(tree.body)==len(old.body)
for i,(a,b) in enumerate(zip(old.body,tree.body)):
 if ast.dump(a)!=ast.dump(b):changed.append(i)
assert len(changed)==2
assert isinstance(tree.body[changed[0]],ast.FunctionDef) and tree.body[changed[0]].name=='safe'
assert isinstance(tree.body[changed[1]],ast.FunctionDef) and tree.body[changed[1]].name=='main'
constants={n.targets[0].id:ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and isinstance(n.targets[0],ast.Name) and n.targets[0].id in {'BASELINE','RESULT'}}
assert constants['BASELINE']=='01b95073d2f78d066ef88c1aa3fd20af1d631e22'
assert "assert not any(re.fullmatch(r'checkpoint-\\d+', part) for part in Path(n).parts[:-1])" in s
m=json.loads((R/'reports/full-coverage/checkpoint-30-manifest.json').read_bytes())
a=json.loads((R/m['successful_verification']['report']).read_bytes())
assert m['status']=='formal_verification_passed_partial_coverage' and m['coverage_complete'] is False
assert m['source_only_snapshot'] is True and m['old_snapshot_or_lake_tree_copied'] is False
assert a['status']=='passed' and len(a['proof_sha256'])==len(m['proof_files'])==a['proof_file_count']==1242
assert a['proof_sha256']=={n:r['sha256'] for n,r in m['proof_files'].items()}
assert a['theorem_count']==len(a['declarations'])==len(a['axiom_dependencies'])==11080
assert len(a['checks'])==1245 and all(c['exit_code']==0 for c in a['checks'])
assert len(a['source_sha256'])==31
assert all(set(xs)<={'Classical.choice','propext','Quot.sound'} for xs in a['axiom_dependencies'].values())
frozen=m['frozen_inputs_sha256'];snapshot=R/m['snapshot']
assert len(frozen)==1298 and all(sha(snapshot/n)==h for n,h in frozen.items())
assert {n:h for n,h in frozen.items() if n.startswith('SafeLearning/')}==a['source_sha256']
pub=R/'reports/book/publication-repo'
head=subprocess.run(['git','rev-parse','HEAD'],cwd=pub,check=True,capture_output=True).stdout.decode().strip()
status=subprocess.run(['git','status','--porcelain','-z','--untracked-files=all'],cwd=pub,check=True,capture_output=True).stdout
assert head==constants['BASELINE'] and status==b''
index=(pub/subprocess.run(['git','rev-parse','--git-path','index'],cwd=pub,check=True,capture_output=True).stdout.decode().strip()).resolve()
assert index.is_relative_to(pub/'.git') and index.is_file()
actual_index_sha=sha(index)
assert "'.git' not in Path(n).parts" in s
assert 'assert sha(index_path) == original_index_sha256' in s
assert all(sha(R/n)==h for n,h in PINS.items())
f={
 'status':'passed_independent_checkpoint30_source_only_publication_preparer3_full_code_review',
 'errors':[], 'reviewer':'/root/modules_finish28','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),
 'helper':ref('book/coverage/prepare_publication30_source_only_v3.py'),
 'original_unexecuted_preparer2':ref('book/coverage/prepare_publication30_source_only_v2.py'),
 'reviewed_helpers_sha256':{n:h for n,h in PINS.items() if n.endswith('.py')},
 'full_code_read':True, 'exact_v2_to_v3_delta_read':True,
 'original_unexecuted_v2_observation':'After the genuine publisher2 read, a disjoint Applied boundary read found that supplemental .git paths were still allowed. No producer invocation occurred. NEW3 rejects every .git component and asserts unchanged clean-baseline HEAD/index bytes after copying. Exact original2/full peer/body/time are retained.',
 'previous_full_independent_peer':ref('book/coverage/checks/future30-core/publisher30-source-only2-independent-modules-v1/checkpoint30-source-only-publication-preparer2-full-code-independent-modules30-closed-peer-v1.json'),
 'Git_internal_components_rejected_for_every_ROOT_and_PUB_path':True,
 'publication_HEAD_and_original_index_sha_preserved_by_final_guards':True,
 'all_planned_copy_paths_physically_contained_and_symlink_ancestors_rejected':True,
 'all_old_and_current_snapshot_directories_lake_and_python_cache_excluded_before_any_copy':True,
 'all_explicit_source_hashes_and_individual_100MB_limit_prechecked':True,
 'unchanged_existing_historical_publication_paths_disjoint_verified_and_retained':True,
 'copies_only_changed_explicit_files_and_emits_exact_whitelist':True,
 'final_byte_checks_cover_all_sources_targets_and_existing_references':True,
 'actual_source_only_manifest':ref('reports/full-coverage/checkpoint-30-manifest.json'),
 'unchanged_exported_original_report':ref(m['successful_verification']['report']),
 'actual_frozen_hashes_checked':len(frozen), 'selected_sources':1242, 'public_theorem_and_lemma_names':11080,
 'actual_publication_baseline_head':head,'actual_publication_baseline_clean':True,
 'actual_publication_baseline_index_sha256':actual_index_sha,
 'code_review_only':True, 'producer_invoked':False,'git_stage_commit_push_invoked':False,
 'publication_preparation_staging_or_delivery_approved_as_actual_output':False,
 'old79_context_guard_invoked':False,
 'explicit_supplement_actual_output_not_yet_reviewed':True,
 'scope':'Full prepare_publication30_source_only_v3 code and exact preceding version delta, with genuine frozen source-only manifest/final-CSS audit schema and all1298 frozen byte hashes. Conditional code approval; the final explicit supplement must independently satisfy all pinned manifest/disjoint historical paths/hash/path/size prerequisites before Root invokes this producer. No stage, commit, push or delivery approval.'}
assert sha(index)==actual_index_sha
O.write_text(json.dumps(f,indent=2)+'\n')
print(json.dumps({'status':f['status'],'errors':[],'frozen_hashes_checked':1298,'baseline_clean':True,'producer_invoked':False}))
