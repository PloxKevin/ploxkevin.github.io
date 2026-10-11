"""Independent read-only code and current-archive eligibility review, not Pages25 execution."""
from pathlib import Path
from datetime import datetime, timezone
import ast, hashlib, json, subprocess, copy
R=Path('/home/oxrexkevin/SafetyBased');PUB=R/'reports/book/publication-repo'
H='book/coverage/checks/root_prepare_pages25_config_v1.py';OUT=Path('/tmp/pages25-config-helper-independent-modules-review-v1.json')
EXPECTED='04207875a69824919c74a78d0fc95b415369cbceaab24989815b7b96dafaccad'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(n):return {'file':n,'sha256':digest(R/n)}
assert not OUT.exists() and digest(R/H)==EXPECTED
text=(R/H).read_text();tree=ast.parse(text)
# Import only function definitions and literal constants into an isolated namespace.
ns={'Path':Path,'datetime':datetime,'timezone':timezone,'hashlib':hashlib,'json':json,'subprocess':subprocess,'copy':copy,'ROOT':R,'PUB':PUB}
for node in tree.body:
 if isinstance(node,ast.FunctionDef):exec(compile(ast.Module(body=[node],type_ignores=[]),H,'exec'),ns)
 elif isinstance(node,ast.Assign) and isinstance(node.value,(ast.Constant,ast.Dict)):
  try:value=ast.literal_eval(node.value)
  except (ValueError,TypeError):continue
  for target in node.targets:
   if isinstance(target,ast.Name):ns[target.id]=value
fixtures=[]
def check_zero(name,d,accepted):
 try:ns['zero'](d);result=True
 except AssertionError:result=False
 assert result==accepted,(name,d);fixtures.append({'case':name,'accepted':result,'synthetic':True})
for name,d,ok in [('native_actual0',{'actual_exit_code':0},True),('native_exit0',{'exit_code':0},True),('both0',{'actual_exit_code':0,'exit_code':0},True),('actual_false',{'actual_exit_code':False},False),('exit_false',{'exit_code':False},False),('conflicting',{'actual_exit_code':0,'exit_code':1},False),('missing',{},False),('float0',{'exit_code':0.0},False),('string0',{'exit_code':'0'},False),('negative',{'exit_code':-15},False)]:check_zero(name,d,ok)
old=(PUB/'_config.yml').read_bytes();assert digest(PUB/'_config.yml')==ns['BEFORE']=='11ac06530cbae6f0c63e84afb63d2a85e60ad6c666899044a50c3b799a293965'
header='# Keep complete audit archives in Git while limiting the published website.\nexclude:\n'
ex={l[4:] for l in old.decode().splitlines() if l.startswith('  - ')}
assert len(ex)==88 and old.decode()==header+''.join('  - '+n+'\n' for n in sorted(ex))
retired=ns['RETIRED_FILES'];assert len(retired)==6
archive=ns['RETIRED_DIR'];assert archive=='reports/full-coverage/lean-checkpoint-23'
retired_map={p.relative_to(R).as_posix():digest(p) for p in (R/archive).rglob('*') if p.is_file()}
assert retired_map and archive+'/verification-original.json' in retired_map
ns['tracked_exact'](archive,retired_map)
for n,h in retired.items():ns['tracked_exact'](n,{n:h})
added=set(retired)|{archive,'reports/full-coverage/checkpoint-25','reports/full-coverage/owner24-originals-before-owner25-integration-v1'}
assert len(added)==9 and not ex&added
new=ex|added;assert len(new)==97
assert all(n and not Path(n).is_absolute() and '..' not in Path(n).parts and not any(c in n for c in '*?[{') for n in new)
ns['exclusions']=new
kept=ns['kept']
for n in ['SafeLearning/verification.html','SafeLearning/nn-in-the-loop.html','book/coverage/inventory.json','book/coverage/core.json','book/coverage/applied.json','book/coverage/foundations.json','book/coverage/modules.json','reports/full-coverage/checkpoint-24-manifest.json','reports/full-coverage/checkpoint-24-selection.json','reports/full-coverage/checkpoint-25-manifest.json','reports/full-coverage/checkpoint-25-selection.json','reports/full-coverage/lean-checkpoint-24/verification-original.json','reports/full-coverage/lean-checkpoint-25/verification-original.json']:
 assert kept(n);fixtures.append({'case':'required_included:'+n,'accepted':True,'synthetic_path_eligibility_only':True})
for n in sorted(added):assert not kept(n);assert not kept(n+'/sample.json');fixtures.append({'case':'literal_retired_subtree:'+n,'accepted':False,'synthetic_path_eligibility_only':True})
for n in ['reports/full-coverage/lean-checkpoint-230/verification-original.json','reports/full-coverage/lean-checkpoint-25/verification-original.json']:
 assert kept(n);fixtures.append({'case':'prefix_neighbour_retained:'+n,'accepted':True,'synthetic_path_eligibility_only':True})
# Future genuine gates must all precede the first write, with explicit output nonexistence guards.
firstwrite=min(n.lineno for n in ast.walk(tree) if isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute) and n.func.attr=='open' and any(isinstance(a,ast.Constant) and a.value in {'xb','wb'} for a in n.args))
assert firstwrite>next(n.lineno for n in ast.walk(tree) if isinstance(n,ast.Assert) and isinstance(n.test,ast.Compare) and ast.unparse(n.test).startswith('prospective <'))
assert "assert prospective < 850_000_000" in text and text.index('assert prospective < 850_000_000')<text.index("with (ROOT / BACKUP).open('xb')")
assert "all(type(c['exit_code']) is int and c['exit_code'] == 0" in text
assert "sum(c.get('evidence_mode') == 'fresh_kernel_replay' for c in audit['checks']) == 12" in text
assert "== 1144" in text and "audit['theorem_count'] == 9369" in text
assert "removed == baseline_removed and len(removed) == (3 if owner == 'applied' else 0)" in text
assert "normalized == json.loads((PUB / name).read_text())" in text
assert "for stem in ('verify-checkpoint25', 'export-checkpoint25', 'prepare-publication25'): actual(stem)" in text
assert "all(not (ROOT / name).exists()" in text
required_old={n:h for n,h in json.loads((R/'reports/full-coverage/checkpoint-24-manifest.json').read_text())['frozen_inputs_sha256'].items() if n.startswith('SafeLearning/')}
assert len(required_old)==31
for n,h in required_old.items():assert digest(R/n)==digest(PUB/n)==h and kept(n)
after=(header+''.join('  - '+n+'\n' for n in sorted(new))).encode()
current=sum(p.stat().st_size for p in PUB.rglob('*') if p.is_file() and '.git' not in p.relative_to(PUB).parts and kept(p.relative_to(PUB).as_posix()))-len(old)+len(after)
prior=json.loads(Path('/tmp/pages25-config-helper-independent-modules-actual-v1.json').read_text());assert prior['actual_exit_code']==1
assert 'assert firstwrite>170' in Path(prior['raw_log']).read_text()
report={'first_reader_failure':{'actual_record':'/tmp/pages25-config-helper-independent-modules-actual-v1.json','sha256':digest(Path('/tmp/pages25-config-helper-independent-modules-actual-v1.json')),'reason':'Checker1 used an arbitrary physical line threshold; Checker2 checks the actual budget assertion precedes writes.'},'status':'passed_independent_pages25_config_helper_code_and_current_archive_review','checked_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'/root/modules_resume','helper':ref(H),'helper_sha256':EXPECTED,'errors':[],'fixture_count':len(fixtures),'isolated_synthetic_fixtures':fixtures,'original_pages24_config_sha256':ns['BEFORE'],'old_literal_exclusion_count':88,'new_literal_exclusion_count':97,'exact_nine_additions':sorted(added),'six_old_manifest_selection_archives_root_pub_tracked_head_exact':retired,'older_audit_file_count':len(retired_map),'older_audit_exact_map_fingerprint':hashlib.sha256(json.dumps(retired_map,sort_keys=True,separators=(',',':')).encode()).hexdigest(),'current_publication_tree_with_prospective_exclusions_bytes':current,'current_budget_measurement_scope':'Read-only current PUB tree only. Future actual25 export/stage/native records must separately pass the helper prewrite 850MB gate; this is not an actual25 budget or production execution.','all31_current52_source_assets_exact':True,'future_actual_audit_export_publication_required':True,'frozen_vs_working_three_applied_metadata_rows_scope_preserved':True,'scope':'Full helper code read and focused isolated fixtures/read-only current archive checks. No helper execution, config mutation, future audit, publication build, or live delivery inferred.'}
OUT.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'report':str(OUT),'sha256':digest(OUT),'fixtures':len(fixtures),'current_prospective_bytes':current}))
