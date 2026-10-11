from pathlib import Path
from datetime import datetime,timezone
import ast,copy,hashlib,json,subprocess
R=Path('/home/oxrexkevin/SafetyBased');P=R/'reports/book/publication-repo';O=Path('/tmp/pages26-config-helper-independent-modules-observation-v3.json');assert not O.exists()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(n):return {'file':n,'sha256':sha(R/n)}
def read(n):return json.loads((R/n).read_text())
HELP='book/coverage/checks/root_prepare_pages26_config_v3.py';HS='30d7f41eb587b915230eaa272efd44355b6a1965864ec71624ae295c2c03b50f';OLD='book/coverage/checks/root_prepare_pages26_config_v2.py';PEER='book/coverage/checks/pages26-config-helper-independent-modules-review-v2.json'
assert sha(R/HELP)==HS and sha(R/OLD)=='7beca7f7261101b5adb8ba9b7f0603a31d7343c94ddf2057a231a45fa53b5d73'and sha(R/PEER)=='11df6187967d961da129f74a9d2a19204d64da822b2d8e513003f27a568d55c7'
prior=read(PEER)
for n,h in prior['closed_evidence_sha256'].items():assert sha(R/n)==h
T=ast.parse((R/HELP).read_text());B=ast.parse((R/OLD).read_text());compile(T,HELP,'exec')
# These exact inserted statements are fixed by the reviewed whole-helper digest.
removed={*range(15,20),*range(28,42),*range(76,85),94,95,96};N=copy.deepcopy(T);N.body=[n for i,n in enumerate(N.body)if i not in removed];assert len(N.body)==len(B.body)
new_fields={'original_unexecuted_config2_helper','original_config2_independent_code_review','original_real_prepared_budget_observation','exact_older_screenshot_archive_observation','retired_older_screenshot_directories','retired_older_screenshot_file_count','retired_older_screenshot_archive_bytes','retired_older_screenshot_sorted_exact_path_sha256_map_fingerprint','current26_screenshot_aliases48_remain_public_exact'}
for c,b in zip(N.body,B.body):
 if ast.dump(c,include_attributes=False)==ast.dump(b,include_attributes=False):continue
 if isinstance(c,ast.Assign)and isinstance(c.targets[0],ast.Name)and c.targets[0].id=='added':
  assert isinstance(c.value,ast.BinOp)and isinstance(c.value.right,ast.Name)and c.value.right.id=='RETIRED_SCREENSHOT_DIRS';c.value=c.value.left
 elif isinstance(c,ast.Assert):
  assert ast.unparse(c.test).replace('len(added) == 15','len(added) == 9').replace('len(exclusions) == 116','len(exclusions) == 110')==ast.unparse(b.test);c.test=copy.deepcopy(b.test)
 elif isinstance(c,ast.Assign)and isinstance(c.targets[0],ast.Name)and c.targets[0].id=='report':
  cd={k.value:v for k,v in zip(c.value.keys,c.value.values)};bd={k.value:v for k,v in zip(b.value.keys,b.value.values)};assert set(cd)-set(bd)==new_fields
  assert all(ast.dump(cd[k],include_attributes=False)==ast.dump(bd[k],include_attributes=False)for k in bd if k not in ['excluded_count','scope']);assert ast.literal_eval(cd['excluded_count'])==116
  assert 'Six literal older19–24 screenshot directories (288 exact originals)'in ast.literal_eval(cd['scope']);c.value=copy.deepcopy(b.value)
 elif isinstance(c,ast.Expr):
  assert ast.unparse(c).replace("'exclusions': 116","'exclusions': 110")==ast.unparse(b);c.value=copy.deepcopy(b.value)
 else:raise AssertionError('unexpected inherited-code delta '+ast.unparse(c))
assert ast.dump(N,include_attributes=False)==ast.dump(B,include_attributes=False)
CON={}
for n in T.body:
 if isinstance(n,ast.Assign)and len(n.targets)==1 and isinstance(n.targets[0],ast.Name):
  try:CON[n.targets[0].id]=ast.literal_eval(n.value)
  except(ValueError,TypeError):pass
DIRS={'reports/full-coverage/browser-artifacts-'+str(i)for i in range(19,25)};assert CON['RETIRED_SCREENSHOT_DIRS']==DIRS
ARC=CON['SCREENSHOT_ARCHIVE_OBSERVATION'];BUD=CON['REAL_PREPARED_BUDGET_OBSERVATION'];assert sha(R/ARC)==CON['SCREENSHOT_ARCHIVE_OBSERVATION_SHA']and sha(R/BUD)==CON['REAL_PREPARED_BUDGET_OBSERVATION_SHA']
arc=read(ARC);budget=read(BUD);assert set(arc['archival_directories'])==DIRS and budget['currently_observed_prospective_website_bytes']==987112720
CFG=P/'_config.yml';BEFORE=sha(CFG);assert BEFORE==CON['BEFORE'];old=CFG.read_bytes();header='# Keep complete audit archives in Git while limiting the published website.\nexclude:\n';base={l[4:]for l in old.decode().splitlines()if l.startswith('  - ')};assert len(base)==101
added=set(CON['RETIRED_FILES'])|{CON['RETIRED_DIR']}|CON['NEW_DUPLICATE_OR_SNAPSHOT_EXCLUSIONS']|DIRS;exclusions=base|added;assert len(exclusions)==116
ns={'Path':Path,'hashlib':hashlib,'json':json,'subprocess':subprocess,'ROOT':R,'PUB':P,'exclusions':exclusions,**CON}
exec(compile(ast.Module(body=[n for n in T.body if isinstance(n,ast.FunctionDef)],type_ignores=[]),HELP,'exec'),ns)
FIX=[]
def check(label,f):f();FIX.append(label)
def reject(label,f):
 try:f()
 except(AssertionError,subprocess.CalledProcessError,FileNotFoundError):FIX.append(label);return
 raise AssertionError('accepted negative '+label)
LOOP=T.body[78];assert isinstance(LOOP,ast.For)and ast.unparse(LOOP.iter)=='sorted(RETIRED_SCREENSHOT_DIRS)'
CODE=compile(ast.Module(body=[copy.deepcopy(LOOP)],type_ignores=[]),HELP,'exec')
def validate(a,dirs=DIRS):
 x=dict(ns,archive_observation=a,RETIRED_SCREENSHOT_DIRS=dirs,retired_screenshots={},retired_screenshot_bytes=0);exec(CODE,x)
 return x
native=validate(arc);assert len(native['retired_screenshots'])==arc['total_files']==288 and native['retired_screenshot_bytes']==arc['total_bytes']==169960594
assert all(not(R/d).is_symlink()and not(P/d).is_symlink()for d in DIRS)
FIX.append('actual six full archive guards passed 288 PNG paths ROOT/PUB/tracked HEAD')
first=sorted(DIRS)[0]
for key,value in [('file_count',47),('byte_count',arc['archival_directories'][first]['byte_count']+1),('sorted_exact_path_sha256_map_fingerprint','0'*64)]:
 a=copy.deepcopy(arc);a['archival_directories'][first][key]=value;reject('exact archive rejects changed '+key,lambda a=a:validate(a))
for variant in ['wrong_sha','missing_file','unexpected_file','non_png','unsafe_path','wrong_prefix']:
 a=copy.deepcopy(arc);m=a['archival_directories'][first]['exact_files_sha256'];name=next(iter(m));h=m[name]
 if variant=='wrong_sha':m[name]='0'*64
 elif variant=='missing_file':m.pop(name)
 elif variant=='unexpected_file':m[first+'/unexpected.png']=h
 elif variant=='non_png':m[name[:-4]+'.txt']=m.pop(name)
 elif variant=='unsafe_path':m[first+'/../escape.png']=m.pop(name)
 else:m['reports/full-coverage/browser-artifacts-26/unapproved.png']=m.pop(name)
 reject('archive rejects '+variant,lambda a=a:validate(a))
# Existing tracked_exact function remains byte-exact and rejects real digest/tracked-set mismatch.
name,h=next(iter(native['retired_screenshots'].items()));reject('native Git tracked-set mismatch rejected',lambda:ns['tracked_exact'](first,{name:h}));reject('native archival byte mismatch rejected',lambda:ns['tracked_exact'](name,{name:'0'*64}))
for d in DIRS:assert not ns['kept'](d+'/any.png')and ns['kept'](d+'-sibling/any.png')
FIX.append('six literal exclusions preserve similarly prefixed sibling directories')
for d in ['reports/full-coverage/browser-artifacts-25','reports/full-coverage/browser-artifacts-26','reports/full-coverage/browser-artifacts-source53-26-v1']:assert ns['kept'](d+'/any.png')
FIX.append('current25/current26/fresh source53 screenshot roots remain included')
inputs=read('reports/full-coverage/browser-corrections-26-inputs.json');assert len(inputs['screenshot_aliases'])==48
for row in inputs['screenshot_aliases']:
 n,h=row['file'],row['sha256'];assert n.startswith('reports/full-coverage/browser-artifacts-26/')and sha(R/n)==sha(P/n)==h and ns['kept'](n)
FIX.append('all48 current26 actual screenshot aliases remain exact/public')
for n,h in inputs['source_sha256'].items():assert sha(R/n)==sha(P/n)==h and ns['kept'](n)
for n in ['reports/full-coverage/lean-checkpoint-25/verification-original.json','reports/full-coverage/lean-checkpoint-26/verification-original.json','book/coverage/inventory.json']+[f'book/coverage/{o}.json'for o in ['core','foundations','applied','modules']]:assert ns['kept'](n)
FIX.append('all31 current53 assets/current owners/current26 baseline25 audits included')
writes=[n.lineno for n in ast.walk(T)if isinstance(n,ast.Call)and isinstance(n.func,ast.Attribute)and(n.func.attr=='write_bytes'or n.func.attr=='open'and n.args and isinstance(n.args[0],ast.Constant)and n.args[0].value=='xb')]
assert writes and LOOP.end_lineno<min(writes)and T.body[84].end_lineno<min(writes)
FIX.append('complete archive/current image/budget guards precede every producer write')
after=(header+''.join('  - '+n+'\n'for n in sorted(exclusions))).encode();treebytes=sum(p.stat().st_size for p in P.rglob('*')if p.is_file()and'.git'not in p.relative_to(P).parts and ns['kept'](p.relative_to(P).as_posix()))-len(old)+len(after)
reserved_projection=budget['currently_observed_prospective_website_bytes']-native['retired_screenshot_bytes']+budget['explicit_reserve_for_future_missing_records_and_changes_bytes'];assert reserved_projection==822152126 and reserved_projection<850000000
assert sha(R/HELP)==HS and sha(CFG)==BEFORE and all(not(R/CON[k]).exists()for k in ['REPORT','BACKUP','BACKUP_RECORD'])
report={'status':'passed_independent_pages26_configuration3_code_delta_and_native_fixtures','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':ref(HELP),'helper_sha256':HS,'original_configuration2_code_peer':ref(PEER),'entire_original_config2_code_peer_body_and_time':prior,'exact_reverse_normalization_to_full_config2_AST':True,'prior_fixture_count_reused_without_new_execution':prior['fixture_count'],'new_fixture_count':len(FIX),'new_fixture_results':FIX,'retired_screenshot_count':288,'retired_screenshot_bytes':169960594,'current26_screenshot_count_exact_kept':48,'literal_excluded_count':116,'retired_screenshot_directories':sorted(DIRS),'archive_map_fingerprint':hashlib.sha256(json.dumps(native['retired_screenshots'],sort_keys=True,separators=(',',':')).encode()).hexdigest(),'readonly_current_pub_tree_with_configuration3_bytes':treebytes,'original_prepared_budget_minus_retired_bytes_plus_reserve':reserved_projection,'original_prepared_budget_observation':ref(BUD),'exact_archive_observation':ref(ARC),'website_budget_bytes':850000000,'actual_configuration_execution_claimed':False,'scope':'Full code read and narrow exact AST inverse plus real 288 ROOT/PUB/GitHEAD hashes, isolated accept/reject archive guards and actual current48 aliases. Existing31 source assets/owners/current26 and baseline25 audits stay included. Code peer is not actual producer/staging/Pages or future final budget success.'}
O.write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'report':str(O),'sha256':sha(O),'new_fixture_count':len(FIX),'current_tree_bytes':treebytes,'reserved_projection':reserved_projection}))
