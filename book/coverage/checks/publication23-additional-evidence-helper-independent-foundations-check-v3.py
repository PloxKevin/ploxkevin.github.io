from pathlib import Path
from datetime import datetime,timezone
import ast,json,hashlib,copy,difflib
ROOT=Path(__file__).resolve().parents[3]
HELPER=ROOT/'book/coverage/checks/root_stage_checkpoint23_additional_execution_evidence_v3.py'
OLD=ROOT/'book/coverage/checks/root_stage_checkpoint23_additional_execution_evidence_v2.py'
PEEROLD=ROOT/'book/coverage/checks/publication23-additional-evidence-helper-independent-foundations-review-v1.json'
OUT=ROOT/'book/coverage/checks/publication23-additional-evidence-helper-independent-foundations-review-v2.json'
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();R=lambda p:json.loads(p.read_text())
def ref(p):return {'file':p.relative_to(ROOT).as_posix(),'sha256':H(p)}
assert not OUT.exists();assert H(HELPER)=='8eb092f0d73da1b177e8ab43d329b8437db9fb47433e5a1f7f60696ef1e7d2d0'
assert H(OLD)=='9c9ddd68df0e351fcaae628f6740bf6db0eb45148372b4d9b751dc53c24f16f4'
assert H(PEEROLD)=='c2776226f844313de51069ff2dc69af87a3ff8db3ac88ec5f6b2c544f8e5621b'
oldpeer=R(PEEROLD);assert'passed'in oldpeer['status']and oldpeer['errors']==[]and oldpeer['helper_sha256']==H(OLD)
code=HELPER.read_text();oldcode=OLD.read_text();tree=ast.parse(code);oldtree=ast.parse(oldcode)
def constants(t):
 d={}
 for n in t.body:
  if isinstance(n,ast.Assign)and len(n.targets)==1 and isinstance(n.targets[0],ast.Name):
   try:d[n.targets[0].id]=ast.literal_eval(n.value)
   except(ValueError,TypeError):pass
 return d
c=constants(tree);o=constants(oldtree)
assert c['SELF_NAME']==ref(HELPER)['file']and c['PEER_NAME']==OUT.relative_to(ROOT).as_posix()
assert c['PRIMARY_HELPER']=='book/coverage/checks/root_prepare_and_stage_publication23_v4.py'
assert c['PRIMARY_HELPER_SHA']==H(ROOT/c['PRIMARY_HELPER'])=='a7c07a5560b480e183b8eefba95c087eb406d474e47f80ec007137e286bdcf87'
assert c['BASELINE_HELPER_SHA']==H(ROOT/c['BASELINE_HELPER'])=='fbde350b584b9204c0af797a95ee691c6ef51d8bec4cecf26b840d1ef089705f'
assert c['ORIGINAL_UNEXECUTED_HELPER_SHA']==H(ROOT/c['ORIGINAL_UNEXECUTED_HELPER'])=='a78c008bf23113f484cd6c121d6c5e1c6807bed5f976f431a4852890b1ea7130'
pins=copy.deepcopy(c['PINNED_CLOSED_EVIDENCE']);codes=copy.deepcopy(c['ORIGINAL_EXECUTION_CODES']);updates=[];codeupdates=[]
for n in tree.body:
 if isinstance(n,ast.Expr)and isinstance(n.value,ast.Call)and isinstance(n.value.func,ast.Attribute)and isinstance(n.value.func.value,ast.Name)and n.value.func.value.id=='PINNED_CLOSED_EVIDENCE':
  assert n.value.func.attr=='update'and len(n.value.args)==1;update=ast.literal_eval(n.value.args[0]);updates.append(update);pins.update(update)
 if isinstance(n,ast.Assign)and len(n.targets)==1 and isinstance(n.targets[0],ast.Subscript)and isinstance(n.targets[0].value,ast.Name)and n.targets[0].value.id=='ORIGINAL_EXECUTION_CODES':
  k=ast.literal_eval(n.targets[0].slice);v=ast.literal_eval(n.value);codeupdates.append((k,v));codes[k]=v
assert len(updates)==1 and len(updates[0])==10 and len(pins)==108 and c['PINNED_CLOSED_EVIDENCE']==o['PINNED_CLOSED_EVIDENCE']
assert codeupdates==[('pages23-config-execution-v2',1)]and len(codes)==33
assert c['ORIGINAL_EXECUTION_CODES']==o['ORIGINAL_EXECUTION_CODES']
assert c['SUCCESSFUL_LATER_EXECUTIONS']==tuple('pages23-config-execution-v3'if s=='pages23-config-execution-v2'else s for s in o['SUCCESSFUL_LATER_EXECUTIONS'])
# The complete operational AST must equal the previously reviewed body after
# removing only the explicitly declared version/pin/code changes.
normalized=copy.deepcopy(tree);keep=[]
for n in normalized.body:
 if isinstance(n,ast.Expr)and isinstance(n.value,ast.Constant)and isinstance(n.value.value,str):continue
 if isinstance(n,ast.Expr)and isinstance(n.value,ast.Call)and isinstance(n.value.func,ast.Attribute)and isinstance(n.value.func.value,ast.Name)and n.value.func.value.id=='PINNED_CLOSED_EVIDENCE':continue
 if isinstance(n,ast.Assign)and len(n.targets)==1 and isinstance(n.targets[0],ast.Subscript)and isinstance(n.targets[0].value,ast.Name)and n.targets[0].value.id=='ORIGINAL_EXECUTION_CODES':continue
 if isinstance(n,ast.Assign)and len(n.targets)==1 and isinstance(n.targets[0],ast.Name)and n.targets[0].id in ['SELF_NAME','PEER_NAME','PRIMARY_HELPER','PRIMARY_HELPER_SHA','SUCCESSFUL_LATER_EXECUTIONS']:
  oldnode=next(a for a in oldtree.body if isinstance(a,ast.Assign)and any(isinstance(t,ast.Name)and t.id==n.targets[0].id for t in a.targets));n.value=copy.deepcopy(oldnode.value)
 keep.append(n)
normalized.body=keep;expected=copy.deepcopy(oldtree);expected.body=[n for n in expected.body if not(isinstance(n,ast.Expr)and isinstance(n.value,ast.Constant)and isinstance(n.value.value,str))]
assert ast.dump(normalized,include_attributes=False)==ast.dump(expected,include_attributes=False)
closed=[]
for n,h in pins.items():
 assert H(ROOT/n)==h,n
 assert not Path(n).is_absolute()and'..'not in Path(n).parts and not any(k in n for k in'\x00\n\r')and not n.startswith('verification/lean/')
for stem,expectedcode in codes.items():
 p=ROOT/f'reports/full-coverage/{stem}.json';r=R(p);observed=[r[k]for k in['actual_exit_code','exit_code']if k in r]
 assert observed and all(type(v)is int and v==expectedcode for v in observed)
 assert r['actual_workdir']==str(ROOT)and H(ROOT/r['log'])==r['log_sha256']
 assert r['actual_command']and r['started_at_utc']<r['finished_at_utc']and r['elapsed_seconds']>=0
 for key in['helper_sha256_before','helper_sha256_after']:
  if key in r:
   for n,h in r[key].items():assert H(ROOT/n)==h,n
 if'helper_sha256_before'in r and'helper_sha256_after'in r:assert r['helper_sha256_before']==r['helper_sha256_after']
 closed.append({'record':ref(p),'entire_original_actual_record_and_time':r,'raw_log':ref(ROOT/r['log']),'original_actual_exit_code':expectedcode})
assert {s for s,v in codes.items()if v==1}=={'prepare-checkpoint23-selection-execution-v1','owner23-binding-preparation-execution-v1','owner23-binding-preparation-execution-v2','pages23-config-execution-v2'}
assert 'pages23-config-execution-v2'not in c['SUCCESSFUL_LATER_EXECUTIONS']and'pages23-config-execution-v3'in c['SUCCESSFUL_LATER_EXECUTIONS']
for token in["primary_native['status']=='passed_explicit_whitelist_staged'","primary_native['actual_exit_code']==0","assert peer['helper_sha256']==sha(source(SELF_NAME))","assert not out.exists() and not pathspec.exists()","assert dirty_names()<=base|names","if target.exists():assert target.is_file() and not target.is_symlink() and sha(target)==digest","assert {x.decode() for x in staged.split(b'\\0') if x}<=base|names","'--pathspec-file-nul'","'verification/lean/' not in '\\n'.join(names)"]:
 assert token in code,token
assert code.index('expected={name:sha(source(name))')<code.index('shutil.copyfile')and code.index('assert dirty_names()<=base|names')<code.index('shutil.copyfile')
assert "['python3',PRIMARY_HELPER]"in code and "==(18,1113)"in code
configfailure=R(ROOT/'reports/full-coverage/pages23-config-execution-v2.json');assert configfailure['actual_exit_code']==1
for n in ['pages23-config-preparation-v2.json','pages23-config-previous-original-v2.yml','pages23-config-previous-original-v2.json']:assert not(ROOT/'reports/full-coverage'/n).exists()
newstagepeer=ROOT/'book/coverage/checks/publication23-helper-independent-foundations-review-v3.json';newstage=R(newstagepeer)
assert newstage['helper_sha256']==c['PRIMARY_HELPER_SHA']and'passed'in newstage['status']and newstage['errors']==[]
future={f'reports/full-coverage/{s}.json':(ROOT/f'reports/full-coverage/{s}.json').exists()for s in c['SUCCESSFUL_LATER_EXECUTIONS']}
report={'status':'passed_independent_supplemental_publication23_v3_code_review_requires_actual_primary_stage_v4_and_config_v3','reviewer':'/root/config21_next','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':ref(HELPER)['file'],'helper_sha256':H(HELPER),'checker':ref(Path(__file__)),'entire_new_helper_source_read':code,'original_unexecuted_v2_helper':ref(OLD),'original_v2_independent_code_peer':ref(PEEROLD),'entire_original_v2_code_peer_body_and_time_unchanged':oldpeer,'exact_unified_delta_from_v2':''.join(difflib.unified_diff(oldcode.splitlines(keepends=True),code.splitlines(keepends=True),fromfile=ref(OLD)['file'],tofile=ref(HELPER)['file'])),'preserved_actual_first_reader_failure':{'checker':ref(ROOT/'book/coverage/checks/publication23-additional-evidence-helper-independent-foundations-check-v2.py'),'execution':ref(ROOT/'book/coverage/checks/publication23-additional-evidence-helper-independent-foundations-actual-v2.json'),'raw_log':ref(ROOT/'book/coverage/checks/publication23-additional-evidence-helper-independent-foundations-actual-v2.log'),'entire_original_actual_record_and_time':R(ROOT/'book/coverage/checks/publication23-additional-evidence-helper-independent-foundations-actual-v2.json'),'reason':'The first reader tried to hash its not-yet-created review output while comparing its declared filename. This new reader compares only that future relative path. Reviewed helper/source/evidence bytes stay exact.'},'all108_exact_closed_evidence_pins_checked':pins,'exact_ten_new_history_pins':updates[0],'all33_original_actual_execution_rows_and_times_checked':closed,'all_four_genuine_failed_executions_retained_as_exit1':sorted(s for s,v in codes.items()if v==1),'operational_body_AST_exact_after_only_declared_version_history_changes':True,'new_primary_stage_v4_code_peer':ref(newstagepeer),'actual_future_prerequisite_presence':future,'findings':['Full new source read; only required primary stage4/helper hash, self/peer version, config-success3 and exact10 closed-history pins/config2failure code differ. The entire operational AST matches the independently reviewed prior body.','The actual1131/9193 frozen audit/allfrozen bytes/heldowners/promotions/source51, real primary-stage4 zero/nativewhitelist/integrity and export18fresh/1113reused precede copies.','Original selector1/binding1/binding2/config2 failures remain actual1 with exact original bodies/times/commands/cwd/helper/rawlogs. Newconfig3 belongs only to future mandatory actualzero executions.','Every literal safe source/target and existing target equal hash is preflighted, dirty paths must fit the existing primary whitelist plus explicit supplemental names, exact copies and NUL-separated Git pathspec/staged-subset checks remain identical.','No verification sources/current owners/HTML are written. Original supplemental2+c277 entire time/body and its readers/rawactual histories are explicitly preserved.'],'errors':[],'coverage_complete':False,'scope':'Independent code-only and actual closed-evidence schema/hash review; no production helper, publication copy, Git staging, Pages build or live execution claimed. Actual primary stage4/config3/export and final supplemental execution remain Root-owned requirements.'}
with OUT.open('x')as f:f.write(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'report':ref(OUT),'helper_sha256':H(HELPER),'pins':len(pins),'original_execution_rows':len(closed)}))
