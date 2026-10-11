from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,ast,re
ROOT=Path('/home/oxrexkevin/SafetyBased');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();R=lambda p:json.loads(Path(p).read_text())
HELPER=Path('/tmp/root_stage_checkpoint23_additional_execution_evidence_v2.py')
ORIGINAL=Path('/tmp/root_stage_checkpoint23_additional_execution_evidence_v1.py')
OUT=Path('/tmp/publication23-additional-evidence-helper-independent-foundations-review-v1.json')
assert not OUT.exists();assert H(HELPER)=='9c9ddd68df0e351fcaae628f6740bf6db0eb45148372b4d9b751dc53c24f16f4'
assert H(ORIGINAL)=='a78c008bf23113f484cd6c121d6c5e1c6807bed5f976f431a4852890b1ea7130'
code=HELPER.read_text();tree=ast.parse(code)
def constant(n):
 return next(ast.literal_eval(a.value)for a in tree.body if isinstance(a,ast.Assign)and any(isinstance(t,ast.Name)and t.id==n for t in a.targets))
pins=constant('PINNED_CLOSED_EVIDENCE');codes=constant('ORIGINAL_EXECUTION_CODES');later=constant('SUCCESSFUL_LATER_EXECUTIONS');native=constant('NATIVE_STAGE_NAMES')
assert len(pins)==98 and len(codes)==32 and len(later)==9
for n,d in pins.items():assert H(ROOT/n)==d,n
closed=[]
for stem,expected in codes.items():
 p=ROOT/f'reports/full-coverage/{stem}.json';r=R(p);observed=[r[k]for k in ['actual_exit_code','exit_code']if k in r]
 assert observed and all(type(v)is int and v==expected for v in observed),stem
 assert H(ROOT/r['log'])==r['log_sha256']and r['actual_workdir']==str(ROOT)
 assert r['actual_command']and r['started_at_utc']<r['finished_at_utc']and r['elapsed_seconds']>=0
 for k in ['helper_sha256_before','helper_sha256_after']:
  if k in r:
   for n,d in r[k].items():assert H(ROOT/n)==d,n
 if 'helper_sha256_before'in r and'helper_sha256_after'in r:assert r['helper_sha256_before']==r['helper_sha256_after']
 closed.append({'file':str(p),'sha256':H(p),'original_actual_exit_code':expected,'original_started_at_utc':r['started_at_utc'],'original_finished_at_utc':r['finished_at_utc'],'raw_log':{'file':r['log'],'sha256':r['log_sha256']}})
assert codes['prepare-checkpoint23-selection-execution-v1']==codes['owner23-binding-preparation-execution-v1']==codes['owner23-binding-preparation-execution-v2']==1
assert codes['prepare-checkpoint23-selection-execution-v2']==codes['prepare-owner23-alias-plan-execution-v3']==0
assert constant('SELF_NAME')=='book/coverage/checks/root_stage_checkpoint23_additional_execution_evidence_v2.py'
assert constant('PEER_NAME')=='book/coverage/checks/publication23-additional-evidence-helper-independent-foundations-review-v1.json'
assert H(ROOT/constant('PRIMARY_HELPER'))==constant('PRIMARY_HELPER_SHA')=='9a584d7155f6696a9fd225277005341dc8f908f4a74fdb911498eb7de0a078bb'
assert H(ROOT/constant('BASELINE_HELPER'))==constant('BASELINE_HELPER_SHA')=='fbde350b584b9204c0af797a95ee691c6ef51d8bec4cecf26b840d1ef089705f'
normalized=code.replace("SELF_NAME = 'book/coverage/checks/root_stage_checkpoint23_additional_execution_evidence_v2.py'","SELF_NAME = 'book/coverage/checks/root_stage_checkpoint23_additional_execution_evidence_v1.py'")
normalized=normalized.replace("ORIGINAL_UNEXECUTED_HELPER = 'book/coverage/checks/root_stage_checkpoint23_additional_execution_evidence_v1.py'\nORIGINAL_UNEXECUTED_HELPER_SHA = 'a78c008bf23113f484cd6c121d6c5e1c6807bed5f976f431a4852890b1ea7130'\n",'')
normalized=normalized.replace('assert sha(source(ORIGINAL_UNEXECUTED_HELPER))==ORIGINAL_UNEXECUTED_HELPER_SHA\n','').replace('{SELF_NAME,PEER_NAME,ORIGINAL_UNEXECUTED_HELPER}','{SELF_NAME,PEER_NAME}').replace('book/coverage/applied-promotions.json','book/coverage/applied-review-promotions19.json')
assert normalized==ORIGINAL.read_text()
assert "assert manifest['status']=='formal_verification_passed_partial_coverage'"in code
assert "audit['theorem_count']==9193"in code and "==1131"in code
assert 'all(row[\'exit_code\']==0 for row in audit[\'checks\'])'in code
assert 'for name,digest in manifest[\'frozen_inputs_sha256\'].items()'in code
assert "assert peer['helper_sha256']==sha(source(SELF_NAME))"in code
assert "primary_native['status']=='passed_explicit_whitelist_staged'"in code and "primary_native['actual_exit_code']==0"in code
assert "assert {x.decode() for x in staged.split(b'\\0') if x}<=base|names"in code
assert '--pathspec-file-nul'in code and 'git\',\'add\',\'-f\''in code
assert "assert not out.exists() and not pathspec.exists()"in code
assert code.index('expected={name:sha(source(name))')<code.index('shutil.copyfile')
assert code.index('assert dirty_names()<=base|names')<code.index('shutil.copyfile')
assert "if target.exists():assert target.is_file() and not target.is_symlink() and sha(target)==digest"in code
assert 'actual failed records retained as failures'in code
for n in pins:
 assert not Path(n).is_absolute()and'..'not in Path(n).parts and not any(c in n for c in '\x00\n\r')and not n.startswith('verification/lean/')
future=[f'reports/full-coverage/{s}.json'for s in later]
report={'status':'passed_independent_code_review_supplemental_publication23_helper_v2_future_actual_execution_required',
 'reviewer':'/root/config21_next','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':constant('SELF_NAME'),'helper_sha256':H(HELPER),
 'exact_TMP_helper':{'file':str(HELPER),'sha256':H(HELPER)},'entire_reviewed_helper_body':code,
 'original_unexecuted_v1':{'file':str(ORIGINAL),'sha256':H(ORIGINAL)},'entire_original_v1_helper_body':ORIGINAL.read_text(),
 'actual_checker':str(Path(__file__)),'actual_checker_sha256':H(__file__),
 'original_closed_execution_rows_checked':closed,'all98_exact_closed_evidence_pins_checked':pins,
 'observed_future_prerequisite_presence':{n:(ROOT/n).exists()for n in future},
 'code_findings':['Full source read. Only explicit closed evidence paths/native primary-stage provenance/self and author-independent peer are copied; verification sources and current mathematical owners/HTML are not edited.',
                  'Mandatory future actual1131/9193 passed frozen audit, all frozen bytes, exact current installed owners/promotions/source51, actual primary staging0 and export-integrity18fresh/1113reused precede copies.',
                  'Every original execution is checked against its exact actual success/failure code and command/cwd/log/helper hashes; genuine failed selector1 and binding1/2 remain failures.',
                  'Every source/target is preflighted before mutation; literal safe paths, existing target equality, explicit existing dirty subset and exact copies precede NUL pathspec Git staging; staged subset is checked.',
                  'V2 corrects the stale promotions filename and adds only distinct self/version plus pinned unexecuted-v1 history; full inverse delta restores exact v1 body.',
                  'Primary staging already validates frozen-versus-working Applied three metadata removals and site budget. This supplemental helper copies only closed evidence; it makes no sitebuild or push claim.'],
 'scope':'Independent code-only review and real closed-input hash/schema checks. No helper/stager/Git/PUB mutation, future passed audit, future export or actual stage execution inferred.',
 'errors':[],'coverage_complete':False}
with OUT.open('x')as f:f.write(json.dumps(report,indent=2)+'\n')
print(json.dumps({'report':str(OUT),'sha256':H(OUT),'helper_sha256':H(HELPER)}))
