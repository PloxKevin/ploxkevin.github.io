from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,sys,traceback
ROOT=Path('/home/oxrexkevin/SafetyBased')
REQUEST=Path('/tmp/applied-lyapunov-scenario-support23-independent-review-request-v1.json')
OUT=Path('/tmp/lyapunov-scenario-support23-independent-foundations-components-review-v1.json')
FAIL=Path('/tmp/lyapunov-scenario-support23-independent-foundations-checker-failure-v1.json')
START=datetime.now(timezone.utc).isoformat()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def path(n):return Path(n) if Path(n).is_absolute() else ROOT/n
def check(r):
 p=path(r['file']);assert p.is_file() and not p.is_symlink() and sha(p)==r['sha256'];return p
def actual(ref,original,snapshot_ref,log_ref,exit_code):
 r=read(check(ref));assert r==original and r['actual_exit_code']==exit_code
 snapshot=check(snapshot_ref);log=check(log_ref)
 assert r['actual_command']==['lake','env','lean',str(snapshot)] and r['cwd']==str(ROOT/'verification/lean')
 assert r['source_file']==str(snapshot) and r['source_sha256_before']==r['source_sha256_after']==sha(snapshot)
 assert r['raw_log_file']==str(log) and r['raw_log_sha256']==sha(log)
 assert sha(path(r['runner_file']))==r['runner_sha256']
 assert log.stat().st_size>0
 assert bool(re.search(r'\berror(?:\(|:)',log.read_text()))==(exit_code!=0)
 return r
def main():
 assert not OUT.exists() and not FAIL.exists()
 assert sha(REQUEST)=='b04520ef934d3d4f4e74a9d9dd027c9ced3473e6d8cc52465687517b079f4023'
 q=read(REQUEST);prior=read(check(q['original_two_source_packet']))
 assert prior['created_at_utc']==q['original_two_source_packet_created_at_utc']
 peer=Path('/tmp/lyapunov-scenario-validation23-independent-foundations-components-review-v2.json')
 assert sha(peer)=='e4b152e9cdb7908ea0b46ac85e58a38d90212861152a5be1918a26c09f8d1ded'
 inv=read(check(q['inventory']));assert sha(ROOT/'book/coverage/inventory.json')==q['inventory']['sha256']
 assert next(r for r in inv['exercises'] if r['key']==q['exercise_key'])==q['entire_inventory_record']==prior['entire_inventory_record']
 units={r['key']:r for r in inv['material_source_units']}
 for row in q['material_units']:
  assert units[row['source_unit_key']]==row['entire_inventory_record']
  assert sha(ROOT/row['entire_inventory_record']['source'])==row['entire_inventory_record']['source_sha256']
 source=check(q['proof_source']);snapshot=check(q['source_snapshot']);assert source.read_bytes()==snapshot.read_bytes()
 text=source.read_text();assert not re.search(r'\b(sorry|admit|axiom)\b',text)
 ns=re.search(r'^namespace ([A-Za-z0-9_.]+)$',text,re.M).group(1)
 declarations=[{'name':ns+'.'+m.group(2),'kind':m.group(1)} for m in re.finditer(r'^(theorem|lemma|def) ([A-Za-z0-9_]+)',text,re.M)]
 assert declarations==q['public_declarations'];names={r['name'] for r in declarations if r['kind']=='theorem'}
 assert len(names)==q['public_theorem_count']==9
 passed=actual(q['actual_standalone_record'],q['entire_actual_record'],q['source_snapshot'],q['raw_log'],0)
 assert passed['working_source_sha256_after']==sha(source)
 for old in q['historical_failed_trials']:actual(old['record'],old['entire_original_record'],old['source_snapshot'],old['raw_log'],1)
 assert len(q['historical_failed_trials'])==1
 manifest=read(check(q['protected_selected_sources']['manifest']));assert len(manifest['proof_files'])==1089
 for n,r in manifest['proof_files'].items():assert sha(ROOT/n)==r['sha256']
 dep=q['selected_dependency'];assert sha(ROOT/dep['source_file'])==dep['sha256']==manifest['proof_files'][dep['source_file']]['sha256']
 assert dep['entire_selected21_row']==manifest['proof_files'][dep['source_file']]
 for n,h in dep['entire_selected21_row']['evidence_sha256'].items():assert sha(ROOT/n)==h
 for primary in q['primary_source_correspondence']:assert sha(ROOT/primary['source_file'])==primary['sha256']
 decisions=[];covered=set()
 reasons=[
  'The actual nonempty finite scalar sampled lower-bound feasible set is defined, and its attained unique least objective is derived as the sample maximum using genuine finite sup inequalities. No optimizer is assumed in the hypotheses.',
  'Removing a constraint permits a smaller objective exactly when that sample is the strict unique maximum. The proof handles the singleton remaining-empty case and tied maxima explicitly. Uniqueness derives a subsingleton supporting set and the cardinality≤1 result; this is limited to this scalar program.',
  'For a fixed threshold q, the actual sample-maximum≤q event equals missing every strict-upper-tail event. Explicit measurable mutually independent equal-probability tail events give the exact all-miss probability and exponential bound through the retained genuine dependency. This is not a random optimizer violation-probability scenario theorem.'
 ]
 assert len(q['components'])==3
 for old,reason in zip(q['components'],reasons):
  assert set(old['lean_declarations'])<=names;covered.update(old['lean_declarations'])
  decisions.append({'component_id':old['component_id'],'approved':True,'status':'approved_complete_precise_scalar_support_component','original_component_unchanged':old,'independent_reason':reason,'whole_exercise_or_material_unit_approved':False})
 assert covered==names
 result={'status':'passed_independent_actual_scalar_scenario_support_components_future23','reviewed_by':'/root/config21_next','started_at_utc':START,'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'request':{'file':str(REQUEST),'sha256':sha(REQUEST)},'original_request_created_at_utc':q['created_at_utc'],'prior25_body_peer':{'file':str(peer),'sha256':sha(peer)},'actual_checker':str(Path(__file__)),'actual_checker_sha256':sha(Path(__file__)),'errors':[],'full_source_and_all_nine_bodies':text,'source':q['proof_source'],'public_theorem_names':sorted(names),'component_decisions':decisions,'exact_entire_exercise_and_answer_a':q['entire_inventory_record'],'exact_material_rows':q['material_units'],'original_actual_standalone_record':q['actual_standalone_record'],'entire_original_actual_record':passed,'source_snapshot':q['source_snapshot'],'genuine_nonempty_warning_log':q['raw_log'],'all_original_failed_trials':q['historical_failed_trials'],'selected_dependency_exact':dep,'primary_sources':q['primary_source_correspondence'],'all1089_selected21_sources_exact':True,'whole_exercise_approved':False,'whole_unit_approved':False,'coverage_complete':False,'limits':['This is the scalar minimize-x program with sample lower bounds, not every one-variable convex scenario program.','The fixed q tail event is supplied; no quantile selection, random optimized violation event, general Campi–Garatti upper bound, GP-law construction or repeated-until-pass guarantee is inferred.','The original source(a) finite-decimal exact equalities remain false and are not whole-unit approved.','Original25-body packet/peer bytes and times remain exact. Only new TMP reader/review files are written; no canonical build, aggregate23 or mapping is claimed.','Original runner hash-before/after fields are serialized after compilation; snapshots and original fields are bound without inventing independently observed before-execution capture.']}
 with OUT.open('x') as f:f.write(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
 print(json.dumps({'status':result['status'],'review':str(OUT),'review_sha256':sha(OUT),'public_theorems':9,'precise_components':3}))
if __name__=='__main__':
 try:main()
 except Exception:
  message=traceback.format_exc()
  if not FAIL.exists():
   with FAIL.open('x') as f:f.write(json.dumps({'status':'failed','started_at_utc':START,'failed_at_utc':datetime.now(timezone.utc).isoformat(),'checker':str(Path(__file__)),'checker_sha256':sha(Path(__file__)),'failure':message},indent=2)+'\n')
  sys.stderr.write(message);sys.exit(1)
