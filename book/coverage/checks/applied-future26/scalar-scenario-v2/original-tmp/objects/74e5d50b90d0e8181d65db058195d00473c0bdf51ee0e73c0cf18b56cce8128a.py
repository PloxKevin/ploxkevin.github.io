from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,sys,traceback
ROOT=Path('/home/oxrexkevin/SafetyBased');REQUEST=Path('/tmp/applied-lyapunov-scenario-convex-support23-independent-review-request-v1.json')
OUT=Path('/tmp/lyapunov-scenario-convex-support23-independent-foundations-components-review-v1.json');FAIL=Path('/tmp/lyapunov-scenario-convex-support23-independent-foundations-checker-failure-v1.json');START=datetime.now(timezone.utc).isoformat()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def path(n):return Path(n) if Path(n).is_absolute() else ROOT/n
def check(r):
 p=path(r['file']);assert p.is_file() and not p.is_symlink() and sha(p)==r['sha256'];return p
def main():
 assert not OUT.exists() and not FAIL.exists() and sha(REQUEST)=='61476a46d725cca500be3f7be3a13b9ed557fbb3d8ea47f8c05a2eb66f55e07d'
 q=read(REQUEST);inv=read(check(q['inventory']))
 assert sha(ROOT/'book/coverage/inventory.json')==q['inventory']['sha256']
 assert next(r for r in inv['exercises'] if r['key']==q['exercise_key'])==q['entire_inventory_record']
 unit=q['material_units'][0]
 assert next(r for r in inv['material_source_units'] if r['key']==unit['source_unit_key'])==unit['entire_inventory_record']
 assert sha(ROOT/q['entire_inventory_record']['source'])==q['entire_inventory_record']['source_sha256']
 source=check(q['proof_source']);snapshot=check(q['source_snapshot']);assert source.read_bytes()==snapshot.read_bytes()
 text=source.read_text();assert not re.search(r'\b(sorry|admit|axiom)\b',text)
 ns=re.search(r'^namespace ([A-Za-z0-9_.]+)$',text,re.M).group(1)
 declarations=[{'name':ns+'.'+m.group(2),'kind':m.group(1)} for m in re.finditer(r'^(theorem|lemma|def) ([A-Za-z0-9_]+)',text,re.M)]
 assert declarations==q['public_declarations'];names=[r['name'] for r in declarations if r['kind']=='theorem'];assert len(names)==q['public_theorem_count']==3
 actual=read(check(q['actual_standalone_record']));assert actual==q['entire_actual_record'] and actual['actual_exit_code']==0
 assert actual['actual_command']==['lake','env','lean',str(snapshot)] and actual['cwd']==str(ROOT/'verification/lean')
 assert actual['source_sha256_before']==actual['source_sha256_after']==actual['working_source_sha256_after']==sha(source)
 log=check(q['raw_log']);assert log.stat().st_size==0 and sha(log)==actual['raw_log_sha256'] and str(log)==actual['raw_log_file']
 assert sha(check(q['runner']))==actual['runner_sha256'] and q['historical_failed_trials']==[]
 for r in q['preserved_original_numeric_and_scalar_model_peers']:
  old=read(check(r));assert old['reviewed_at_utc']==r['original_review_time'] and 'passed' in old['status']
 check(q['preserved_two_source_request'])
 selection=read(check(q['protected_selected22_sources']['selection']));assert len(selection['proof_files'])==1113
 for n,r in selection['proof_files'].items():assert sha(ROOT/n)==r['sha256']
 for r in q['primary_source_correspondence']:assert sha(ROOT/r['source_file'])==r['sha256']
 comp=unit['components'][0];assert set(comp['lean_declarations'])==set(names) and comp['missing_clauses']==[]
 result={'status':'passed_independent_general_convex_scalar_scenario_support_count_component_future23','reviewed_by':'/root/config21_next','started_at_utc':START,'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'request':{'file':str(REQUEST),'sha256':sha(REQUEST)},'original_request_created_at_utc':q['created_at_utc'],'actual_checker':str(Path(__file__)),'actual_checker_sha256':sha(Path(__file__)),'errors':[],'source':q['proof_source'],'full_source_and_all_three_proof_bodies':text,'public_theorem_names':names,'exact_whole_exercise_literal':q['entire_inventory_record'],'exact_answer_a_literal':unit['entire_inventory_record'],'approved_component':{'component_id':comp['component_id'],'approved':True,'original_component_unchanged':comp,'independent_reason':'For two supposed supporting indices, order their actual removal witnesses. The greater witness lies between the smaller and the attained optimum in the one constraint omitted by its own witness. Convexity supplies membership of that constraint; all other memberships and domain membership come from the witness. The resulting feasible point has strictly smaller objective, contradicting the genuine IsLeast optimum. This derives subsingleton support for arbitrary index types and cardinality≤1 for finite ones, with no support-count conclusion assumed.'},'entire_original_actual_standalone_record':actual,'actual_standalone_record':q['actual_standalone_record'],'source_snapshot':q['source_snapshot'],'actual_empty_raw_log':q['raw_log'],'runner':q['runner'],'original_failed_trials':[],'exact_prior25_and9_peers':q['preserved_original_numeric_and_scalar_model_peers'],'exact_prior_two_source_request':q['preserved_two_source_request'],'primary_sources':q['primary_source_correspondence'],'all1113_selected22_source_hashes_exact':True,'whole_unit_approved':False,'whole_exercise_approved':False,'coverage_complete':False,'limits':['The objective is the scalar itself (or a nonzero linear objective after orientation); original attained feasible minimum is explicitly assumed rather than constructed. Arbitrary domain need not be convex because each candidate point already belongs to the domain.','This closes only the actual convex scalar strict-improvement support-count clause. No random optimized violation probability or general Campi–Garatti distribution-free risk theorem is derived.','The false exact finite-decimal equalities in source(a) and GP-law/repeated-testing gaps remain as in the preserved original peers.','Only new TMP reader/review files are written, with no canonical/named build, mapping, aggregate23 or publication claim. Original runner before/after fields are bound as serialized, without fabricating independent pre-compilation hash capture.']}
 with OUT.open('x') as f:f.write(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
 print(json.dumps({'status':result['status'],'review':str(OUT),'review_sha256':sha(OUT),'new_theorems':3,'whole_unit_approved':False}))
if __name__=='__main__':
 try:main()
 except Exception:
  message=traceback.format_exc()
  if not FAIL.exists():
   with FAIL.open('x') as f:f.write(json.dumps({'status':'failed','started_at_utc':START,'failed_at_utc':datetime.now(timezone.utc).isoformat(),'checker':str(Path(__file__)),'checker_sha256':sha(Path(__file__)),'failure':message},indent=2)+'\n')
  sys.stderr.write(message);sys.exit(1)
