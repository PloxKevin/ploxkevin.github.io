from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,traceback,sys
ROOT=Path('/home/oxrexkevin/SafetyBased');TMP=Path('/tmp');START=datetime.now(timezone.utc).isoformat()
REQUEST=TMP/'applied-lyapunov-scenario-continuous-risk23-independent-review-request-v1.json'
OUT=TMP/'lyapunov-scenario-continuous-risk23-independent-foundations-components-review-v2.json';FAIL=TMP/'lyapunov-scenario-continuous-risk23-independent-foundations-checker-failure-v2.json'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def path(n):return Path(n) if Path(n).is_absolute() else ROOT/n
def ref(p):return {'file':str(p),'sha256':sha(p)}
def check(r):
 p=path(r['file']);assert p.is_file() and not p.is_symlink() and sha(p)==r['sha256'];return p
def main():
 assert not OUT.exists() and not FAIL.exists() and sha(REQUEST)=='60e27ec9ce54328e9c19adf9211191246d0c987b67473451c31c52b57fac4c05'
 q=read(REQUEST);inv=read(check(q['inventory']))
 assert next(r for r in inv['exercises'] if r['key']==q['exercise_key'])==q['entire_inventory_record']
 unit=q['material_units'][0];assert next(r for r in inv['material_source_units'] if r['key']==unit['source_unit_key'])==unit['entire_inventory_record']
 assert unit['whole_unit_approved'] is False and len(unit['components'])==1
 source=check(q['proof_source']);snapshot=check(q['original_source_snapshot']);assert source.read_bytes()==snapshot.read_bytes()
 text=source.read_text();assert not re.search(r'\b(sorry|admit|axiom)\b',text)
 ns=re.search(r'^namespace ([A-Za-z0-9_.]+)$',text,re.M).group(1);names=[ns+'.'+n for n in re.findall(r'^theorem\s+(\w+)',text,re.M)]
 assert len(names)==q['public_theorem_count']==6 and names==unit['components'][0]['lean_declarations']
 actual=read(check(q['actual_standalone_record']));assert actual==q['entire_actual_record'] and actual['actual_exit_code']==0
 assert actual['actual_command']==['lake','env','lean',str(snapshot)] and actual['cwd']==str(ROOT/'verification/lean')
 assert actual['source_sha256_before']==actual['source_sha256_after']==actual['working_source_sha256_after']==sha(source)
 log=check(q['raw_log']);assert str(log)==actual['raw_log_file'] and sha(log)==actual['raw_log_sha256'] and not re.search(r'\berror(?:\(|:)',log.read_text())
 assert len(re.findall(r'^/tmp/[^\n]+:\d+:\d+: warning:',log.read_text(),re.M))==3 and 'hm' in log.read_text() and 'deprecated' in log.read_text()
 runner=check(q['runner']);assert sha(runner)==actual['runner_sha256'];runtext=runner.read_text()
 assert runtext.index('before=h(snapshot)')<runtext.index('subprocess.run')
 for row in q['preserved_prior_independent_reviews']:
  old=read(check(row['review']));assert old==row['entire_original_body'] and 'passed' in old['status']
 manifestpath=check(q['protected_selected22_sources']['manifest']);manifest=read(manifestpath);assert len(manifest['proof_files'])==1113
 for n,r in manifest['proof_files'].items():assert sha(ROOT/n)==r['sha256']
 for row in q['selected_imports']:
  p=check(row['proof_source']);n=str(p.relative_to(ROOT));assert manifest['proof_files'][n]==row['retained_selected22_row']
  for n,h in row['retained_selected22_row']['evidence_sha256'].items():assert sha(ROOT/n)==h
 extra=ROOT/'verification/lean/SafeLearning/CompleteAppliedCoverageUniformLaw.lean';assert sha(extra)==manifest['proof_files'][str(extra.relative_to(ROOT))]['sha256']
 primary=[]
 for p,scope in [(ROOT/'verification/lean/.lake/packages/mathlib/Mathlib/Probability/CDF.lean','Directly read monotone_cdf and cdf_eq_real real probability ofIic, lines62–83.'),(ROOT/'verification/lean/.lake/packages/mathlib/Mathlib/Probability/Independence/Basic.lean','Directly read true whole-family iIndepFun.meas_iInter and measurable postcomposition, lines255–280/660–679.'),(ROOT/'sources/text/cg2008.txt','Retained full primary Assumption1, strict support definition and general optimized-risk theorem/Table2.2; this review does not infer that general theorem from the scalar example.')]:primary.append({**ref(p),'direct_read_scope':scope})
 bodyreasons=['The optimizer is actually constructed as the nonempty finite sample maximum. Every sample lies below it and every feasible scalar is at least it; IsLeast uniqueness proves the optimizer is unique. No optimality conclusion appears as a premise.','Fresh violation is defined as the actual common-law upper-tail probability. The probability complement identity forIic and the actual CDF definition derive1-CDF for every realx.','Monotonicity of the actual CDF preserves every finite maximum, without requiring strict monotonicity or density.','Strict epsilon<violation at the actual optimizer is algebraically equivalent to every sample CDF coordinate being strictly below1-epsilon. This is an exact random-optimizer event equality, not a fixed supplied risk-event premise.','The selected genuine continuous-CDF probability-integral-transform theorem gives each transformed reading the true unit-uniform law, and actual measurable postcomposition preserves whole-family independence. Each strict threshold has probability1-epsilon, including endpoints0/1. Multiplication of independent finite events derives the exact actual optimized violation event probability(1-epsilon)^n.','The supplied numeric budget bound transfers the derived exact risk probability to beta; the previously selected genuine exponential inequality additionally proves the actual risk boundexp(-epsilon*n).']
 history=[ref(TMP/'review-lyapunov-scenario-continuous-risk23-independent-foundations-v1.py'),ref(TMP/'lyapunov-scenario-continuous-risk23-independent-foundations-checker-failure-v1.json'),ref(TMP/'lyapunov-scenario-continuous-risk23-independent-foundations-execution-v1.json'),ref(TMP/'lyapunov-scenario-continuous-risk23-independent-foundations-execution-v1.log')]
 result={'preserved_actual_first_checker_failure_history':history,'first_checker_failure_reason':'Naive warning: substring count included the warning hint text. New reader counts exactly three source diagnostic lines; all source/request/semantic scope bytes are unchanged.','status':'passed_independent_actual_continuous_iid_scalar_optimized_risk_six_body_component_future23','reviewed_by':'/root/config21_next','started_at_utc':START,'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'request':ref(REQUEST),'original_request_created_at_utc':q['created_at_utc'],'actual_checker':ref(Path(__file__)),'errors':[],'proof_source':q['proof_source'],'full_source_and_all_six_theorem_bodies':text,'public_theorem_names':names,'per_body_decisions':[{'name':n,'approved':True,'reason':why,'missing_clauses':[]} for n,why in zip(names,bodyreasons)],'approved_component':{'original_component_unchanged':unit['components'][0],'approved':True,'missing_clauses':[],'hypotheses_scope':'Arbitrary probability sample space and real common probability law with continuous CDF, finite positive sample count, measurable mutually independent readings with that common law;0≤epsilon≤1. Actual scalar lower-bound constraints and actual fresh common-law risk are constructed.','reason':'All six complete bodies derive the actual optimizer and random optimized-risk event and its probability, without an optimized-risk/all-miss conclusion premise. The continuous-CDF iid scope is exactly explicit; no density/strictCDF monotonicity assumption is hidden.'},'entire_original_actual_standalone_record':actual,'actual_standalone_record':q['actual_standalone_record'],'source_snapshot':q['original_source_snapshot'],'genuine_three_warning_raw_log':q['raw_log'],'actual_runner':q['runner'],'source_identity_scope':'Original runner genuinely captures the snapshot hash before the compiler subprocess and again afterward; the two serialized hashes and immutable snapshot match.','exact_archived_source49_exercise':q['entire_inventory_record'],'exact_archived_source49_material_unit':unit['entire_inventory_record'],'source49_inventory':q['inventory'],'original25_9_3_review_full_bodies_and_times':q['preserved_prior_independent_reviews'],'selected_imports_exact':q['selected_imports'],'directly_read_primary_files':primary,'all1113_selected22_source_hashes_exact':True,'whole_unit_approved':False,'whole_exercise_approved':False,'coverage_complete':False,'limits':['This closes actual random optimized violation probability in the sampled lower-bound scalar program under a continuous common CDF and iid sampling. It does not prove the distribution-free Campi–Garatti risk theorem for every arbitrary convex scenario program or discrete laws.','The archived49 literal(a) false exact finite-decimal equalities remain governed by the separate passed precision proposal; the original peer does not acquire a retrospective whole-unit decision.','No GP-law construction, repeated-until-pass guarantee or nonlinear stability result is inferred.','No fifth-source canonical/named or aggregate23/selection/mapping execution is claimed here. Only new TMP checker/review files are written and all earlier37 theorem sources/peer bodies/times remain unchanged.']}
 with OUT.open('x') as f:f.write(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
 print(json.dumps({'status':result['status'],'review':ref(OUT),'public_theorems':6,'whole_unit_approved':False}))
if __name__=='__main__':
 try:main()
 except Exception:
  msg=traceback.format_exc()
  if not FAIL.exists():
   with FAIL.open('x') as f:f.write(json.dumps({'status':'failed','started_at_utc':START,'failed_at_utc':datetime.now(timezone.utc).isoformat(),'actual_checker':ref(Path(__file__)),'failure':msg},indent=2)+'\n')
  sys.stderr.write(msg);sys.exit(1)
