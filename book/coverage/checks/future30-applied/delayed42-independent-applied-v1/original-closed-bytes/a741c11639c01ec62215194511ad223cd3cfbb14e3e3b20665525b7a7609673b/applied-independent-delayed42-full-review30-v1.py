from pathlib import Path
from datetime import datetime, timezone
from fractions import Fraction as Q
import hashlib,json,re,time
ROOT=Path('/home/oxrexkevin/SafetyBased')
REQUEST=ROOT/'book/coverage/checks/modules-future30/delayed42-full-scope-v1/modules-delayed42-full-source-literal-independent-review-request30-v2.json'
REQUEST_SHA='6d71f540f80e3467ff3483d471c92a47faa9b98ce7e0c385f18f6d4da47c1042'
CONTEXT=Path('/tmp/root_tmp_lean_current65_owner29_context_v1.json')
CONTEXT_SHA='ed8ca5f56d1f101b1a5898e367162bda47bd6b0845312ce3ba2dda4d58938ae2'
OUT=ROOT/'book/coverage/checks/future30-applied/delayed42-independent-applied-v1'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def file(n):
 p=Path(n);return p if p.is_absolute() else ROOT/p
def ref(p):return {'file':str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
start=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
assert sha(REQUEST)==REQUEST_SHA and sha(CONTEXT)==CONTEXT_SHA and not OUT.exists()
context=json.loads(CONTEXT.read_bytes());d=json.loads(REQUEST.read_bytes())
guards={**context['pins_sha256'],**context['held_current_source_sha256'],**context['owners_sha256']}
def guard():
 assert sha(REQUEST)==REQUEST_SHA and sha(CONTEXT)==CONTEXT_SHA
 for n,h in guards.items():assert sha(ROOT/n)==h,n
before={n:sha(ROOT/n) for n in guards};guard()
refs={str(REQUEST):REQUEST_SHA,str(CONTEXT):CONTEXT_SHA}
def collect(x):
 if isinstance(x,dict):
  if isinstance(x.get('file'),str) and isinstance(x.get('sha256'),str):
   n,h=str(file(x['file'])),x['sha256'];assert n not in refs or refs[n]==h;refs[n]=h
  for y in x.values():collect(y)
 elif isinstance(x,list):
  for y in x:collect(y)
collect(d)
for n,h in d['required_evidence_artifacts_sha256'].items():
 n=str(file(n));assert n not in refs or refs[n]==h;refs[n]=h
for n,h in refs.items():assert sha(Path(n))==h,n
body=file(d['source']['file']).read_text();public=re.findall(r'^theorem\s+(\w+)',body,re.M);defs=re.findall(r'^def\s+(\w+)',body,re.M);abbrevs=re.findall(r'^abbrev\s+(\w+)',body,re.M)
ns='SafeLearning.CompleteModulesDelayedSquareWhole30.'
assert len(public)==42 and len(defs)==13 and len(abbrevs)==1
assert [ns+n for n in public]==d['public_theorem_names'] and [ns+n for n in defs]==d['public_definition_names'] and [ns+n for n in abbrevs]==d['public_abbreviation_names']
masked=re.sub(r'/\-.*?\-/|--[^\n]*','',body,flags=re.S)
assert not re.search(r'\b(?:sorry|axiom|admit|unsafe|native_decide|run_elab|implemented_by|ofReduceBool|sorryAx)\b',masked)
hist=[]
for i,x in enumerate(d['genuine_lean_native_history'],1):
 a=json.loads(file(x['actual_native']['file']).read_bytes());log=file(x['actual_raw_log']['file']).read_text()
 assert a['actual_exit_code']==x['actual_exit_code'] and a['protection_errors']==[]
 assert a['source_sha256_before']==a['source_sha256_after']==x['actual_source']['sha256']==x['actual_source_snapshot']['sha256']
 assert a['raw_log_sha256']==x['actual_raw_log']['sha256']
 count=len(re.findall(r'^.*:\d+:\d+: warning:',log,re.M));assert count==x['actual_warning_count']
 hist.append({'trial':i,'original_native':x['actual_native'],'actual_exit_code':a['actual_exit_code'],'actual_warning_header_count':count,'original_started_at_utc':a['started_at_utc'],'original_finished_at_utc':a['finished_at_utc'],'original_elapsed_seconds':a['elapsed_seconds']})
assert [x['actual_exit_code'] for x in hist]==[1,0,1,0] and [x['actual_warning_header_count'] for x in hist]==[0,1,0,0]
assert file(d['genuine_lean_native_history'][-1]['actual_raw_log']['file']).read_bytes()==b''
c=json.loads(file(d['entire_current_and_prospective_context']['file']).read_bytes())
keys=['nn-in-the-loop.html::node-'+str(i) for i in [909,916,920]]
assert [x['key'] for x in c['three_entire_current_material_inventory_rows']]==keys
for x in c['three_entire_current_material_inventory_rows']+[c['entire_current_exercise_literal'],c['entire_prospective_corrected_exercise_literal'],c['entire_prospective_corrected_node920_literal']]:
 assert hashlib.sha256(x['source_text'].encode()).hexdigest()==x['text_sha256']
assert c['entire_current_exercise_owner_row']['inventory_key']==d['exercise_key'] and len(c['entire_current_exercise_owner_row']['claims'])==7
old=r'The roots are $0.45\pm0.312250i$';new=r'The roots are $0.45\pm(\sqrt{39}/20)i\approx0.45\pm0.312250i$'
a=c['entire_current_exercise_literal']['source_text'];b=c['entire_prospective_corrected_exercise_literal']['source_text']
assert a.count(old)==1 and b==a.replace(old,new)
a=c['three_entire_current_material_inventory_rows'][-1]['source_text'];b=c['entire_prospective_corrected_node920_literal']['source_text']
assert a.count(old)==1 and b==a.replace(old,new)
assert Q(6245,20000)**2!=Q(39,400)
assert Q(624499,2000000)**2<Q(39,400)<Q(624501,2000000)**2
assert Q(1095445,2000000)**2<Q(3,10)<Q(1095447,2000000)**2<1
assert Q(9,10)*Q(1,2)-Q(3,10)*Q(-1,2)==Q(3,5) and Q(-3,2)*Q(-1,2)==Q(3,4)<Q(4,5)
assert d['source_number_reserved'] is False and d['source_applied'] is False and d['canonical_pairs_executed'] is False and d['whole_promotion_performed'] is False
OUT.mkdir(parents=True);closed=[]
for n,h in sorted(refs.items()):
 p=Path(n);dest=OUT/'original-closed-bytes'/h/p.name;dest.parent.mkdir(parents=True,exist_ok=True)
 if not dest.exists():dest.write_bytes(p.read_bytes())
 assert sha(dest)==h;closed.append({'original':ref(p),'closed_copy':ref(dest)})
guard();after={n:sha(ROOT/n) for n in guards};assert before==after
for n,h in refs.items():assert sha(Path(n))==h
parts=[
 {'scope':'current whole node909','whole_approved':True,'missing_clauses':[],'correspondence':'Actual controller -1.5 times independently initialized memory and actual normalized zero-disturbance plant compose to the displayed matrix. All initial states are freely quantified. Actual recurrence, initial coordinates, exact Euclidean energy decay, convergence for every state, fixed equilibrium and uniform epsilon/delta Lyapunov stability prove asymptotic stability. Every square initial command is feasible; next-error magnitude<=.6 has both extrema, and the corner(.5,-.5) gives the requested noninvariance with command.75<=.8. No prior admissible-history premise occurs.'},
 {'scope':'current whole node916','whole_approved':True,'missing_clauses':[],'correspondence':'Actual characteristic polynomial is X^2-.9X+.3. Complete factorization, root iff, distinct conjugate roots and actual nonzero eigenvectors derive both exact roots9/20 +/- i sqrt39/20. Both opposite-sign corners attain next errors +/-.6.'},
 {'scope':'current entire Exercise14.B2 and current whole node920','whole_approved':False,'missing_clauses':['Current answer presents .312250 as an exact imaginary part. The exact imaginary part is sqrt39/20 and differs from6245/20000.'],'correspondence':'All other full prompt/hint/answer clauses have direct support in the coherent42-body family. The false current exact decimal prevents whole-current approval.'},
 {'scope':'prospective corrected entire Exercise14.B2 and prospective corrected whole node920','whole_approved':True,'conditional_on_later_actual_source_application':True,'missing_clauses':[],'correspondence':'All five prompt requirements, the entire hint and answer read. Exact roots and strict six-decimal rounding enclosures justify the corrected formula and magnitude. Every independently initialized augmented trajectory converges and the equilibrium is stable, while an initial square state exits with hardware-feasible input. A nontrivial storage sublevel is invariant in BOTH coordinates, all its trajectories remain in the square, every command meets the actuator bound, and its physical temperature projection is contained within[35,45]. This is containment, not equality with the whole interval. Stability of the globally defined nominal recurrence after escape does not claim validity of the physical plant after leaving its stated region.'},
 {'scope':'two original partial proved-component gap associations','whole_approved':False,'component_support_approved':True,'missing_clauses':[],'correspondence':'The new exact roots and all-state convergence discharge the former missing mathematical support of proved-component-1. Exact roots, rigorous rounding and decimal nonexactness independently settle the separate root-value mathematics attached to proved-component-2; its current erroneous literal stays pending until the narrow correction is actually applied. No old statement, declaration, hypothesis, status or time is changed by this peer.'}
]
r={'status':'passed_independent_full_delayed42_semantic_review_with_current_decimal_gap_and_conditional_corrected_whole','reviewer':'/root/applied_finish30','request':ref(REQUEST),'source':d['source'],'review_helper':ref(Path(__file__)),'actual_checker_exit_code':0,'checker_started_at_utc':start,'checker_finished_at_utc':datetime.now(timezone.utc).isoformat(),'checker_elapsed_seconds':time.monotonic()-tick,'errors':[],'read_scope':'Every42 public theorem proof, all13 definitions and State abbreviation in the coherent final source. Three complete selected dependencies were read. Full used primary API proof bodies and typeclass context read for actual characteristic polynomial, matrix-vector multiplication, complex norms, real sqrt and continuity, iterates, Euclidean norms and the additive norm-convergence equivalence. Full current plant/exercise/background context, every requirement, hint and answer, all three source literals and original owner/claim rows, both proposed corrected full literals, every genuine original native/log/source/snapshot and exact warning/time history read. Narrow root substitution independently checked; no independent full29 parser run or canonical installation claimed.','public_theorem_names':d['public_theorem_names'],'public_definition_names':d['public_definition_names'],'public_abbreviation_names':d['public_abbreviation_names'],'full_scope_decisions':parts,'current_exercise_whole_approved':False,'prospective_corrected_exercise_whole_approved':True,'current_whole_material_approved':keys[:2],'current_whole_material_pending':[keys[-1]],'prospective_corrected_material_whole_approved':[keys[-1]],'current_exercise_literal':c['entire_current_exercise_literal'],'prospective_corrected_exercise_literal':c['entire_prospective_corrected_exercise_literal'],'prospective_corrected_material_literal':c['entire_prospective_corrected_node920_literal'],'native_histories_preserved':hist,'warning_count_definition':'Number of emitted source-position warning headers, matching ^.*:\\d+:\\d+: warning: under MULTILINE, excluding linter hint text.','closed_original_inputs':closed,'protected_selected29_proof_sources':1197,'unchanged_current65_book_assets':31,'unchanged_installed29_live_owners':5,'protection_errors':[],'current_source_or_owner_changes':False,'narrow_wording_applied':False,'canonical_installation_or_aggregate_audit_claimed':False,'whole_promotion_performed':False,'coverage_complete':False}
p=OUT/'modules-delayed42-full-independent-applied30-closed-peer-v1.json';p.write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({'record':str(p.relative_to(ROOT)),'sha256':sha(p),'status':r['status'],'actual_checker_exit_code':0,'checker_elapsed_seconds':r['checker_elapsed_seconds'],'errors':[],'protection_errors':[]}))
