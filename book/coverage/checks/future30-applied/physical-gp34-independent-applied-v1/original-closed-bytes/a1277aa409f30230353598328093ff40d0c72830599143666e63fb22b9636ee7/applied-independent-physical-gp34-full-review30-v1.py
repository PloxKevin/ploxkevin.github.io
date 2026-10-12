from pathlib import Path
from datetime import datetime, timezone
from fractions import Fraction as Q
import hashlib,json,re,time
ROOT=Path('/home/oxrexkevin/SafetyBased')
REQUEST=ROOT/'book/coverage/checks/modules-future30/physical-gp34-full-scope-v1/modules-physical-gp34-full-source-literal-independent-review-request30-v2.json'
REQUEST_SHA='d4eb2193fbc1bff33048b8f8ca0bad5c37b91b719fec6e742929710b7a6d40d3'
CONTEXT=Path('/tmp/root_tmp_lean_current65_owner29_context_v1.json')
CONTEXT_SHA='ed8ca5f56d1f101b1a5898e367162bda47bd6b0845312ce3ba2dda4d58938ae2'
OUT=ROOT/'book/coverage/checks/future30-applied/physical-gp34-independent-applied-v1'
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
body=file(d['source']['file']).read_text();public=re.findall(r'^theorem\s+(\w+)',body,re.M);defs=re.findall(r'^def\s+(\w+)',body,re.M)
ns='SafeLearning.CompleteModulesPhysicalGPWhole30.'
assert len(public)==34 and len(defs)==21 and [ns+n for n in public]==d['public_theorem_names'] and [ns+n for n in defs]==d['public_definition_names']
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
assert [x['actual_exit_code'] for x in hist]==[1,1,1,0] and [x['actual_warning_header_count'] for x in hist]==[7,1,0,0]
assert file(d['genuine_lean_native_history'][-1]['actual_raw_log']['file']).read_bytes()==b''
c=json.loads(file(d['entire_current_and_prospective_context']['file']).read_bytes());keys=['toolkit-gp.html::node-'+str(i) for i in [940,944,948,955,959]]
assert [x['key'] for x in c['five_entire_current_material_inventory_rows']]==keys
for x in c['five_entire_current_material_inventory_rows']+c['two_entire_current_exercise_inventory_rows']+[c['entire_prospective_corrected_B2_literal'],c['entire_prospective_corrected_node959_literal']]:
 assert hashlib.sha256(x['source_text'].encode()).hexdigest()==x['text_sha256']
assert [x['inventory_key'] for x in c['two_entire_current_partial_exercise_owner_rows']]==d['exercise_keys']
assert [len(x['claims']) for x in c['two_entire_current_partial_exercise_owner_rows']]==[4,5]
a=c['two_entire_current_exercise_inventory_rows'][1]['source_text'];b=c['entire_prospective_corrected_B2_literal']['source_text']
old=r'The physical residual upper bound is $3.247600+0.4=3.647600$ degrees. The old proposal gives $60.147600$ and fails. Its largest permitted nominal prediction is $60-3.647600\approx56.352400$ degrees.'
new=r'The physical residual upper bound is $6/7+2\sqrt{10/7}+0.4\approx3.647600$ degrees. The old proposal gives $56.5+6/7+2\sqrt{10/7}+0.4\approx60.147600$ and fails. Its largest permitted nominal prediction is $60-(6/7+2\sqrt{10/7}+0.4)\approx56.352400$ degrees.'
assert a.count(old)==1 and b==a.replace(old,new)
a=c['five_entire_current_material_inventory_rows'][-1]['source_text'];b=c['entire_prospective_corrected_node959_literal']['source_text'];assert a.count(old)==1 and b==a.replace(old,new)
# Separate exact rational reviewer checks of the unsafe rounded bound and displays.
sigma_sq=Q(10,7);round_mid=Q(3247600,1000000)
assert ((round_mid-Q(6,7))/2)**2<sigma_sq
for lo,hi,shift,sign in [(Q(36475995,10000000),Q(36476005,10000000),Q(6,7)+Q(2,5),1),(Q(601475995,10000000),Q(601476005,10000000),Q(113,2)+Q(6,7)+Q(2,5),1)]:
 assert ((lo-shift)/2)**2<sigma_sq<((hi-shift)/2)**2
lo,hi=Q(563523995,10000000),Q(563524005,10000000);base=60-Q(6,7)-Q(2,5)
assert ((base-hi)/2)**2<sigma_sq<((base-lo)/2)**2
rlo,rhi=Q(29555535,10000000),Q(29555545,10000000);assert ((rlo-Q(24,13))/2)**2<Q(4,13)<((rhi-Q(24,13))/2)**2 and 57+rhi<60
assert d['source_number_reserved'] is False and d['source_applied'] is False and d['canonical_pairs_executed'] is False and d['whole_promotion_performed'] is False
OUT.mkdir(parents=True);closed=[]
for n,h in sorted(refs.items()):
 p=Path(n);dest=OUT/'original-closed-bytes'/h/p.name;dest.parent.mkdir(parents=True,exist_ok=True)
 if not dest.exists():dest.write_bytes(p.read_bytes())
 assert sha(dest)==h;closed.append({'original':ref(p),'closed_copy':ref(dest)})
guard();after={n:sha(ROOT/n) for n in guards};assert before==after
for n,h in refs.items():assert sha(Path(n))==h
parts=[
 {'scope':'current entire Exercise3.B1 and current whole nodes940/944','whole_approved':True,'missing_clauses':[],'correspondence':'Actual all-4 arbitrary-n Gram matrix plus unit regularizer has explicitly derived inverse and inverse action. Actual selected posterior definitions yield mean8n/(1+4n), latent variance4/(1+4n), including n=0, and uniqueness of the all-ones solution is derived. Actual variance strictly decreases, standard deviation and variance tend to0, mean tends to2 and is positive for n>0. For n=3 exact mean24/13 and variance4/13, rigorous six-decimal rounding enclosures and exact conditional temperature<60 justify the displayed acceptance. Repeated and midpoint actual Gram/labels differ; no pooled posterior is inferred. The supplied error-envelope event remains a hypothesis.'},
 {'scope':'current whole nodes948/955','whole_approved':True,'missing_clauses':[],'correspondence':'Actual midpoint inverse and selected posterior give6/7 and10/7. The exact physical upper residual is a greatest admissible value, genuinely attained by modeled residual at its envelope upper endpoint and discrepancy+.4. Exact all-admissible safety iff nominal<=60 minus that maximum derives the largest replacement and rejects56.5 via an admissible witness. Separate absolute bounds permit a systematic positive discrepancy; zero mean and independence are not hypotheses.'},
 {'scope':'current entire Exercise3.B2 and current whole node959','whole_approved':False,'missing_clauses':['Rounded3.247600 is strictly below the exact modeled upper bound6/7+2sqrt(10/7); current exact physical upper3.647600 and exact complement60-3.647600 are too small/large for the asserted robust bound/maximal nominal.'],'correspondence':'All other complete prompt/hint/answer mathematics is supported, but the current exact rounded upper-bound literal prevents whole approval.'},
 {'scope':'prospective corrected entire Exercise3.B2 and corrected whole node959','whole_approved':True,'conditional_on_later_actual_source_application':True,'missing_clauses':[],'correspondence':'All four prompt requirements and the full hint/answer have direct support. Actual midpoint posterior, exact attained physical upper6/7+2sqrt(10/7)+.4, the universal safety equivalence, attained safe maximal nominal and admissible rejection of56.5 are proved. Strict half-unit six-decimal enclosures justify all corrected displays. A separate fixed two-location countermodel has modeled function2 and deterministic discrepancy0 at the observed location and+.4 at the target. It produces identical repeated observations2 and satisfies the assumed modeled envelope at both locations for EVERY n while actual posterior variance tends to0 and target physical residual remains2.4. This counterexample illustrates persistence and does not pool the midpoint dataset or prove a probabilistic confidence event. No all-time plant, zero-mean discrepancy or independence theorem is inferred.'},
 {'scope':'old partial component gap associations','whole_approved':False,'B1_matrix_gap_mathematical_support_approved':True,'B2_original_probability_scope_note_remains_true':True,'missing_clauses':[],'correspondence':'The four named actual inverse/action/posterior/unique-system bodies discharge the prior B1 matrix-to-scalar gap. The B2 probability note is an inherited explicit source hypothesis; no confidence probability is proved and this note stays true. No original statement, declaration, hypothesis, correspondence, status or time is changed.'}
]
r={'status':'passed_independent_full_physical_GP34_semantic_review_with_current_rounded_bound_gap_and_conditional_corrected_whole','reviewer':'/root/applied_finish30','request':ref(REQUEST),'source':d['source'],'review_helper':ref(Path(__file__)),'actual_checker_exit_code':0,'checker_started_at_utc':start,'checker_finished_at_utc':datetime.now(timezone.utc).isoformat(),'checker_elapsed_seconds':time.monotonic()-tick,'errors':[],'read_scope':'All34 complete public theorem proofs and21 definitions, both complete selected MatrixGP and ModulesBook dependency sources read. Full used primary API bodies and typeclass context for actual matrix inverse/right-inverse uniqueness, matrix products/mulVec/dotProduct, nat ratio limits, real sqrt positivity/squares/continuity read. Full physical GP context, both complete current exercises, all five current literals, every affected original owner/claim row and both full proposed corrected literals, original native/source/snapshot/log/time histories read. Narrow exact-radical substitution and rounding comparisons checked separately with exact rational arithmetic. No independent full29 parser execution or source installation claimed.','public_theorem_names':d['public_theorem_names'],'public_definition_names':d['public_definition_names'],'full_scope_decisions':parts,'current_exercise_whole_approved':[d['exercise_keys'][0]],'current_exercise_whole_pending':[d['exercise_keys'][1]],'prospective_corrected_exercise_whole_approved':[d['exercise_keys'][1]],'current_whole_material_approved':keys[:4],'current_whole_material_pending':keys[-1:],'prospective_corrected_material_whole_approved':keys[-1:],'current_exercise_literals':c['two_entire_current_exercise_inventory_rows'],'prospective_corrected_exercise_literal':c['entire_prospective_corrected_B2_literal'],'prospective_corrected_material_literal':c['entire_prospective_corrected_node959_literal'],'native_histories_preserved':hist,'warning_count_definition':'Actual emitted source-position warning headers under ^.*:\\d+:\\d+: warning: MULTILINE; hint text excluded.','closed_original_inputs':closed,'protected_selected29_proof_sources':1197,'unchanged_current65_book_assets':31,'unchanged_installed29_live_owners':5,'protection_errors':[],'current_source_or_owner_changes':False,'narrow_wording_applied':False,'canonical_installation_or_aggregate_audit_claimed':False,'whole_promotion_performed':False,'coverage_complete':False}
p=OUT/'modules-physical-gp34-full-independent-applied30-closed-peer-v1.json';p.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'record':str(p.relative_to(ROOT)),'sha256':sha(p),'status':r['status'],'actual_checker_exit_code':0,'checker_elapsed_seconds':r['checker_elapsed_seconds'],'errors':[],'protection_errors':[]}))
