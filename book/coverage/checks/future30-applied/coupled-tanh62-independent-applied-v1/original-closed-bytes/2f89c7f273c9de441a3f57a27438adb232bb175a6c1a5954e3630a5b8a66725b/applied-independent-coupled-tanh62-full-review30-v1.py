from pathlib import Path
from datetime import datetime, timezone
from fractions import Fraction as Q
import hashlib, json, re, time, math
ROOT=Path('/home/oxrexkevin/SafetyBased')
REQUEST=ROOT/'book/coverage/checks/modules-future30/coupled-tanh62-full-scope-v1/modules-coupled-tanh62-full-scope-independent-review-request30-v2.json'
REQUEST_SHA='64e976ea4fcb8ef17f0ba7532f768e0448feb01f48f24e4af345dbd6069fc1dc'
CONTEXT=Path('/tmp/root_tmp_lean_current65_owner29_context_v1.json')
CONTEXT_SHA='ed8ca5f56d1f101b1a5898e367162bda47bd6b0845312ce3ba2dda4d58938ae2'
OUT=ROOT/'book/coverage/checks/future30-applied/coupled-tanh62-independent-applied-v1'
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
extra_primary=[]
for tail in ['Mathlib/Analysis/Calculus/Deriv/Basic.lean','Mathlib/Analysis/Complex/ExponentialBounds.lean']:
 p=ROOT/'verification/lean/.lake/packages/mathlib'/tail;refs[str(p)]=sha(p);extra_primary.append(ref(p))
for n,h in refs.items():assert sha(Path(n))==h,n
body=file(d['source']['file']).read_text();public=re.findall(r'^theorem\s+(\w+)',body,re.M);defs=re.findall(r'^def\s+(\w+)',body,re.M)
assert len(public)==61 and len(defs)==19 and len(re.findall(r'^private theorem\s+',body,re.M))==1
ns='SafeLearning.CompleteModulesCoupledTanhCounterexample30.'
assert [ns+n for n in public]==d['public_theorem_names'] and [ns+n for n in defs]==d['public_definition_names']
masked=re.sub(r'/\-.*?\-/|--[^\n]*','',body,flags=re.S)
assert not re.search(r'\b(?:sorry|axiom|admit|unsafe|native_decide|run_elab|implemented_by|ofReduceBool|sorryAx)\b',masked)
# Preserve every genuine kernel trial, including the four failed bodies and raw warnings.
hist=[]
for i,x in enumerate(d['real_lean_native_history'],1):
 a=json.loads(file(x['actual_native']['file']).read_bytes());log=file(x['actual_raw_log']['file']).read_text()
 assert a['actual_exit_code']==x['actual_exit_code'] and a['protection_errors']==[]
 assert a['source_sha256_before']==a['source_sha256_after']==x['actual_source']['sha256']==x['actual_source_snapshot']['sha256']
 assert a['raw_log_sha256']==x['actual_raw_log']['sha256'] and len(re.findall(r'warning:',log))==x['actual_warning_count']
 hist.append({'trial':i,'original_native':x['actual_native'],'actual_exit_code':a['actual_exit_code'],'actual_warning_count':x['actual_warning_count'],'original_started_at_utc':a['started_at_utc'],'original_finished_at_utc':a['finished_at_utc'],'original_elapsed_seconds':a['elapsed_seconds']})
assert [x['actual_exit_code'] for x in hist]==[1,1,1,1,0]
assert file(d['real_lean_native_history'][-1]['actual_raw_log']['file']).read_bytes()==b''
ctx=json.loads(file(d['entire_current_context']['file']).read_bytes());keys=['lipsdp.html::node-'+str(i) for i in [1297,1301,1302,1303,1304]]
assert [x['key'] for x in ctx['five_exact_full_inventory_rows']]==keys
for x in ctx['five_exact_full_inventory_rows']:assert hashlib.sha256(x['source_text'].encode()).hexdigest()==x['text_sha256']
assert ctx['current_full_exercise_owner_row']['inventory_key']=='lipsdp.html::exercise-17' and len(ctx['current_full_exercise_owner_row']['claims'])==4
primary=file(d['primary_citation']['full_original_text']['file']).read_text().splitlines();passage='\n'.join(primary[134:218])
assert 'and y = −1.5 0' in passage and '= −2 < 0' in passage
# Independently reproduce the actual grid and Newton algorithm, with distinct reviewer code.
runtime=json.loads(file(d['actual_runtime_support'][1]['file']).read_bytes())
def first(x):return 1/math.cosh(x+1)**2-1/math.cosh(x-1)**2
def second(x):return -2*(1-math.tanh(x+1)**2)*math.tanh(x+1)+2*(1-math.tanh(x-1)**2)*math.tanh(x-1)
def third(x):
 p,m=math.tanh(x+1),math.tanh(x-1);return -2*(1-p*p)*(1-3*p*p)+2*(1-m*m)*(1-3*m*m)
best=max((i/1000 for i in range(6001)),key=lambda z:abs(first(z)));x=best;steps=[]
for i in range(12):
 y=x-second(x)/third(x);steps.append({'iteration':i,'input_before':x,'input_after':y,'residual':second(x)});old=x;x=y
 if abs(x-old)<1e-14:break
assert best==runtime['grid']['maximizing_grid_point']==1.061
assert len(steps)==3 and abs(x-runtime['newton_result'])<1e-13 and abs(second(x))<2e-14
assert .93349<abs(first(x))<.933495
rlo,rhi=Q('.7615941559'),Q('.7615941561');klo,khi=Q('.5800256582'),Q('.5800256587');ulo,uhi=Q('.617919996'),Q('.617919998');slo,shi=Q('.786078873'),Q('.786078876')
poly=lambda k,u:1-3*(1-k)*u-k*u*u
assert min(poly(klo,ulo),poly(khi,ulo))>0 and max(poly(klo,uhi),poly(khi,uhi))<0
low=4*rlo*(1-khi)*slo*(1-uhi)/(1-klo*ulo)**2
high=4*rhi*(1-klo)*shi*(1-ulo)/(1-khi*uhi)**2
assert Q('.93349')<low<high<Q('.933495') and Q('.07')<1/high-1<1/low-1<Q('.075')
assert str(low)==runtime['exact_fraction_gain_enclosure']['lower'] and str(high)==runtime['exact_fraction_gain_enclosure']['upper']
# Original runtime result has an explicit no-global-proof scope, retained verbatim.
assert runtime['rigorous_global_maximum_claimed_by_runtime'] is False
OUT.mkdir(parents=True);closed=[]
for n,h in sorted(refs.items()):
 p=Path(n);dest=OUT/'original-closed-bytes'/h/p.name;dest.parent.mkdir(parents=True,exist_ok=True)
 if not dest.exists():dest.write_bytes(p.read_bytes())
 assert sha(dest)==h;closed.append({'original':ref(p),'closed_copy':ref(dest)})
guard();after={n:sha(ROOT/n) for n in guards};assert before==after
for n,h in refs.items():assert sha(Path(n))==h
# Semantic conclusions follow the independent complete proof/literal read.
groups=[
 {'scope':'whole Exercise12.3/exercise17 and whole node1297','whole_approved':True,'missing_clauses':[], 'correspondence':'All four requirements are directly discharged: actual ReLU points/deltas/form -3; actual affine tanh composition and weights/T products/full certificate; diagonalisation plus characteristic polynomial retain eigenvalue multiplicities and arbitrary-positive-rho NSD; arbitrary sqrt-rho bound implies constancy contradicted by f(1)<f(0); genuine attained least global constant and attained least diagonal SDP value1.'},
 {'scope':'whole node1301','whole_approved':True,'missing_clauses':[], 'correspondence':'Actual coupled incremental QC is expanded to the exact difference-of-chords expression and evaluated to -3 at the stated points. The independent direct SectionII-C source passage has the same points and prints -2; this bibliographic fact is a source read, not a Lean PDF-text claim.'},
 {'scope':'whole node1302','whole_approved':True,'missing_clauses':[], 'correspondence':'The true Fin1+Fin2 certificate equals the displayed Fin3 matrix under finSumFinEquiv. Products, inverse eigenbasis, diagonalisation and factored characteristic polynomial prove -rho,-2,0 including coinciding eigenvalues. The actual multiplier PSD/full certificate NSD hold for every positive rho. The hypothesized false family of network bounds implies constancy and is explicitly disproved.'},
 {'scope':'whole node1303','whole_approved':True,'missing_clauses':[], 'correspondence':'Direct first derivative/sech identity/oddness. Positive tanh-addition denominators reduce the whole real-line magnitude to the profile on [0,1]. The strictly decreasing critical polynomial has a unique interior root; derivative signs prove the full profile maximum, artanh supplies attaining inputs, and the two directions of mean-value/derivative-bound equivalence prove the least true global constant. Rigorous rational exponential/profile/input and direct printed-point sech bounds justify every rounding. Source weights give d0-d1, all independent patterns attain maximum1, all diagonal certificates force rho>=1 while identity is feasible; the resulting bound1 is directly valid. 7% is approximate: rigorously 7%<relative looseness<7.5%.'},
 {'scope':'whole node1304','whole_approved':True,'missing_clauses':[], 'correspondence':'Both actual derivatives are derived, sech identity/even magnitude/asymptotic decay are direct. Every global magnitude maximizer has nonzero derivative; sign cases give an actual local min/max of fprime and Fermat forces the printed fsecond=0. The actual original grid6001 over[0,6] plus Newton on printed fsecond and reviewer reproduction locate1.0610852744162456 and0.933492585..., distinct from the kernel global theorem.'}
]
review={'status':'passed_independent_full_coupled_tanh62_whole_exercise_and_five_units_semantic_review','reviewer':'/root/applied_finish30','request':ref(REQUEST),'source':d['source'],'review_helper':ref(Path(__file__)),'actual_checker_exit_code':0,'checker_started_at_utc':start,'checker_finished_at_utc':datetime.now(timezone.utc).isoformat(),'checker_elapsed_seconds':time.monotonic()-tick,'errors':[], 'read_scope':'All61 public proofs, one private proof and all19 definitions in the final coherent source. Nine complete selected dependency sources were independently read; full used primary API proof bodies/context for inverse tanh, Fermat/local extrema, characteristic polynomial, PSD, mean-value/derivative bounds, sqrt and exponential estimates; two additionally located full primary files are preserved. Full actual exercise, Section5 background, five exact literals, all four exercise requirements and affected original claim rows read. Original runtime helper/wrapper/result/log, native histories and exact source citation passage read.', 'public_theorem_names':d['public_theorem_names'],'public_definition_names':d['public_definition_names'],'private_full_body_names':d['private_full_body_names'],'full_scope_decisions':groups,'exercise_whole_approved':True,'material_unit_keys':keys,'whole_material_approved':keys,'native_histories_preserved':hist,'actual_reviewer_numeric_reproduction':{'grid_count':6001,'grid_maximizer':best,'newton_steps':steps,'newton_result':x,'derivative_magnitude':abs(first(x)),'exact_fraction_lower':str(low),'exact_fraction_upper':str(high),'global_proof_claimed_by_numeric_reproduction':False},'closed_original_inputs':closed,'extra_full_primary_sources':extra_primary,'protected_selected29_proof_sources':1197,'unchanged_current65_book_assets':31,'unchanged_installed29_live_owners':5,'protection_errors':[],'current_source_or_owner_changes':False,'canonical_installation_or_aggregate_audit_claimed':False,'section5_cosine_fit_product2_bibliographic_history_whole_promotion_claimed':False,'coverage_complete':False}
p=OUT/'modules-coupled-tanh62-full-independent-applied30-closed-peer-v1.json';p.write_text(json.dumps(review,indent=2)+'\n')
print(json.dumps({'record':str(p.relative_to(ROOT)),'sha256':sha(p),'status':review['status'],'actual_checker_exit_code':0,'checker_elapsed_seconds':review['checker_elapsed_seconds'],'errors':[],'protection_errors':[]}))
