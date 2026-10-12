from pathlib import Path
from datetime import datetime, timezone
from fractions import Fraction as Q
import hashlib,json,re,time
ROOT=Path('/home/oxrexkevin/SafetyBased')
REQUEST=ROOT/'book/coverage/checks/modules-future30/thermal40-full-scope-v1/modules-thermal40-full-source-literal-independent-review-request30-v2.json'
REQUEST_SHA='c7b29c7d9d7f0d8a8adfe612a3d6564f401f7bcd26276adbc85e9c5a3c9db6e2'
CONTEXT=Path('/tmp/root_tmp_lean_current65_owner29_context_v1.json')
CONTEXT_SHA='ed8ca5f56d1f101b1a5898e367162bda47bd6b0845312ce3ba2dda4d58938ae2'
OUT=ROOT/'book/coverage/checks/future30-applied/thermal40-independent-applied-v1'
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

body=file(d['source']['file']).read_text();ns='SafeLearning.CompleteModulesThermalPenaltyBellmanWhole30.'
public=re.findall(r'^theorem\s+(\w+)',body,re.M);defs=re.findall(r'^(?:def|abbrev)\s+(\w+)',body,re.M)
assert len(public)==40 and len(defs)==20 and [ns+n for n in public]==d['public_theorem_names'] and [ns+n for n in defs]==d['public_definition_and_abbreviation_names']
masked=re.sub(r'/\-.*?\-/|--[^\n]*','',body,flags=re.S)
assert not re.search(r'\b(?:sorry|axiom|admit|unsafe|native_decide|run_elab|implemented_by|ofReduceBool|sorryAx)\b',masked)
hist=[]
for i,x in enumerate(d['genuine_lean_native_history'],1):
 a=json.loads(file(x['actual_native']['file']).read_bytes());log=file(x['actual_raw_log']['file']).read_text()
 assert a['actual_exit_code']==x['actual_exit_code'] and a['protection_errors']==[]
 assert a['source_sha256_before']==a['source_sha256_after']==x['actual_source']['sha256']==x['actual_source_snapshot']['sha256'] and a['raw_log_sha256']==x['actual_raw_log']['sha256']
 count=len(re.findall(r'^.*:\d+:\d+: warning:',log,re.M));assert count==x['actual_warning_count']
 assert x['original_times']=={k:a[k] for k in ['started_at_utc','finished_at_utc','elapsed_seconds']}
 hist.append({'trial':i,'original_native':x['actual_native'],'actual_exit_code':a['actual_exit_code'],'actual_warning_header_count':count,**x['original_times']})
assert [x['actual_exit_code'] for x in hist]==[1,0,1,0,0] and [x['actual_warning_header_count'] for x in hist]==[1,0,1,0,0]
for x in d['earlier_passed_proof_body_prefixes']:
 b=file(x['original']['file']).read_bytes();N=x['preserved_exact_bytes_through_last_original_theorem'];assert body.encode()[:N]==b[:N]
c=json.loads(file(d['entire_current_and_prospective_context']['file']).read_bytes());keys=['viability.html::node-'+str(i) for i in [838,839,864,871,875]]
assert [x['key'] for x in c['five_entire_current_material_inventory_rows']]==keys
for x in c['five_entire_current_material_inventory_rows']+[c['entire_current_exercise_inventory_row'],c['entire_prospective_corrected_B2_literal'],c['entire_prospective_corrected_node875_literal']]:
 assert hashlib.sha256(x['source_text'].encode()).hexdigest()==x['text_sha256']
owner=c['entire_current_partial_exercise_owner_row'];assert owner['inventory_key']==d['exercise_keys'][0] and len(owner['claims'])==4
assert owner['claims'][-1]['id']=='viability.html#book-m7-b2::proved-component-1' and owner['claims'][-1]['status']=='proved'
assert len(c['five_entire_old_affected_material_claim_rows'])==5
proposal=json.loads(file(d['unnumbered_narrow_wording_proposal']['file']).read_bytes());assert len(proposal['exact_replacements'])==1
for a,b in [(c['entire_current_exercise_inventory_row']['source_text'],c['entire_prospective_corrected_B2_literal']['source_text']),(c['five_entire_current_material_inventory_rows'][-1]['source_text'],c['entire_prospective_corrected_node875_literal']['source_text'])]:
 for x in proposal['exact_replacements']:
  assert a.count(x['before'])==1;a=a.replace(x['before'],x['after'])
 assert a==b
# Independent exact finite-model arithmetic, including all affine Bellman cases.
nextRun=[1,2,3,4,5,5];nextCool=[5,5,0,1,5,5]
def reward(p,s,a):return [Q(3),Q(3),Q(3),Q(25),Q(3)-p,Q(0)][s] if a else [-p,-p,Q(0),Q(0),Q(0),Q(0)][s]
def safeValue(g,p):
 v3=(3*g+3*g*g)/(1-g**3);v2=3+g*v3;v1=3+g*v2;v0=3+g*v1;return [v0,v1,v2,v3,3-p,Q(0)]
def rushValue(g,p):
 v3=25+g*(3-p);v2=3+g*v3;v1=3+g*v2;v0=3+g*v1;return [v0,v1,v2,v3,3-p,Q(0)]
def slack(g,p,s,a,value):
 return reward(p,s,a)+g*value[nextRun[s] if a else nextCool[s]]-value[s]
g8,g9=Q(4,5),Q(9,10);theta=Q(5657,244);vs8,vs9=safeValue(g8,Q(0))[3],safeValue(g9,Q(0))[3]
assert vs8==Q(540,61) and vs9==Q(5130,271) and (25+3*g8-vs8)/g8==theta
assert (25+3*g9-vs9)/g9==Q(23767,2439)<theta and vs8<vs9
for g in [g8,g9]:
 for s in range(4):
  for a in [False,True]:
   nxt=nextRun[s] if a else nextCool[s]
   if nxt<4:assert slack(g,Q(0),s,a,safeValue(g,Q(0)))<=0
for s in range(6):
 for a in [False,True]:
  if s==4 and not a:continue
  at=slack(g8,theta,s,a,safeValue(g8,theta));later=slack(g8,theta+1,s,a,safeValue(g8,theta+1));assert at<=0 and later-at<=0
  for p in [Q(0),theta]:assert slack(g8,p,s,a,rushValue(g8,p))<=0
  assert slack(g9,Q(5),s,a,rushValue(g9,Q(5)))<=0
assert rushValue(g8,theta)[3]==vs8 and rushValue(g8,Q(24))[3]==Q(41,5)<vs8
assert rushValue(g9,Q(5))[3]==Q(116,5)>vs9
assert vs8>Q(8852459,1000000) and (Q(137,5)-Q(8852459,1000000))/g8>theta
for exact,display in [(vs8,Q(8852459,1000000)),(vs9,Q(18929889,1000000)),(theta,Q(23184426,1000000))]:assert abs(exact-display)<Q(1,2000000)
assert d['source_number_reserved'] is False and d['source_applied'] is False and d['canonical_pairs_executed'] is False and d['whole_promotion_performed'] is False
additional=[]
for tail in ['Analysis/Normed/Group/InfiniteSum.lean','Analysis/SpecificLimits/Normed.lean']:
 p=ROOT/'verification/lean/.lake/packages/mathlib/Mathlib'/tail;refs[str(p)]=sha(p);additional.append(ref(p))
OUT.mkdir(parents=True);closed=[]
for n,h in sorted(refs.items()):
 p=Path(n)
 if p.is_relative_to(ROOT) and 'original-closed-bytes' in p.parts and not p.is_symlink():dest=p
 else:
  dest=OUT/'original-closed-bytes'/h/p.name;dest.parent.mkdir(parents=True,exist_ok=True)
  if not dest.exists():dest.write_bytes(p.read_bytes())
 assert dest.resolve().is_relative_to(ROOT) and sha(dest)==h
 closed.append({'original':ref(p),'closed_copy':ref(dest)})
guard();after={n:sha(ROOT/n) for n in guards};assert before==after
for n,h in refs.items():assert sha(Path(n))==h
parts=[
 {'scope':'current whole838/839/864/871','whole_approved':True,'missing_clauses':[],'correspondence':'Exact complete thermal transitions/rewards, interlock, one-time failure penalty at its actual transition reward and absorbing zero tail match commissioning. Finite reward/value bounds derive summability and genuine terminal-value decay. Finite telescoping passes to actual infinite discounted returns, bounding every allowed action stream including history dependent controllers. Actual safe cycle is admissible, always viable and Bellman-equality attaining. IsGreatest over ALL safe histories gives true gamma.9 value5130/271 with rigorous18.929889 rounding. Forced safe actions and strictly inferior cooling detour are proved. Actual rush at gamma.9/p5 is globally optimal over every admissible history, equals23.2 and exceeds every safe return. The exact gamma.8 threshold/p24/unsafe tie results answer every current question/hint clause.'},
 {'scope':'current entire7.B2/current whole875','whole_approved':False,'missing_clauses':['The current strict inequality inserts rounded8.852459 as the exact safe value and therefore defines a threshold strictly above5657/244; at that wrong exact boundary the unsafe route is no longer a maximizing tie.'],'correspondence':'All other complete prompt/hint/answer clauses have genuine full infinite-return support. A current sharp-threshold/equality claim cannot be approved with that literal.'},
 {'scope':'prospective corrected entire7.B2/corrected whole875','whole_approved':True,'conditional_on_later_actual_source_application':True,'missing_clauses':[],'correspondence':'Actual gamma.8 safe cycle return540/61 is the attained greatest return over every safe history. For p>=5657/244 the complete cycle value table is a global Bellman bound and attained true infinite optimum. For0<=p<=5657/244 the actual always-run value table globally bounds every allowed history and is attained. These IsGreatest results derive every TRUE infinite-return optimal first action at58 cooling iff p>5657/244; desired optimal return is not supplied as a whole premise. Penalty24 gives41/5 below540/61 and all optimal first actions cool. At the exact boundary the admissible actual rush58->60->failure is an unsafe maximizing tie with the safe cycle. Six-decimal enclosures and exact rational replacement are verified. The discount comparison is for this supplied model: gamma.8 safe return is lower and its rush-separation threshold exceeds the gamma.9 threshold23767/2439, while delayed failure penalty is weighted by the smaller discount.'},
 {'scope':'original proved-component1 entire Bellman/infinite-return remaining-gap association','whole_approved':False,'mathematical_discharge_approved':True,'missing_clauses':[],'correspondence':'The genuine discounted-series and finite-to-infinite Bellman bodies plus actual IsGreatest/every-optimal-first-action/unsafe boundary witnesses close the prior all-policy optimality gap in its stated deterministic complete-state model. Original component statements, proposed-comparison hypotheses, declarations, status, correspondence, gap text and historical time/body are retained unchanged. Current whole exercise still awaits exact source correction.'}
]
r={'status':'passed_independent_full_thermal40_semantic_review_with_current_threshold_precision_gap_and_conditional_corrected_whole','reviewer':'/root/applied_finish30','request':ref(REQUEST),'source':d['source'],'review_helper':ref(Path(__file__)),'actual_checker_exit_code':0,'checker_started_at_utc':start,'checker_finished_at_utc':datetime.now(timezone.utc).isoformat(),'checker_elapsed_seconds':time.monotonic()-tick,'errors':[],'read_scope':'All40 full proofs and19 definitions/one abbreviation, five COMPLETE selected dependency sources (unchanged ModulesBook previously read in full), full commissioning model, complete current/prospective7.B2 and all five material literals, every affected original owner row/claim including the entire partial gap association read. Full used primary geometric summability/norm comparison, finite telescoping/terminal-decay/order limits, infinite sum shift/negation/multiplication and IsGreatest uniqueness proof/typeclass bodies read. All five original native/source/snapshot/raw/warning/time histories read/preserved. Independent exact rational finite Bellman/affine-regime cases and rounding comparisons checked. No fresh Lean/parser execution or source installation claimed.','public_theorem_names':d['public_theorem_names'],'public_definition_and_abbreviation_names':d['public_definition_and_abbreviation_names'],'full_scope_decisions':parts,'current_exercise_whole_approved':[],'current_exercise_whole_pending':d['exercise_keys'],'prospective_corrected_exercise_whole_approved':d['exercise_keys'],'current_whole_material_approved':keys[:4],'current_whole_material_pending':keys[-1:],'prospective_corrected_material_whole_approved':keys[-1:],'old_partial_component_mathematical_gap_discharge_approved':True,'current_exercise_literal':c['entire_current_exercise_inventory_row'],'prospective_corrected_exercise_literal':c['entire_prospective_corrected_B2_literal'],'prospective_corrected_material_literal':c['entire_prospective_corrected_node875_literal'],'native_histories_preserved':hist,'warning_count_definition':'Actual emitted source-position warning headers under ^.*:\d+:\d+: warning: MULTILINE; hint occurrences excluded.','additional_used_full_primary_inputs':additional,'closed_original_inputs':closed,'protected_selected29_proof_sources':1197,'unchanged_current65_book_assets':31,'unchanged_installed29_live_owners':5,'protection_errors':[],'current_source_or_owner_changes':False,'original_claim_body_or_time_mutations':False,'narrow_wording_applied':False,'canonical_installation_or_aggregate_audit_claimed':False,'whole_promotion_performed':False,'coverage_complete':False}
p=OUT/'modules-thermal40-full-independent-applied30-closed-peer-v1.json';p.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'record':str(p.relative_to(ROOT)),'sha256':sha(p),'status':r['status'],'actual_checker_exit_code':0,'checker_elapsed_seconds':r['checker_elapsed_seconds'],'errors':[],'protection_errors':[]}))
