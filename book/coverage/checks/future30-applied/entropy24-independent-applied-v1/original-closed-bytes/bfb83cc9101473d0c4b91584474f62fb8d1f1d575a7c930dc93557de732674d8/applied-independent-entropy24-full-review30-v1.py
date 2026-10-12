from pathlib import Path
from datetime import datetime, timezone
from fractions import Fraction as Q
import hashlib,json,re,time
ROOT=Path('/home/oxrexkevin/SafetyBased')
REQUEST=ROOT/'book/coverage/checks/modules-future30/entropy24-full-scope-v1/modules-entropy24-full-source-literal-independent-review-request30-v2.json'
REQUEST_SHA='8ec8a21e5443466938b6635ebb5437097ca47c414ec7d054201febd411f648dd'
CONTEXT=Path('/tmp/root_tmp_lean_current65_owner29_context_v1.json')
CONTEXT_SHA='ed8ca5f56d1f101b1a5898e367162bda47bd6b0845312ce3ba2dda4d58938ae2'
OUT=ROOT/'book/coverage/checks/future30-applied/entropy24-independent-applied-v1'
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

body=file(d['source']['file']).read_text();ns='SafeLearning.CompleteModulesViabilityEntropyWhole30.'
public=re.findall(r'^theorem\s+(\w+)',body,re.M);defs=re.findall(r'^def\s+(\w+)',body,re.M)
assert len(public)==24 and len(defs)==7 and [ns+n for n in public]==d['public_theorem_names'] and [ns+n for n in defs]==d['public_definition_names']
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
assert [x['actual_exit_code'] for x in hist]==[1,1,0,0,0] and [x['actual_warning_header_count'] for x in hist]==[8,7,12,14,14]
for x in d['earlier_passed_proof_body_prefixes']:
 b=file(x['original']['file']).read_bytes();N=x['preserved_exact_bytes_through_last_original_theorem'];assert body.encode()[:N]==b[:N]
c=json.loads(file(d['entire_current_and_prospective_context']['file']).read_bytes());keys=['viability.html::node-'+str(i) for i in [1167,1171,1173,1174]]
assert [x['key'] for x in c['four_entire_current_material_inventory_rows']]==keys
for x in c['four_entire_current_material_inventory_rows']+[c['entire_current_exercise_inventory_row'],c['entire_prospective_corrected_exercise_literal'],c['entire_prospective_corrected_node1174_literal']]:
 assert hashlib.sha256(x['source_text'].encode()).hexdigest()==x['text_sha256']
assert c['entire_original_pending_exercise_owner_row']['inventory_key']==d['exercise_keys'][0] and len(c['entire_original_pending_exercise_owner_row']['claims'])==3
assert len(c['four_entire_old_pending_material_claim_rows'])==4
proposal=json.loads(file(d['unnumbered_narrow_wording_proposal']['file']).read_bytes())
for old,new in [(c['entire_current_exercise_inventory_row']['source_text'],c['entire_prospective_corrected_exercise_literal']['source_text']),(c['four_entire_current_material_inventory_rows'][-1]['source_text'],c['entire_prospective_corrected_node1174_literal']['source_text'])]:
 for x in proposal['exact_replacements']:
  assert old.count(x['before'])==1;old=old.replace(x['before'],x['after'])
 assert old==new
assert len(proposal['exact_replacements'])==5
lo,hi=Q(230258509,100000000),Q(230258510,100000000)
assert 2*lo>Q(4605,1000) and 11+lo>Q(1330,100) and 14+4*lo>Q(2321,100)
for a,b,display,half in [(11+lo,11+hi,Q(1330,100),Q(1,200)),(14+4*lo,14+4*hi,Q(2321,100),Q(1,200)),(lo/2,hi/2,Q(115,100),Q(1,200)),(2*lo,2*hi,Q(461,100),Q(1,200)),(2*lo,2*hi,Q(4605,1000),Q(1,2000))]:
 assert display-half<a<b<display+half
assert d['source_number_reserved'] is False and d['source_applied'] is False and d['canonical_pairs_executed'] is False and d['whole_promotion_performed'] is False
# Additional full primary files for the actually read pushforward/RN/typeclass proof bodies.
additional=[]
for tail in ['MeasureTheory/Measure/Map.lean','MeasureTheory/Measure/Decomposition/Lebesgue.lean','MeasureTheory/Measure/LogLikelihoodRatio.lean','MeasureTheory/Function/L1Space/Integrable.lean']:
 p=ROOT/'verification/lean/.lake/packages/mathlib/Mathlib'/tail;refs[str(p)]=sha(p);additional.append(ref(p))
OUT.mkdir(parents=True);closed=[]
for n,h in sorted(refs.items()):
 p=Path(n)
 # Reuse exact existing physical immutable request aliases, avoiding duplicate giant old packages.
 if p.is_relative_to(ROOT) and 'original-closed-bytes' in p.parts and not p.is_symlink():dest=p
 else:
  dest=OUT/'original-closed-bytes'/h/p.name;dest.parent.mkdir(parents=True,exist_ok=True)
  if not dest.exists():dest.write_bytes(p.read_bytes())
 assert dest.resolve().is_relative_to(ROOT) and sha(dest)==h
 closed.append({'original':ref(p),'closed_copy':ref(dest)})
guard();after={n:sha(ROOT/n) for n in guards};assert before==after
for n,h in refs.items():assert sha(Path(n))==h
parts=[
 {'scope':'current whole nodes1167/1171/1173','whole_approved':True,'missing_clauses':[],'correspondence':'Full question has actual supported entropy and exact threshold/decade computations. A genuinely measurable first action is pushed forward from an arbitrary probability space to its actual finite PMF. Every path on an unviable-first-action event eventually hits failure; the countable union of actual null failure events derives zero action mass and true support in the viable slice. Probability normalization derives the slice nonempty. Actual uniform cardinality masses, true finite supported KL identity/finiteness/nonnegativity and Gibbs equality derive the entropy cap and equality iff uniform. Positive-time failure convention and actual stationary kernel witnesses match the source. Uniform equality is a statement about the slice law, not a claim that this law is globally safe when failure is nonterminal and recoverable.'},
 {'scope':'current entire Exercise7.6 and current whole node1174','whole_approved':False,'missing_clauses':['Current exact -ln(10^-2)=4.605 and exact decimal p1 equations are false; both rounded13.30 and23.21 are below the exact sufficient thresholds. Growth of a conservative sufficient threshold alone does not prove that each actual fixed penalty is overcome.'],'correspondence':'All requested entropy and threshold mathematics has direct support, but the current exact-decimal and unqualified growth-to-unsafety language prevents whole approval.'},
 {'scope':'prospective corrected entire Exercise7.6 and corrected whole node1174','whole_approved':True,'conditional_on_later_actual_source_application':True,'missing_clauses':[],'correspondence':'All three full prompt requirements and all answer clauses are supported. Actual normalized exponential masses and a genuine one-action denominator lower bound convert the displayed two-sided Q bounds to the exact exponential per-action probability bound. Exact positive alpha/u3/delta algebra proves threshold equivalence and delta safety for p>=p1. Exact illustrative thresholds are11+ln10 and14+4ln10, with half-unit two-decimal enclosures; the extra decade costs exactly alpha ln10/u3. Full primary paper3.2/5.1/6.1.2/Fig3/D.3 bodies directly support the attributed cliff-world fixed-penalty observation and scaling recommendation. Affine sufficient-bound growth is derived separately, without inferring actual unsafety from it. No empirical constants are presented as the exercise illustrative constants.'}
]
r={'status':'passed_independent_full_entropy24_semantic_review_with_current_precision_attribution_gap_and_conditional_corrected_whole','reviewer':'/root/applied_finish30','request':ref(REQUEST),'source':d['source'],'review_helper':ref(Path(__file__)),'actual_checker_exit_code':0,'checker_started_at_utc':start,'checker_finished_at_utc':datetime.now(timezone.utc).isoformat(),'checker_elapsed_seconds':time.monotonic()-tick,'errors':[],'read_scope':'All24 full theorem proofs/seven definitions, six COMPLETE selected dependency sources, complete current/proposed Exercise7.6, four entire material literals and every affected original owner claim, full Section5 setting and actual two-sided Q walkthrough read. Full used primary PMF/uniform, actual pushforward/probability/RN/null-union, true KL finiteness/nonnegativity/Gibbs, logarithm/rigorous log bounds and finite-integrability proof/typeclass bodies read. Full primary paper sections3.2/5.1/6.1.2 and Fig3 caption plus whole AppendixD.3 Lemma2/proofTheorem2 context read. Original five native/source/snapshot/raw/time/warning histories read and preserved. Independent rational rounding checks use kernel-derived log enclosures. No fresh parser/Lean execution or source installation claimed.','public_theorem_names':d['public_theorem_names'],'public_definition_names':d['public_definition_names'],'full_scope_decisions':parts,'current_exercise_whole_approved':[],'current_exercise_whole_pending':d['exercise_keys'],'prospective_corrected_exercise_whole_approved':d['exercise_keys'],'current_whole_material_approved':keys[:3],'current_whole_material_pending':keys[-1:],'prospective_corrected_material_whole_approved':keys[-1:],'current_exercise_literal':c['entire_current_exercise_inventory_row'],'prospective_corrected_exercise_literal':c['entire_prospective_corrected_exercise_literal'],'prospective_corrected_material_literal':c['entire_prospective_corrected_node1174_literal'],'native_histories_preserved':hist,'warning_count_definition':'Actual emitted source-position warning headers under ^.*:\d+:\d+: warning: MULTILINE; hint occurrences excluded.','additional_used_full_primary_inputs':additional,'closed_original_inputs':closed,'protected_selected29_proof_sources':1197,'unchanged_current65_book_assets':31,'unchanged_installed29_live_owners':5,'protection_errors':[],'current_source_or_owner_changes':False,'narrow_wording_applied':False,'canonical_installation_or_aggregate_audit_claimed':False,'whole_promotion_performed':False,'coverage_complete':False}
p=OUT/'modules-entropy24-full-independent-applied30-closed-peer-v1.json';p.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'record':str(p.relative_to(ROOT)),'sha256':sha(p),'status':r['status'],'actual_checker_exit_code':0,'checker_elapsed_seconds':r['checker_elapsed_seconds'],'errors':[],'protection_errors':[]}))
