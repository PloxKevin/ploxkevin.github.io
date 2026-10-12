from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,re,sys
sys.dont_write_bytecode=True
ROOT=Path('/home/oxrexkevin/SafetyBased')
REQUEST=ROOT/'book/coverage/checks/modules-future30/finite-polytope8-strongduality-v2/modules-finite-polytope8-actual-history-CMDP-attained-strongduality-review-request30-v2.json'
OUT=Path('/tmp/modules-finitepolytope8-independent-foundations30-findings-v1.json')
assert not OUT.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):return {'file':str(p),'sha256':sha(p),'bytes':Path(p).stat().st_size}
closed={str(REQUEST):sha(REQUEST),str(Path(__file__)):sha(__file__)}
def add(q):
 p=Path(q['file']);p=p if p.is_absolute()else ROOT/p
 assert p.is_file()and sha(p)==q['sha256']
 if 'bytes'in q:assert p.stat().st_size==q['bytes']
 if p.is_relative_to(ROOT):assert p.resolve().is_relative_to(ROOT)
 closed[str(p)]=sha(p);return p
assert sha(REQUEST)=='e456be03e3d5074cb9da113836c36cad46462f00f71127d32799bff4f78ddfae'
d=json.loads(REQUEST.read_bytes())
for n,h in d['required_evidence_artifacts_sha256'].items():add({'file':n,'sha256':h})
for n,q in d['original_closed_byte_aliases'].items():
 p=add(q);assert Path(n).is_file()and sha(n)==sha(p)
source=add(d['source']);body=source.read_text();assert body==d['full_source_body']
assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by)\b',body)
ns=re.search(r'^namespace (\S+)',body,re.M).group(1)
names=[ns+'.'+n for n in re.findall(r'^theorem (\w+)',body,re.M)]
defs=[ns+'.'+n for n in re.findall(r'^def (\w+)',body,re.M)]
assert names==d['public_theorem_names']and len(names)==d['public_theorem_count']==8
assert defs==d['public_definition_names']and len(defs)==d['public_definition_count']==4
for q in d['selected_complete_dependency_sources']+d['complete_primary_used_API_sources']:add(q)
assert len(d['selected_complete_dependency_sources'])==12 and len(d['complete_primary_used_API_sources'])==7
prior=ROOT/'book/coverage/checks/modules-future30/finiteDP2-independent-foundations-v1/modules-finiteDP2-common-stationary-optimizer-association-independent-foundations30-closed-peer-v2.json'
assert sha(prior)=='19aaf74991167387b8059c2758b311a65b06eff786af5c1b0637feadf70ed696';add(ref(prior));pd=json.loads(prior.read_bytes())
priorselected=pd['all9_complete_selected_dependency_sources_read']+pd['additional3_complete_selected_used_chain_sources_read']
assert {q['sha256']for q in d['selected_complete_dependency_sources'][2:]} <= {q['sha256']for q in priorselected}
prior55=ROOT/'book/coverage/checks/modules-future30/duality55-independent-foundations-v1/modules-duality55-full-source-six-components-independent-foundations30-closed-peer-v2.json'
assert sha(prior55)=='155cf3e814e7a7f9651588323fdcf1614d089f45187f8be5053693eb19160316';add(ref(prior55))
add(d['original55_full_current_literal_and_component_request'])
contextpath=add(d['current_full_context']);context=json.loads(contextpath.read_bytes())
inv=json.loads((ROOT/'book/coverage/inventory.json').read_bytes());owner=json.loads((ROOT/'book/coverage/modules.json').read_bytes())
literal=next(r for r in inv['exercises']if r['key']=='viability.html::exercise-19')
assert literal==context['entire_current_exercise_inventory_row']
assert next(r for r in owner['exercises']if r['inventory_key']==literal['key'])==context['entire_original_pending_exercise_owner_row']
assert [h['true_exit_code']for h in d['genuine_native_history']]==[1,0,1,1,0]
assert [h['actual_warning_header_count']for h in d['genuine_native_history']]==[4,6,6,6,6]
for h in d['genuine_native_history']:
 a=json.loads(add(h['native']).read_bytes());s=add(h['source']);snap=add(h['source_snapshot']);raw=add(h['raw_log'])
 for k in ['actual_exit_code','actual_runner_exit_code']:assert type(a[k])is int and a[k]==h['true_exit_code']
 assert a['actual_command']==['lake','env','lean',a['source']]and a['actual_workdir']==str(ROOT/'verification/lean')
 assert sha(s)==sha(snap)==a['source_sha256_before']==a['source_sha256_after']==a['source_snapshot_sha256']
 assert sha(raw)==a['raw_log_sha256']
 assert len(re.findall(r'^.*:\d+:\d+: warning:',raw.read_text(),re.M))==h['actual_warning_header_count']
 assert a['protection_errors']==[]and a['source_unchanged']is True
 assert [a[k]for k in ['protected_selected29_proof_sources','unchanged_current65_book_assets','unchanged_installed29_live_owners']]==[1197,31,5]
 assert a['original_actual_runner']['sha256']=='5eca9a664c2c81d8c67c412a20be5782f6e84ec124a193233a5a2700e602575c'
 assert a['actual_source65_installed29_context']['sha256']=='ed8ca5f56d1f101b1a5898e367162bda47bd6b0845312ce3ba2dda4d58938ae2'
 for k,v in h['original_times'].items():assert a[k]==v
assert d['genuine_native_history'][-1]['source']['sha256']==sha(source)
for h in d['uncompiled_intermediate_drafts']:add(h['source']);assert h['compiled']is False
prep=json.loads(add(d['actual_author_preparation']).read_bytes())
assert prep['status']=='passed'and type(prep['actual_exit_code'])is int and prep['actual_exit_code']==0 and prep['protection_errors']==[]
assert prep['actual_command']==['python3','/tmp/prepare-modules-finite-polytope8-strongduality-request30-v2.py']and prep['actual_workdir']==str(ROOT)
assert prep['helper_sha256_before']==prep['helper_sha256_after']and prep['protected_inputs_sha256_before']==prep['protected_inputs_sha256_after']
for old,q in d['actual_author_preparation_original_byte_aliases'].items():assert sha(add(q))==sha(old)
assert sha(add(d['actual_author_preparation_original_byte_aliases'][prep['raw_log']]))==prep['raw_log_sha256']
failed=d['true_author1_failed_before_request_output'];failednative=json.loads(add(failed['native']).read_bytes())
assert type(failednative['actual_exit_code'])is int and failednative['actual_exit_code']==1
for q in [failed['helper'],failed['runner'],failed['raw']]:add(q)
assert sha(add(failed['raw']))==failednative['raw_log_sha256'] and failednative['protection_errors']==[]
add(d['original_association_request_v1'])
assert all(d[k]is False for k in ['whole_exercise_review_requested','whole_exercise_approved','source_applied','canonical_pairs_executed','coverage_complete'])
extra=[];extra_aliases={}
for relative in [
 'verification/lean/SafeLearning/CompleteFiniteCMDPActiveFlow.lean',
 'verification/lean/SafeLearning/CompleteFiniteNonnegativeAffineExtrema.lean',
 'verification/lean/.lake/packages/mathlib/Mathlib/Order/ConditionallyCompletePartialOrder/Basic.lean',
 'verification/lean/.lake/packages/mathlib/Mathlib/Data/Finset/Lattice/Fold.lean']:
 p=ROOT/relative;h=sha(p);q=Path('/tmp/foundations-finitepolytope8-full-used-primary30-v1')/h/p.name;q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists():assert sha(q)==h
 else:
  with q.open('xb')as f:f.write(p.read_bytes())
 assert sha(p)==sha(q)==h;extra.append(ref(q));extra_aliases[str(p)]=ref(q);closed[str(q)]=h
reasons=[
 'Compact finite convex hull and a closed feasible halfspace give an actual reward-maximizing feasible point. A finite slope maximum, including zero via Option I, constructs a nonnegative multiplier. For each strictly low-cost vertex, the exact feasible boundary mixture with every high-cost vertex derives the opposite slope bound. All vertex Lagrangians are bounded by the maximizing reward; affine convexity extends this to the entire hull. Evaluating at the feasible maximizer derives complementarity. Neither a multiplier nor a primal optimum is assumed.',
 'The actual compact convex flow set has its extreme points identified with genuine deterministic stationary occupancies by the fully read support-kernel rank and active-flow classification. Krein-Milman then represents it by their closed convex hull, and finiteness makes that hull compact and closed. The polytope representation is proved from the actual probability flow equations.',
 'The true occupancy reward identity applies the positive factor 1-gamma to actual feasibility. The constructed flow saddle is recovered as a genuine stationary randomized policy, and the positive scaling is cancelled to derive original expected-return feasibility, complementarity and global penalized optimality over every time-dependent Markov policy.',
 'Each fixed-penalty return functional is continuous on the actual compact flow set, so its image is bounded above. All genuine policy occupancies satisfy those flows and the true return identity transfers that bound; no dual bound premise is supplied.',
 'The constructed complementary saddle yields an actual greatest feasible reward and greatest penalized reward at its multiplier. At every other nonnegative multiplier the same feasible policy gives weak duality, using the separately derived bounded dual supremum. This proves an actual least dual value and attained primal/dual equality, including budgets with no strictly feasible policy.',
 'Every actual Bochner history-dependent return pair belongs to the actual history path occupancy image. The full proved flow-image equality and real recovery theorem construct a Markov policy realizing both reward and cost simultaneously.',
 'The history-to-Markov realization and actual constructed Markov path expected-return theorem give both directions of the primal and every-penalty dual value-set equality. No equality of optimal values is assumed.',
 'Actual history feasibility transfers through the realized reward/cost pair to the finite CMDP saddle theorem. The proved value-set identities then derive attained primal and dual equality for genuine all-history path returns, with a stationary randomized optimizer and nonnegative scalar multiplier.'
]
finding={
 'status':'passed_independent_full_finitepolytope8_scalar_finite_CMDP_attained_strongduality_association_review',
 'reviewer':'/root/foundations_recovery28','review_finished_at_utc':datetime.now(timezone.utc).isoformat(),
 'request':ref(REQUEST),'source':ref(source),'public_theorem_names':names,'public_theorem_count':8,'public_definition_names':defs,'public_definition_count':4,
 'all8_entire_proof_bodies_and_actual_definitions_read':True,
 'all12_complete_selected_dependency_sources_read':d['selected_complete_dependency_sources'],
 'selected_read_continuity':'The two new full LP/vertex-classification sources and two additional active-flow/support-extrema sources were read in this review; the other ten complete selected sources were fully read in the same continuing task and their exact bytes are bound to the prior finiteDP2 full-source review. No integrity-only source-correspondence inference is used.',
 'prior_full_finiteDP2_read_and_native_body_times_unchanged':ref(prior),
 'additional2_complete_selected_support_classification_sources_read':extra[:2],
 'complete_physical_primary_API_sources':d['complete_primary_used_API_sources']+extra[2:],
 'primary_read_scope':'Entire KreinMilman file and actual extremal separation/Zorn proof read. Full used finite-convex-hull compactness/closure, compact exists_isMaxOn, finite sup-prime construction and lower/upper-bound proofs, conditionally-complete IsGreatest.csSup_eq/IsLeast.csInf_eq, le_csSup and positive-factor cancellation proof bodies and surrounding typeclass domains read. The earlier full history-path/Bochner used-proof-chain read is retained through finiteDP2. Unrelated primary theorem families are not claimed reviewed.',
 'full_current_exercise7_5_and_original7_pending_claims_read':True,'current_full_context':d['current_full_context'],
 'prior_full_sections3_5_read_and_original55_semantic_body_times_unchanged':ref(prior55),
 'semantic_decisions':[{'declaration':n,'approved_in_exact_scope':True,'missing_clauses':[],'mathematical_reason':r}for n,r in zip(names,reasons)],
 'requested_single_risk_finite_CMDP_feasibility_alone_association_approved':True,'whole_exercise7_5_approved':False,
 'hypotheses_and_scope':d['hypotheses_and_scope'],'zero_budget_specialization':d['zero_budget_specialization'],'remaining_scope':d['remaining_scope'],
 'explicit_limits':['One scalar cost budget in a finite discounted probability model; not general multi-budget LP duality.','Some stationary feasible penalized maximizer and attained zero gap are proved; safety of every penalized maximizer is not implied.','The separate generic bounded-risk Slater result and all remaining exercise associations retain their original pending scope.'],
 'current_owner_rows_unchanged':True,'genuine_native_history':d['genuine_native_history'],'uncompiled_intermediate_drafts':d['uncompiled_intermediate_drafts'],
 'true_author1_failure_exact_preserved':d['true_author1_failed_before_request_output'],'actual_author_preparation':d['actual_author_preparation'],
 'integrity_does_not_substitute_for_source_correspondence':True,
 'original_closed_byte_aliases':{**d['original_closed_byte_aliases'],**extra_aliases},'required_evidence_artifacts_sha256':closed,'errors':[],
 'compiler_parser_source_owner_canonical_publication_mutation':False,'prospective_evidence_outside_frozen29':True,'coverage_complete':False}
OUT.write_text(json.dumps(finding,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'findings':ref(OUT),'public_count':8,'requested_association_approved':True,'whole_exercise7_5':False,'errors':[]}))
