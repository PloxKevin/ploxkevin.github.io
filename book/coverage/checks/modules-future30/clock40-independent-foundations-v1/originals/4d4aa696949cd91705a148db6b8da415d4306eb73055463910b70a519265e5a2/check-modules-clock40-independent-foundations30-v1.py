from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,re,sys
sys.dont_write_bytecode=True
ROOT=Path('/home/oxrexkevin/SafetyBased')
REQUEST=ROOT/'book/coverage/checks/modules-future30/clock40-all-penalty-association-v2/modules-clock40-actual-all-penalty-common-stationary-attainment-association-review-request30-v2.json'
OUT=Path('/tmp/modules-clock40-independent-foundations30-findings-v1.json')
assert not OUT.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):return {'file':str(p),'sha256':sha(p),'bytes':Path(p).stat().st_size}
closed={str(REQUEST):sha(REQUEST),str(Path(__file__)):sha(__file__)}
def add(q):
 p=Path(q['file']);p=p if p.is_absolute() else ROOT/p
 assert p.is_file() and sha(p)==q['sha256']
 if 'bytes'in q:assert p.stat().st_size==q['bytes']
 if p.is_relative_to(ROOT):assert p.resolve().is_relative_to(ROOT)
 closed[str(p)]=sha(p);return p
assert sha(REQUEST)=='10ebb7dbf800bb0dd79c3716344e73a4dffd38ab332f362b73ae2fe39d3e87be'
d=json.loads(REQUEST.read_bytes())
for n,h in d['required_evidence_artifacts_sha256'].items():add({'file':n,'sha256':h})
for n,q in d['original_closed_byte_aliases'].items():
 p=add(q);assert Path(n).is_file() and sha(n)==sha(p)
source=add(d['source']);body=source.read_text();assert body==d['full_source_body']
assert not re.search(r'\b(?:sorry|admit|native_decide|implemented_by)\b',body)
assert not re.search(r'^\s*(?:axiom|unsafe)\s',body,re.M)
ns='SafeLearning.CompleteModulesViabilityDualClock30'
names=[ns+'.'+n for n in re.findall(r'^theorem (\w+)',body,re.M)]
defs=[ns+'.'+n for n in re.findall(r'^def (\w+)',body,re.M)]
assert names==d['public_theorem_names'] and len(names)==d['public_theorem_count']==40
assert defs==d['public_definition_names'] and len(defs)==d['public_definition_count']==30
assert names[-3:]==d['new_theorem_names']
assert len(re.findall(r'^private theorem ',body,re.M))==1
old68=json.loads(add(d['original68_full_association_request']).read_bytes());oldsource=add(old68['families'][0]['source'])
assert source.read_bytes().startswith(oldsource.read_bytes()) and d['exact_entire_passed37_source_byte_prefix_preserved'] is True
prior68=add(d['original68_full_independent_peer']);assert sha(prior68)=='0b377d5a4daa9d9de294045cb8870403991c4505066608144c6400d5ecdc5eb4'
for q in d['new_complete_primary_used_API_sources']:add(q)
prior55=ROOT/'book/coverage/checks/modules-future30/duality55-independent-foundations-v1/modules-duality55-full-source-six-components-independent-foundations30-closed-peer-v2.json'
assert sha(prior55)=='155cf3e814e7a7f9651588323fdcf1614d089f45187f8be5053693eb19160316';add(ref(prior55))
context=json.loads(add(d['current_entire_Exercise7_5_and_used_context']).read_bytes())
inv=json.loads((ROOT/'book/coverage/inventory.json').read_bytes());owner=json.loads((ROOT/'book/coverage/modules.json').read_bytes())
key='viability.html::exercise-19';literal=next(r for r in inv['exercises']if r['key']==key)
assert literal==context['entire_current_exercise_inventory_row']
assert next(r for r in owner['exercises']if r['inventory_key']==key)==context['entire_original_pending_exercise_owner_row']
assert [h['true_exit_code']for h in d['genuine_new_native_history']]==[1,1,1,0]
assert [h['actual_warning_header_count']for h in d['genuine_new_native_history']]==[1,2,3,2]
assert [h['actual_exit_code']for h in d['old37_actual_native_history']]==[0,0]
assert [h['actual_warning_count']for h in d['old37_actual_native_history']]==[1,1]
def trial(h,old=False):
 a=json.loads(add(h['actual_native']if old else h['native']).read_bytes())
 s=add(h['actual_source']if old else h['source']);snap=add(h['actual_source_snapshot']if old else h['source_snapshot']);raw=add(h['actual_raw_log']if old else h['raw_log'])
 code=h['actual_exit_code']if old else h['true_exit_code'];warnings=h['actual_warning_count']if old else h['actual_warning_header_count']
 for k in ['actual_exit_code','actual_runner_exit_code']:assert type(a[k])is int and a[k]==code
 assert a['actual_command']==['lake','env','lean',a['source']] and a['actual_workdir']==str(ROOT/'verification/lean')
 assert sha(s)==sha(snap)==a['source_sha256_before']==a['source_sha256_after']==a['source_snapshot_sha256']
 assert sha(raw)==a['raw_log_sha256']
 assert len(re.findall(r'^.*:\d+:\d+: warning:',raw.read_text(),re.M))==warnings
 assert a['protection_errors']==[] and a['source_unchanged'] is True
 assert [a[k]for k in ['protected_selected29_proof_sources','unchanged_current65_book_assets','unchanged_installed29_live_owners']]==[1197,31,5]
 assert a['original_actual_runner']['sha256']=='5eca9a664c2c81d8c67c412a20be5782f6e84ec124a193233a5a2700e602575c'
 assert a['actual_source65_installed29_context']['sha256']=='ed8ca5f56d1f101b1a5898e367162bda47bd6b0845312ce3ba2dda4d58938ae2'
 for k,v in h['original_times'].items():assert a[k]==v
for h in d['genuine_new_native_history']:trial(h)
for h in d['old37_actual_native_history']:trial(h,True)
assert d['genuine_new_native_history'][-1]['source']['sha256']==sha(source)
prep=json.loads(add(d['actual_author_preparation']).read_bytes())
assert prep['status']=='passed' and type(prep['actual_exit_code'])is int and prep['actual_exit_code']==0 and prep['protection_errors']==[]
assert prep['actual_command']==['python3','/tmp/prepare-modules-clock40-all-penalty-association-request30-v2.py'] and prep['actual_workdir']==str(ROOT)
assert prep['helper_sha256_before']==prep['helper_sha256_after'] and prep['protected_inputs_sha256_before']==prep['protected_inputs_sha256_after']
for old,q in d['actual_author_preparation_original_byte_aliases'].items():assert sha(add(q))==sha(old)
assert sha(add(d['actual_author_preparation_original_byte_aliases'][prep['raw_log']]))==prep['raw_log_sha256']
failed=d['genuine_author1_failed_before_request_output'];a=json.loads(add(failed['native']).read_bytes())
assert type(a['actual_exit_code'])is int and a['actual_exit_code']==1 and a['protection_errors']==[]
for k in ['helper','runner','raw']:add(failed[k])
assert sha(add(failed['raw']))==a['raw_log_sha256']
assert all(d[k]is False for k in ['whole_Exercise7_5_requested','whole_Exercise7_5_approved','source_applied','canonical_pairs_executed','coverage_complete'])
reasons=[
 'The genuine first-jump geometric profile tends to0. For penalty<1 a sufficiently late geometric q is positive but below1-penalty, so the profile is positive somewhere. Compactness of its range with its limit0 gives an attained greatest value; positivity rules out the adjoined limit. Comparing the actual next term derives the slope bound (3/2)qk<=1-penalty. No maximizing index premise is supplied.',
 'For every initial clock n<=k, the actual first-jump return scaled by the positive factor2^-n is the same profile at n+j, so the derived discrete global maximum dominates all admissible histories. For n>k, the derived slope bound and monotone geometric q show immediate stopping dominates every later jump and the never-jump zero return. The single threshold feedback is therefore truly optimal from every surviving clock, including clocks beyond its threshold.',
 'For penalty<1 the prior two actual theorems construct the threshold feedback. For penalty>=1, all genuine first-jump Lagrangians are nonpositive and never-jump feedback attains0 from every clock. Thus one stationary feedback works simultaneously at all surviving initial states for every nonnegative penalty, without assuming a common optimizer.'
]
finding={
 'status':'passed_independent_full_clock40_all_penalty_common_stationary_attainment_association_review',
 'reviewer':'/root/foundations_recovery28','review_finished_at_utc':datetime.now(timezone.utc).isoformat(),
 'request':ref(REQUEST),'source':ref(source),'public_theorem_names':names,'public_theorem_count':40,
 'public_definition_names':defs,'public_definition_count':30,'private_first_failure_proof_count':1,
 'all40_entire_proof_bodies_actual_definitions_and_private_proof_read':True,
 'actual_proof_dependencies':'Mathlib plus the complete self-contained prior37 literal source prefix. No selected application declaration is used as an optimizer premise.',
 'new_complete_physical_primary_API_sources':d['new_complete_primary_used_API_sources'],
 'primary_read_scope':'Full geometric power convergence proof and domains, Tendsto.isCompact_insert_range and its actual cocompact/cofinite proof chain, and compact exists_isGreatest through the full exists_isLeast closed-directed-family proof read. Old first-failure, genuine finite-support HasSum, finite-cardinality injection and finite-mass stopping primary bodies and selected semantic contexts retain the exact continuing read in prior68. No unrelated primary theorem family is claimed reviewed.',
 'full_current_exercise7_5_and_original7_pending_claims_read':True,'current_full_context':d['current_entire_Exercise7_5_and_used_context'],
 'prior_full_sections3_5_read_and_original55_semantic_body_times_unchanged':ref(prior55),
 'prior_full37_source_and_associations_read_and_original68_body_times_unchanged':ref(prior68),
 'exact_entire_old37_source_byte_prefix_preserved':ref(oldsource),
 'semantic_decisions':[{'declaration':n,'approved_in_exact_scope':True,'missing_clauses':[],'mathematical_reason':r}for n,r in zip(names[-3:],reasons)],
 'requested_actual_Exercise7_5_d_clock_association_approved':True,'whole_exercise7_5_approved':False,
 'actual_arbitrary_penalty_construction':d['actual_arbitrary_penalty_construction'],
 'viability_and_assumption1_correspondence':d['viability_and_assumption1_correspondence'],
 'requested_scope':d['requested_scope'],'domain_scope':d['domain_scope'],
 'explicit_limits':['Common stationary attainment is quantified over every surviving natural starting clock; the terminated failure bookkeeping state carries no further reward/action.','The actual kernel and immediate post-exit failure are proved, and Tf=0 bounds failure only after exit; it places no bound on the viable clock delay.','The exact unsafe-maximizer search has shrinking positive risk and never crosses1. This is an actual infinite-state counterexample to automatic finite stopping, not a counterexample to the separately proved finite-feedback stopping theorem.','No full Exercise7.5, continuous-time, generic initial-law measurability or finite-state LP association is inferred.'],
 'current_owner_rows_unchanged':True,'genuine_new_native_history':d['genuine_new_native_history'],
 'old37_actual_native_history':d['old37_actual_native_history'],
 'genuine_author1_failure_preserved':d['genuine_author1_failed_before_request_output'],
 'actual_author_preparation':d['actual_author_preparation'],
 'integrity_does_not_substitute_for_source_correspondence':True,
 'original_closed_byte_aliases':d['original_closed_byte_aliases'],'required_evidence_artifacts_sha256':closed,'errors':[],
 'compiler_parser_source_owner_canonical_publication_mutation':False,'prospective_evidence_outside_frozen29':True,'coverage_complete':False}
OUT.write_text(json.dumps(finding,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'findings':ref(OUT),'new_associations':3,'requested_association_approved':True,'whole_exercise7_5':False,'errors':[]}))
