from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,re,sys
sys.dont_write_bytecode=True
ROOT=Path('/home/oxrexkevin/SafetyBased')
REQUEST=ROOT/'book/coverage/checks/modules-future30/finiteDP2-association-v1/modules-finiteDP2-common-stationary-optimizer-association-review-request30-v2.json'
OUT=Path('/tmp/modules-finiteDP2-independent-foundations30-findings-v1.json')
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
assert sha(REQUEST)=='3d871a9e0be8490c779c8fbaeb591fdfaf096afe8d857844f87b7901e09c1474'
d=json.loads(REQUEST.read_bytes())
for n,h in d['required_evidence_artifacts_sha256'].items():add({'file':n,'sha256':h})
for n,q in d['original_closed_byte_aliases'].items():
 p=add(q);assert Path(n).is_file()and sha(n)==sha(p)
source=add(d['source']);body=source.read_text();assert body==d['full_source_body']
assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by)\b',body)
ns=re.search(r'^namespace (\S+)',body,re.M).group(1)
names=[ns+'.'+n for n in re.findall(r'^theorem (\w+)',body,re.M)]
assert names==d['public_theorem_names']and len(names)==d['public_theorem_count']==2
for q in d['selected_complete_dependency_sources']:add(q)
assert len(d['selected_complete_dependency_sources'])==9
add(d['complete_primary_fixedpoint_source'])
oldrequest=add(d['original55_full_current_literal_and_component_request'])
assert sha(oldrequest)=='baab5e6bf29af3a4e306c3c6954bbd7b906926d755880bafb015d0bf058892c0'
contextpath=add(d['current_full_context']);context=json.loads(contextpath.read_bytes())
inv=json.loads((ROOT/'book/coverage/inventory.json').read_bytes());owner=json.loads((ROOT/'book/coverage/modules.json').read_bytes())
literal=next(r for r in inv['exercises']if r['key']=='viability.html::exercise-19')
assert literal==context['entire_current_exercise_inventory_row']
assert next(r for r in owner['exercises']if r['inventory_key']==literal['key'])==context['entire_original_pending_exercise_owner_row']
a=json.loads(add(d['actual_native']).read_bytes());snap=add(d['actual_source_snapshot']);raw=add(d['actual_raw_log'])
for k in ['actual_exit_code','actual_runner_exit_code']:assert type(a[k])is int and a[k]==0
assert a['actual_command']==['lake','env','lean',a['source']]and a['actual_workdir']==str(ROOT/'verification/lean')
assert sha(source)==sha(snap)==a['source_sha256_before']==a['source_sha256_after']==a['source_snapshot_sha256']
assert sha(raw)==a['raw_log_sha256']and raw.read_bytes()==b''
assert a['protection_errors']==[]and a['source_unchanged']is True
assert [a[k]for k in ['protected_selected29_proof_sources','unchanged_current65_book_assets','unchanged_installed29_live_owners']]==[1197,31,5]
for k,v in d['original_times'].items():assert a[k]==v
assert d['true_first_trial0_empty_raw_zero_warnings']is True and d['original_body_and_times_untouched']is True
prep=json.loads(add(d['actual_author_preparation']).read_bytes())
assert prep['status']=='passed'and type(prep['actual_exit_code'])is int and prep['actual_exit_code']==0 and prep['protection_errors']==[]
assert prep['actual_command']==['python3','/tmp/prepare-modules-finiteDP2-association-request30-v1.py']and prep['actual_workdir']==str(ROOT)
assert prep['helper_sha256_before']==prep['helper_sha256_after']and prep['protected_inputs_sha256_before']==prep['protected_inputs_sha256_after']
for old,q in d['actual_author_preparation_original_byte_aliases'].items():assert sha(add(q))==sha(old)
assert sha(add(d['actual_author_preparation_original_byte_aliases'][prep['raw_log']]))==prep['raw_log_sha256']
add(d['original_association_request_v1'])
assert all(d[k]is False for k in ['whole_exercise_review_requested','whole_exercise_approved','source_applied','canonical_pairs_executed','coverage_complete'])
extra=[];extra_aliases={}
for relative in [
 'verification/lean/SafeLearning/CompleteFiniteControlledPathFlow.lean',
 'verification/lean/SafeLearning/CompleteFiniteCMDPRecovery.lean',
 'verification/lean/SafeLearning/CompleteFiniteTrajectoryReturns.lean',
 'verification/lean/.lake/packages/mathlib/Mathlib/Probability/Kernel/IonescuTulcea/Traj.lean',
 'verification/lean/.lake/packages/mathlib/Mathlib/Probability/Kernel/IonescuTulcea/PartialTraj.lean',
 'verification/lean/.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean']:
 p=ROOT/relative;h=sha(p);q=Path('/tmp/foundations-finiteDP2-full-used-primary30-v1')/h/p.name;q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists():assert sha(q)==h
 else:
  with q.open('xb')as f:f.write(p.read_bytes())
 assert sha(p)==sha(q)==h;extra.append(ref(q));extra_aliases[str(p)]=ref(q);closed[str(q)]=h
finding={
 'status':'passed_independent_full_finiteDP2_common_stationary_attainment_association_semantic_review',
 'reviewer':'/root/foundations_recovery28','review_finished_at_utc':datetime.now(timezone.utc).isoformat(),
 'request':ref(REQUEST),'source':ref(source),'public_theorem_names':names,'public_theorem_count':2,
 'all2_entire_proof_bodies_and_actual_definitions_read':True,
 'all9_complete_selected_dependency_sources_read':d['selected_complete_dependency_sources'],
 'additional3_complete_selected_used_chain_sources_read':extra[:3],
 'complete_Contracting_primary_fixedpoint_source_read':d['complete_primary_fixedpoint_source'],
 'additional_complete_physical_primary_files_with_used_proof_bodies_and_typeclass_scopes_read':extra[3:],
 'primary_used_scopes':'Full actual trajectory construction definition/probability instance, full marginal and successor joint-law proof bodies and preceding types; full partial trajectory definition/self identity; full used integral_tsum and integral_tsum_of_summable_integral_norm proof bodies. Full Contracting file, including actual Cauchy iteration existence/uniqueness proof. Unrelated Ionescu-Tulcea or DCT theorem families are not promoted.',
 'full_current_exercise7_5_and_original7_pending_claims_read':True,
 'current_full_context':d['current_full_context'],'original55_full_request_and_body_times_retained':d['original55_full_current_literal_and_component_request'],
 'semantic_decisions':[
 {'declaration':names[0],'approved_in_exact_scope':True,'missing_clauses':[],
 'mathematical_reason':'Actual finite Bellman action sup and normalized transition PMFs derive gamma contraction on the complete finite real function space. Banach iteration supplies the real fixed point rather than taking it as a premise. Finite action maxima construct a greedy stationary feedback solely from that value, before any initial PMF is supplied. Full actual infinite history path construction has normalized initial/transition laws; measurable finite rewards have geometrically summable integral norms, so the actual Bochner discounted return equals its occupancy functional. Bellman potential identity bounds every true history occupancy; actual pure-policy occupancy is supported on maximizing actions and attains equality. Hence the same feedback has actual optimal pathReturn simultaneously for every initial PMF, including each Dirac law. No common optimizer, desired return identity or attained value hypothesis is supplied by this new theorem.'},
 {'declaration':names[1],'approved_in_exact_scope':True,'missing_clauses':[],
 'mathematical_reason':'Deterministic finite next-state maps are substituted as genuine pure transition PMFs, and the actual stage reward-minus-penalty-times-cost is substituted into the arbitrary finite real reward theorem. Finite state/action rewards and costs are bounded automatically; gamma is NNReal with gamma<1. This establishes exactly the source finite deterministic discounted dynamic-programming stationary common-attainment parenthetical for each fixed penalty, without asking for optimizer existence as a premise.'}],
 'requested_parenthetical_association_approved':True,'whole_exercise7_5_approved':False,
 'remaining_scope':d['remaining_scope'],'current_owner_rows_unchanged':True,
 'actual_original_first0_empty_raw_zero_warnings':True,'genuine_native':d['actual_native'],'original_genuine_times':d['original_times'],
 'integrity_does_not_substitute_for_source_correspondence':True,
 'original_closed_byte_aliases':{**d['original_closed_byte_aliases'],**extra_aliases},
 'required_evidence_artifacts_sha256':closed,'errors':[],
 'compiler_parser_source_owner_canonical_publication_mutation':False,
 'prospective_evidence_outside_frozen29':True,'coverage_complete':False}
OUT.write_text(json.dumps(finding,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'findings':ref(OUT),'public_count':2,'requested_association_approved':True,'whole_exercise7_5':False,'errors':[]}))
