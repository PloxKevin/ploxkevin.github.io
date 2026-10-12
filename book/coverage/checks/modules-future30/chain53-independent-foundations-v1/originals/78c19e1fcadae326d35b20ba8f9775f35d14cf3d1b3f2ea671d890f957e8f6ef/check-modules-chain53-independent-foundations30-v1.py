from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,re,sys
sys.dont_write_bytecode=True
ROOT=Path('/home/oxrexkevin/SafetyBased')
REQUEST=ROOT/'book/coverage/checks/modules-future30/chain53-dirac-association-v1/modules-chain53-actual-Dirac2-dual-safe-primal-association-review-request30-v2.json'
OUT=Path('/tmp/modules-chain53-independent-foundations30-findings-v1.json')
assert not OUT.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):return {'file':str(p),'sha256':sha(p),'bytes':Path(p).stat().st_size}
closed={str(REQUEST):sha(REQUEST),str(Path(__file__)):sha(__file__)}
def add(q):
 p=Path(q['file']);p=p if p.is_absolute() else ROOT/p
 assert p.is_file() and sha(p)==q['sha256']
 if 'bytes' in q:assert p.stat().st_size==q['bytes']
 if p.is_relative_to(ROOT):assert p.resolve().is_relative_to(ROOT)
 closed[str(p)]=sha(p);return p
assert sha(REQUEST)=='f197bdaec8a950897f2d465ecdbccb6a88b2f1353938623abc0308aa9bd4b91b'
d=json.loads(REQUEST.read_bytes())
for n,h in d['required_evidence_artifacts_sha256'].items():add({'file':n,'sha256':h})
for n,q in d['original_closed_byte_aliases'].items():
 p=add(q);assert Path(n).is_file() and sha(n)==sha(p)
source=add(d['source']);body=source.read_text();assert body==d['full_source_body']
assert not re.search(r'\b(?:sorry|admit|native_decide|implemented_by)\b',body)
assert not re.search(r'^\s*(?:axiom|unsafe)\s',body,re.M)
ns='SafeLearning.CompleteModulesChainPenaltyWhole30'
names=[ns+'.'+n for n in re.findall(r'^theorem (\w+)',body,re.M)]
defs=[ns+'.'+n for n in re.findall(r'^(?:def|abbrev) (\w+)',body,re.M)]
assert names==d['public_theorem_names'] and len(names)==d['public_theorem_count']==53
assert defs==d['public_definition_and_abbreviation_names'] and len(defs)==d['public_definition_and_abbreviation_count']==27
assert names[-4:]==d['new_theorem_names']
old49=json.loads(add(d['original49_full_scope_request']).read_bytes())
oldsource=add(old49['source']);assert source.read_bytes().startswith(oldsource.read_bytes())
assert d['exact_entire_passed49_source_byte_prefix_preserved'] is True
for q in d['selected_complete_dependency_sources']+d['new_complete_primary_used_API_sources']:add(q)
for q in d['original49_primary_used_API_full_sources']:add(q['exact_physical_byte_alias'])
assert len(d['selected_complete_dependency_sources'])==5
prior55=ROOT/'book/coverage/checks/modules-future30/duality55-independent-foundations-v1/modules-duality55-full-source-six-components-independent-foundations30-closed-peer-v2.json'
assert sha(prior55)=='155cf3e814e7a7f9651588323fdcf1614d089f45187f8be5053693eb19160316';add(ref(prior55))
context=json.loads(add(d['current_entire_Exercise7_5_and_used_context']).read_bytes())
chaincontext=json.loads(add(d['original49_full_current_Exercise7_4_and_used_context']).read_bytes())
inv=json.loads((ROOT/'book/coverage/inventory.json').read_bytes());owner=json.loads((ROOT/'book/coverage/modules.json').read_bytes())
for ctx,key in [(context,'viability.html::exercise-19'),(chaincontext,'viability.html::exercise-18')]:
 literal=next(r for r in inv['exercises'] if r['key']==key)
 assert literal==ctx['entire_current_exercise_inventory_row']
 assert next(r for r in owner['exercises'] if r['inventory_key']==key)==ctx['entire_original_pending_exercise_owner_row']
assert [h['true_exit_code']for h in d['genuine_new_native_history']]==[1,0]
assert [h['actual_warning_header_count']for h in d['genuine_new_native_history']]==[1,1]
assert [h['actual_exit_code']for h in d['old49_actual_native_history']]==[1,1,1,1,0,0]
assert [h['actual_warning_count']for h in d['old49_actual_native_history']]==[8,2,3,3,1,1]
def trial(h,old=False):
 a=json.loads(add(h['actual_native']if old else h['native']).read_bytes())
 s=add(h['actual_source']if old else h['source']);snap=add(h['actual_source_snapshot']if old else h['source_snapshot']);raw=add(h['actual_raw_log']if old else h['raw_log'])
 code=h['actual_exit_code']if old else h['true_exit_code'];warnings=h['actual_warning_count']if old else h['actual_warning_header_count']
 for k in ['actual_exit_code','actual_runner_exit_code']:assert type(a[k]) is int and a[k]==code
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
for h in d['old49_actual_native_history']:trial(h,True)
assert d['genuine_new_native_history'][-1]['source']['sha256']==sha(source)
prep=json.loads(add(d['actual_author_preparation']).read_bytes())
assert prep['status']=='passed' and type(prep['actual_exit_code']) is int and prep['actual_exit_code']==0 and prep['protection_errors']==[]
assert prep['actual_command']==['python3','/tmp/prepare-modules-chain53-dirac-association-request30-v1.py'] and prep['actual_workdir']==str(ROOT)
assert prep['helper_sha256_before']==prep['helper_sha256_after'] and prep['protected_inputs_sha256_before']==prep['protected_inputs_sha256_after']
for old,q in d['actual_author_preparation_original_byte_aliases'].items():assert sha(add(q))==sha(old)
assert sha(add(d['actual_author_preparation_original_byte_aliases'][prep['raw_log']]))==prep['raw_log_sha256']
assert all(d[k] is False for k in ['whole_Exercise7_5_requested','whole_Exercise7_5_approved','source_applied','canonical_pairs_executed','coverage_complete'])
extra=[];extra_aliases={}
for relative in [
 'verification/lean/.lake/packages/mathlib/Mathlib/Order/ConditionallyCompletePartialOrder/Basic.lean',
 'verification/lean/.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Dirac/Basic.lean']:
 p=ROOT/relative;h=sha(p);q=Path('/tmp/foundations-chain53-full-used-primary30-v1')/h/p.name;q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists():assert sha(q)==h
 else:
  with q.open('xb')as f:f.write(p.read_bytes())
 assert sha(p)==sha(q)==h;extra.append(ref(q));extra_aliases[str(p)]=ref(q);closed[str(q)]=h
reasons=[
 'The actual value set ranges over every admissible infinite state/action history with the actual chain recurrence and genuine discounted tsum return. The full Bellman inequalities, terminal geometric bound and attained feedback path establish IsGreatest, so csSup is that actual attained value rather than a supplied formula.',
 'The dual is explicitly the Bochner integral of the genuine history supremum under the Dirac law at actual physical cell2. The top measurable structure supports the actual integral_dirac theorem. Evaluating the derived Bellman value gives max(-7/4,-3/2-p/4) for every p>=0, with both threshold branches proved.',
 'The primal ranges over all actual safe infinite admissible histories from cell2. The walk path is genuinely viable at every time and attains -7/4; the safe Bellman inequalities upper-bound all such histories. Its attained supremum is therefore -7/4 without a safe optimizer premise.',
 'Combining the two derived actual values proves both inclusions of the full nonnegative dual zero-gap set as Ici1. At p=1 the safe and unsafe paths can tie; the closed dual-optimal ray does not assert safety of every penalized maximizer.'
]
finding={
 'status':'passed_independent_full_chain53_actual_Dirac2_four_associations_review',
 'reviewer':'/root/foundations_recovery28','review_finished_at_utc':datetime.now(timezone.utc).isoformat(),
 'request':ref(REQUEST),'source':ref(source),'public_theorem_names':names,'public_theorem_count':53,
 'public_definition_and_abbreviation_names':defs,'public_definition_and_abbreviation_count':27,
 'all53_entire_proof_bodies_and_actual_definitions_read':True,
 'all5_complete_selected_dependency_sources_read':d['selected_complete_dependency_sources'],
 'primary_API_byte_references':d['original49_primary_used_API_full_sources']+d['new_complete_primary_used_API_sources']+extra,
 'primary_read_scope':'Full used geometric majorization and infinite-sum/finite-prefix convergence bodies, actual finite telescoping proof chain, order-limit upper-bound and terminal squeeze domains read. Full actual Bochner integral_dirac, Dirac AE equality, IsGreatest.csSup_eq and surrounding measurable-singleton/conditionally-complete typeclass domains read. Complete selected TelescopingApplications, TelescopingModels, LessonSeries, Series and ModulesBook sources read. No unrelated primary theorem family is claimed reviewed.',
 'full_current_exercise7_5_and_original7_pending_claims_read':True,
 'current_full_context':d['current_entire_Exercise7_5_and_used_context'],
 'prior_full_sections3_5_read_and_original55_semantic_body_times_unchanged':ref(prior55),
 'full_original_chain_exercise7_4_and_reward_theorem2_context_read':d['original49_full_current_Exercise7_4_and_used_context'],
 'exact_entire_old49_proof_source_byte_prefix_preserved':ref(oldsource),
 'semantic_decisions':[{'declaration':n,'approved_in_exact_scope':True,'missing_clauses':[],'mathematical_reason':r}for n,r in zip(names[-4:],reasons)],
 'requested_actual_Exercise7_5_b_Dirac2_association_approved':True,
 'whole_exercise7_5_approved':False,'whole_exercise7_4_redecided':False,
 'original49_whole_semantic_peer_pending_and_separate':d['original49_whole_semantic_peer_pending_and_separate'],
 'requested_scope':d['requested_scope'],'domain_scope':d['domain_scope'],
 'explicit_limits':['Only the actual gamma1/2 physical Chain/Dirac2 association in Exercise7.5(b).','Cell7 is absorbed post-failure bookkeeping projected to physical cliff0, with the source once-event penalty; no new physical state is substituted.','The separate gamma.9 literal3.12 arithmetic correction remains prospective and no whole Exercise7.4 decision is inferred.','A closed zero-gap dual ray permits the threshold unsafe tie and does not make all its maximizers safe.'],
 'current_owner_rows_unchanged':True,'genuine_new_native_history':d['genuine_new_native_history'],
 'old49_actual_native_history':d['old49_actual_native_history'],'actual_author_preparation':d['actual_author_preparation'],
 'integrity_does_not_substitute_for_source_correspondence':True,
 'original_closed_byte_aliases':{**d['original_closed_byte_aliases'],**extra_aliases},
 'required_evidence_artifacts_sha256':closed,'errors':[],
 'compiler_parser_source_owner_canonical_publication_mutation':False,'prospective_evidence_outside_frozen29':True,'coverage_complete':False}
OUT.write_text(json.dumps(finding,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'findings':ref(OUT),'new_associations':4,'requested_associations_approved':True,'whole_exercise7_5':False,'errors':[]}))
