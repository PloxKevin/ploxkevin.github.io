from pathlib import Path
from datetime import datetime, timezone
import json, hashlib, re, sys
ROOT=Path('/home/oxrexkevin/SafetyBased')
REQUEST=ROOT/'book/coverage/checks/modules-future30/duality55-components-v1/modules-duality55-full-source-current-literal-component-review-request30-v2.json'
OUT=Path('/tmp/modules-duality55-independent-foundations30-findings-v2.json')
assert not OUT.exists()
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p): return {'file':str(p),'sha256':sha(p),'bytes':Path(p).stat().st_size}
closed={str(REQUEST):sha(REQUEST),str(Path(__file__)):sha(__file__)}
def add(q):
 p=Path(q['file']); p=p if p.is_absolute() else ROOT/p
 assert p.is_file() and sha(p)==q['sha256']
 if 'bytes' in q: assert p.stat().st_size==q['bytes']
 if p.is_relative_to(ROOT): assert p.resolve().is_relative_to(ROOT)
 closed[str(p)]=q['sha256']; return p
assert sha(REQUEST)=='baab5e6bf29af3a4e306c3c6954bbd7b906926d755880bafb015d0bf058892c0'
d=json.loads(REQUEST.read_bytes())
for n,h in d['required_evidence_artifacts_sha256'].items(): add({'file':n,'sha256':h})
for original,q in d['original_closed_byte_aliases'].items():
 p=add(q); assert Path(original).is_file() and sha(original)==sha(p)
for original,q in d['actual_author_preparation_original_byte_aliases'].items():
 p=add(q); assert Path(original).is_file() and sha(original)==sha(p)
assert d['public_theorem_count']==55 and d['public_definition_count']==30 and d['private_clock_proof_count']==1
assert d['whole_exercise_current_pending'] is True
assert all(d[k] is False for k in ['whole_exercise_review_requested','component_approval_by_author','source_number_reserved','source_applied','canonical_pairs_executed','whole_promotion_performed','coverage_complete'])
all_names=[]; families=[]
expected_codes=[[1,0,1,0],[1,1,0,1,0,1,0,0]]
expected_warnings=[[1,1,4,1],[3,0,0,4,1,0,0,0]]
for f,codes,warnings in zip(d['families'],expected_codes,expected_warnings):
 p=add(f['source']); body=p.read_text(); assert body==f['full_source_body']
 assert not re.search(r'\b(sorry|admit|axiom)\b',body)
 ns=re.search(r'^namespace (\S+)',body,re.M).group(1)
 names=[ns+'.'+n for n in re.findall(r'^theorem (\w+)',body,re.M)]
 defs=[ns+'.'+n for n in re.findall(r'^def (\w+)',body,re.M)]
 assert names==f['public_theorem_names'] and len(names)==f['public_theorem_count']
 assert defs==f['public_definition_names'] and len(defs)==f['public_definition_count']
 assert len(re.findall(r'^private (?:theorem|lemma) ',body,re.M))==(1 if len(names)==27 else 0)
 assert f['final_trial_is_kernel0'] is True and f['entire_earlier_final_source_byte_prefix_asserted'] is False
 assert len(f['genuine_native_history'])==len(codes)
 for row,code,warning in zip(f['genuine_native_history'],codes,warnings):
  a=json.loads(add(row['actual_native']).read_bytes())
  for k in ['actual_exit_code','actual_runner_exit_code']: assert type(a[k]) is int and a[k]==code
  assert row['actual_exit_code']==code and a['protection_errors']==[] and a['source_unchanged'] is True
  assert a['actual_command']==['lake','env','lean',a['source']] and a['actual_workdir']==str(ROOT/'verification/lean')
  src=add(row['actual_source']); snapshot=add(row['actual_source_snapshot']); log=add(row['actual_raw_log'])
  assert sha(src)==sha(snapshot)==a['source_sha256_before']==a['source_sha256_after']==a['source_snapshot_sha256']
  assert sha(log)==a['raw_log_sha256']
  assert len(re.findall(r':\d+:\d+: warning:',log.read_text()))==row['actual_warning_count']==warning
  assert row['original_body_and_times_untouched'] is True
  for k,v in row['original_times'].items(): assert a[k]==v
  assert [a[k] for k in ['protected_selected29_proof_sources','unchanged_current65_book_assets','unchanged_installed29_live_owners']]==[1197,31,5]
 assert f['genuine_native_history'][-1]['actual_source']['sha256']==sha(p)
 assert f['final_warning_count']==warnings[-1]
 all_names.extend(names); families.append(f)
assert len(all_names)==len(set(all_names))==55
ctx=json.loads(add(d['current_full_context']).read_bytes())
page=add(d['current_page_original_byte_alias']); lines=page.read_text().splitlines(keepends=True)
for k,a,b in [('full_exercise7_5_and_answer_context_lines941_957',941,957),('full_source_Section3_penalty_setup_lines251_307',251,307),('full_source_Section4_theorem_context_lines308_479',308,479),('full_source_Section5_and_duality_context_lines480_581',480,581)]:
 assert ctx[k]==''.join(lines[a-1:b])
assert page.read_bytes()==(ROOT/'SafeLearning/viability.html').read_bytes()
inv=json.loads(add(d['current_inventory']).read_bytes()); owner=json.loads(add(d['original_owner29_candidate']).read_bytes())
assert ctx['entire_current_exercise_inventory_row']==next(x for x in inv['exercises'] if x['key']=='viability.html::exercise-19')
assert ctx['entire_original_pending_exercise_owner_row']==next(x for x in owner['exercises'] if x.get('inventory_key')=='viability.html::exercise-19')
assert all(x['status']=='pending' for x in ctx['entire_original_pending_exercise_owner_row']['claims'])
for q in d['selected_complete_dependency_sources']: add(q)
for q in d['primary_used_API_full_sources']: add(q['exact_physical_byte_alias'])
offline=[]
for q in d['actual_primary_HTTP_receipts']:
 receipt=json.loads(add(q).read_bytes()); assert type(receipt['actual_http_status']) is int and receipt['actual_http_status']==200
 p=Path(receipt['original_body_tmp_path_historical_metadata']); assert p.is_file() and sha(p)==receipt['body_sha256'] and p.stat().st_size==receipt['body_bytes']
 offline.append({'url':receipt['url'],'body_sha256':sha(p),'body_bytes':p.stat().st_size,'historical_TMP_path':str(p),'full_original_body_kept_TMP_offline_only':True,'receipt':q})
assert d['remote_full_primary_bodies_kept_TMP_offline_only'] is True
prep=json.loads(add(d['actual_author_preparation']).read_bytes()); assert type(prep['actual_exit_code']) is int and prep['actual_exit_code']==0 and prep['status']=='passed' and prep['protection_errors']==[]
assert prep['actual_command']==['python3','/tmp/prepare-modules-duality55-component-request30-v1.py'] and prep['actual_workdir']==str(ROOT)
assert prep['helper_sha256_before']==prep['helper_sha256_after'] and prep['protected_inputs_sha256_before']==prep['protected_inputs_sha256_after']
assert sha(add(d['actual_author_preparation_original_byte_aliases'][prep['raw_log']]))==prep['raw_log_sha256']
add(d['original_component_request_v1'])
for p in [Path('/tmp/check-modules-duality55-independent-foundations30-v1.py'),Path('/tmp/run-modules-duality55-independent-foundations30-v1.py'),Path('/tmp/modules-duality55-independent-foundations30-actual-v1.json'),Path('/tmp/modules-duality55-independent-foundations30-actual-v1.log')]: closed[str(p)]=sha(p)
extra=[]
for n in ['MeasureTheory/Function/L1Space/Integrable.lean','Algebra/Order/Archimedean/Defs.lean']:
 p=ROOT/'verification/lean/.lake/packages/mathlib/Mathlib'/n
 assert p.is_file(); closed[str(p)]=sha(p); extra.append(ref(p))
clock=families[0]['public_theorem_names']; expect=families[1]['public_theorem_names']
reason=[
 'Real ciSup definitions use nonempty bounded primitive reward/unit-risk images. Weak duality, antitone, convexity and one-Lipschitz bounds follow pointwise then by genuine supremum inequalities. A common safe optimum and attained/all-safe penalized maxima for nonnegative multipliers derive the plateau; continuity and the attained infimum of its closed nonempty level set derive the closed optimal ray. No desired ray or general strong-duality conclusion is supplied.',
 'Measurability and bounded reward/unit risk derive all Bochner integrability. A common controller attaining pointwise values derives the sup-integral identity; a common safe optimum derives the expected primal identity. Nonnegative risk integrates to zero exactly when AE zero. Actual pointwise SVF makes the nonnegative penalized gap have zero integral for every expected global maximizer, so AE safety follows from its genuine pointwise equality, not an expected-safety premise.',
 'The projected zero-budget step is the actual max0 update; its nonnegative cost gives strict increase iff risk positive and termination iff AE safe. A genuinely feasible controller and actual zero duality gap derive complementarity, global Lagrangian saddle and primal optimality. This conditional statement does not establish general gap or multiplier existence. The printed p10 counterexample has three actual controllers and explicitly proves ordinary Lagrange multiplier lambda=p/10; its infeasible and suboptimal ties are exact.',
 'Actual recursive paths, bounded physical rewards, discounted first-entry risk and infinite HasSum returns are derived for every history. The completed square establishes the delayed controller as a genuine global maximizer at lambda_k=1-2^-k. Its actual positive risk makes the eta1 projected update equal lambda_(k+1), never stopping or reaching 1 despite all multipliers above 1 having only safe maximizers. The source Assumption1/common stationary attainment association is explicitly still pending in this original27 packet.',
 'A genuine no-repeat argument makes every finite feedback first failure earlier than card X. The actual discounted first-entry series, positive supported initial-law minimum mass, and positive expected risk derive a uniform mass*gamma^card lower bound. Constant positive-step updates and a safe-above-threshold premise imply an Archimedean finite stop. No lower risk bound or finite stop conclusion is assumed.',
 'For the displayed max(-7/4,-3/2-p/4), direct exact arithmetic establishes nonnegative optimal ray [1,infinity), tie at1, strictly dominated unsafe branch above1, and comparison with15/2. This is an algebra component; actual Chain49 dynamics/Bellman attainment/delta2 association is expressly pending.'
]
group_names=[expect[:10],expect[10:18],expect[18:25]+expect[27:],clock[:14],clock[14:],expect[25:27]]
assert set(n for ns in group_names for n in ns)==set(all_names) and sum(map(len,group_names))==55
groups=[dict(s,approved_in_exact_scope=True,missing_clauses=[],public_theorem_names=ns,mathematical_reason=why) for s,ns,why in zip(d['component_review_scopes'],group_names,reason)]
finding={
 'status':'passed_independent_full_dual55_component_semantic_review','reviewer':'/root/foundations_recovery28','review_finished_at_utc':datetime.now(timezone.utc).isoformat(),
 'request':ref(REQUEST),'families':families,'all55_entire_proof_bodies_and30_definitions_and_one_private_proof_read':True,
 'entire_current_exercise7_5_and_original_seven_pending_claims_read':True,'full_used_Section3_4_model_SVF_A1_Proposition1_Theorem2_context_read':True,
 'all_six_complete_selected_sources_read':True,'complete_used_primary_API_proof_bodies_and_typeclass_domains_read':True,
 'actual_remote_primary_used_scope':d['primary_used_scope'],'actual_primary_bodies_checked_and_kept_offline':offline,
 'entire_remote_papers_read_claimed':False,'all_context_window_byte_hashes_verified_not_a_claim_every_unrelated_Section5_paragraph_mathematically_audited':True,
 'semantic_scope_determined_by_full_mathematical_read_not_integrity':True,'component_decisions':groups,
 'whole_literal_decisions':[{'inventory_key':'viability.html::exercise-19','whole_literal_approved':False,'remaining_clauses':d['explicit_remaining_whole_exercise_associations']}],
 'whole_exercise7_5_approved':False,'current_seven_original_pending_claims_not_promoted':True,
 'source_assumption_correspondence':{
  'uniform_attainment':'The generic expected dual identity assumes one actual pointwise maximizing controller, as the source explicitly does. It does not prove finite deterministic dynamic programming supplies it.',
  'pointwise_SVF':'All penalized pointwise maximizers on the viable initial domain are safe; the expected-maximizer AE statement is genuinely derived via nonnegative gap integration.',
  'zero_gap_saddle':'The saddle statement is explicitly conditional on actual zero gap and a feasible controller. Bibliographic general finite-CMDP LP strong duality remains pending.',
  'clock':'All actual infinite-return/update/global-max statements are proved in the original clock27 model; source viability-kernel/uniform-postexit/common stationary-all-start association requires the separately forthcoming source extension.',
  'finite_termination':'The input is an actual finite deterministic feedback map, gamma in(0,1), supported finite initial law and constant positive step. Finite first failure/lower risk/stopping are derived.',
  'positive_budget_inexact_final_sentence':'No universal oscillation theorem is proved or approved. Its literal editorial/empirical scope or qualification remains explicit.'},
 'all12_true_native_failures_and_passes_sources_snapshots_raw_logs_original_times_preserved':True,
 'original_closed_byte_aliases':d['original_closed_byte_aliases'],'additional_complete_used_primary_API_sources':extra,
 'required_evidence_artifacts_sha256':closed,'errors':[],
 'original_reader1_schema_failure':{'reason':'Reader1 used owner claims at the top level; the native owner schema uses exercises. NEW2 repairs only that field lookup. No proof, source, author or native-history change.','checker':ref(Path('/tmp/check-modules-duality55-independent-foundations30-v1.py')),'actual':ref(Path('/tmp/modules-duality55-independent-foundations30-actual-v1.json')),'raw_log':ref(Path('/tmp/modules-duality55-independent-foundations30-actual-v1.log'))},
 'compiler_parser_source_owner_canonical_publication_mutation':False,'prospective_evidence_outside_frozen29':True,'coverage_complete':False}
OUT.write_text(json.dumps(finding,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'findings':ref(OUT),'component_public_count':55,'actual_history_count':12,'whole_exercise7_5':False,'errors':[]}))
