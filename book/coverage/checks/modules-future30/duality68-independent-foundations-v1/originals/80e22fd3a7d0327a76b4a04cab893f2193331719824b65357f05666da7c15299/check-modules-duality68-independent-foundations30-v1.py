from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re
ROOT=Path('/home/oxrexkevin/SafetyBased')
REQUEST=ROOT/'book/coverage/checks/modules-future30/duality68-association-supplement-v2/modules-duality68-exact-prefix-association-supplement-review-request30-v3.json'
OUT=Path('/tmp/modules-duality68-independent-foundations30-findings-v1.json')
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
assert sha(REQUEST)=='79acb6d803452e1728a5f259f2579a49dd4f86170ab100bcf210cef7379af087'
d=json.loads(REQUEST.read_bytes())
for n,h in d['required_evidence_artifacts_sha256'].items():add({'file':n,'sha256':h})
for old,q in d['original_closed_byte_aliases'].items():
 p=add(q);assert Path(old).is_file() and sha(old)==sha(p)
oldpeerpath=add(d['original55_independent_full_peer']);assert sha(oldpeerpath)=='155cf3e814e7a7f9651588323fdcf1614d089f45187f8be5053693eb19160316'
oldpeer=json.loads(oldpeerpath.read_bytes());assert oldpeer['errors']==[] and oldpeer['whole_exercise7_5_approved'] is False
for n,h in oldpeer['required_evidence_artifacts_sha256'].items():add({'file':n,'sha256':h})
oldrequest=add(d['original55_component_request']);assert sha(oldrequest)=='baab5e6bf29af3a4e306c3c6954bbd7b906926d755880bafb015d0bf058892c0'
assert d['original55_peer_body_and_times_unchanged'] is True
assert d['public_theorem_count']==68 and d['public_definition_count']==43 and d['private_clock_proof_count']==1
assert all(d[k] is False for k in ['whole_exercise_review_requested','source_number_reserved','source_applied','canonical_pairs_executed','whole_promotion_performed','coverage_complete'])
names=[];newnames=[];newdefs=[];histories=[]
for f,oldf,codes,warns in zip(d['families'],oldpeer['families'],[[0,0],[1,0]],[[1,1],[1,3]]):
 source=add(f['source']);body=source.read_text();old=add(f['old_final_source']);assert sha(old)==oldf['source']['sha256']
 assert body==f['full_source_body'] and body.startswith(old.read_text()) and f['entire_old_final_source_exact_byte_prefix'] is True
 assert not re.search(r'\b(sorry|admit|axiom)\b',body)
 ns=re.search(r'^namespace (\S+)',body,re.M).group(1)
 nsnames=[ns+'.'+n for n in re.findall(r'^theorem (\w+)',body,re.M)]
 nsdefs=[ns+'.'+n for n in re.findall(r'^def (\w+)',body,re.M)]
 assert nsnames==f['public_theorem_names'] and len(nsnames)==f['public_theorem_count']
 assert nsdefs==f['public_definition_names'] and len(nsdefs)==f['public_definition_count']
 assert nsnames[:oldf['public_theorem_count']]==oldf['public_theorem_names']
 append=body[len(old.read_text()):]
 nn=[ns+'.'+n for n in re.findall(r'^theorem (\w+)',append,re.M)]
 nd=[ns+'.'+n for n in re.findall(r'^def (\w+)',append,re.M)]
 assert nn==f['new_theorem_names'];newnames.extend(nn);newdefs.extend(nd);names.extend(nsnames)
 assert len(f['new_genuine_native_history'])==len(codes)
 for row,code,warn in zip(f['new_genuine_native_history'],codes,warns):
  a=json.loads(add(row['actual_native']).read_bytes());src=add(row['actual_source']);snap=add(row['actual_source_snapshot']);raw=add(row['actual_raw_log'])
  for k in ['actual_exit_code','actual_runner_exit_code']:assert type(a[k])is int and a[k]==code
  assert row['actual_exit_code']==code and a['actual_command']==['lake','env','lean',a['source']] and a['actual_workdir']==str(ROOT/'verification/lean')
  assert sha(src)==sha(snap)==a['source_sha256_before']==a['source_sha256_after']==a['source_snapshot_sha256']
  assert sha(raw)==a['raw_log_sha256'] and len(re.findall(r':\d+:\d+: warning:',raw.read_text()))==row['actual_warning_count']==warn
  for k,v in row['original_times'].items():assert a[k]==v
  assert a['protection_errors']==[] and a['source_unchanged']is True and row['original_body_and_times_untouched']is True
  assert [a[k]for k in ['protected_selected29_proof_sources','unchanged_current65_book_assets','unchanged_installed29_live_owners']]==[1197,31,5]
  histories.append(row)
 assert f['new_genuine_native_history'][-1]['actual_source']['sha256']==sha(source) and f['final_trial_is_kernel0']is True and f['final_warning_count']==warns[-1]
assert len(names)==len(set(names))==68 and len(newnames)==13 and len(newdefs)==13
prep=json.loads(add(d['actual_author_preparation']).read_bytes());assert type(prep['actual_exit_code'])is int and prep['actual_exit_code']==0 and prep['status']=='passed' and prep['protection_errors']==[]
assert prep['actual_command']==['python3','/tmp/prepare-modules-duality68-association-supplement30-v2.py'] and prep['actual_workdir']==str(ROOT)
assert prep['helper_sha256_before']==prep['helper_sha256_after'] and prep['protected_inputs_sha256_before']==prep['protected_inputs_sha256_after']
for old,q in d['actual_author_preparation_original_byte_aliases'].items():assert sha(add(q))==sha(old)
assert sha(add(d['actual_author_preparation_original_byte_aliases'][prep['raw_log']]))==prep['raw_log_sha256']
assert d['original_author_preparation1_true_schema_failure_preserved'] is True
add(d['original_association_request_v2'])
clocknew=d['families'][0]['new_theorem_names'];expectednew=d['families'][1]['new_theorem_names']
groups_names=[clocknew[:9],clocknew[9:],expectednew[:2],expectednew[2:]]
assert sum(map(len,groups_names))==13
why=[
 'All stationary-clock definitions use the actual nextState, rather than supplying a shifted-path equality. Induction proves surviving original time equals elapsed time and the actual stationary feedback trajectory equals the shifted original path. For each initial clock n, first-jump HasSum and safe-or-firstjump classification derive the entire infinite reward/risk. A single threshold policy k achieves the exact maximum for every surviving initial clock at each actual lambda_k=1-2^-k: n<=k gives a completed square; n>k gives the true monotone endpoint argument. The actual eta1 search at start0 still follows the original lambda recurrence and never stops. The arbitrary-penalty common-attainment claim is not proved here.',
 'Viability is actually defined by existence of a stationary feedback avoiding none at every time. Never-jump feedback constructs safety from every some n. Starting at none is already failed at time0 and stays failed, so exactly the surviving clocks form the viability kernel and every unviable start has uniform failure time0. This closes the requested postexit source Assumption1 association without assuming a viability set or a failure bound as a premise.',
 'The actual CMDP risk<=0 policy subtype and the actual zero-risk subtype have equal reward ranges because risk is nonnegative; the ciSup identity follows by explicit two-way range witnesses even if either subtype is empty. Genuine risk integrability and nonnegativity make expected risk<=0 equivalent to expected risk=0, hence to AE risk=0 by the original fully-reviewed zero-integral theorem. The source zero-budget primal/feasibility identification is derived, not assumed.',
 'A true flat one-action zero-reward/zero-cost family gives exact maximizers at every multiplier. Its actual positive-budget projected map has 0 as a fixed point for every positive step, and the actual constant process has zero increments. Exact maximizers also satisfy every nonnegative inexact tolerance; zero costs have deterministic zero samples. This is a valid nonoscillation countermodel to an unqualified universal sentence. It proves neither oscillation in deep RL nor a statistical sampled optimizer theorem. The narrow can-oscillate wording proposal is separate and remains unnumbered/unapplied.'
]
finding={
 'status':'passed_independent_full_duality68_exact_prefix_association_component_semantic_review','reviewer':'/root/foundations_recovery28','review_finished_at_utc':datetime.now(timezone.utc).isoformat(),
 'request':ref(REQUEST),'original55_request':ref(oldrequest),'original55_full_semantic_peer':ref(oldpeerpath),
 'original55_entire_bodies_and_original_peer_decisions_body_times_retained_without_redecision':True,
 'families':d['families'],'all13_new_entire_proof_bodies_and13_actual_definitions_read':True,
 'all68_entire_proof_bodies_read_with_exact_prior55_full_read':True,'entire_current_exercise7_5_and_original_seven_pending_claims_read':True,
 'actual_source_model_A1_uniform_attainment_pointwise_SVF_zero_budget_correspondence_read':True,
 'semantic_scope_determined_by_full_mathematical_read_not_integrity':True,
 'component_decisions':[dict(g,public_theorem_names=ns,approved_in_exact_scope=True,missing_clauses=[],mathematical_reason=w)for g,ns,w in zip(d['component_review_scopes'],groups_names,why)],
 'whole_literal_decisions':[{'inventory_key':'viability.html::exercise-19','whole_literal_approved':False,'remaining_clauses':d['explicit_remaining_whole_exercise_associations']}],
 'whole_exercise7_5_approved':False,'current_claims_not_promoted':True,
 'all4_new_actual_native_bodies_sources_snapshots_raw_logs_original_times_preserved':True,
 'all12_original55_actual_histories_and_independent_reader1_failure_original_body_times_retained':True,
 'new_genuine_native_histories':histories,'original_closed_byte_aliases':d['original_closed_byte_aliases'],
 'required_evidence_artifacts_sha256':closed,'errors':[],
 'compiler_parser_source_owner_canonical_publication_mutation':False,'prospective_evidence_outside_frozen29':True,'coverage_complete':False}
OUT.write_text(json.dumps(finding,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'findings':ref(OUT),'new_public_count':13,'exact_prefix_public_count':55,'new_actual_histories':4,'whole_exercise7_5':False,'errors':[]}))
