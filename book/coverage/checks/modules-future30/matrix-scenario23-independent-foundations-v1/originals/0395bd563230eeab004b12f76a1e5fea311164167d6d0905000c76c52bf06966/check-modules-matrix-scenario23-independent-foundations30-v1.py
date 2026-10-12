from pathlib import Path
from datetime import datetime, timezone
from fractions import Fraction
from math import comb
import json, hashlib, re, sys
sys.dont_write_bytecode=True
ROOT=Path('/home/oxrexkevin/SafetyBased')
REQUEST=ROOT/'book/coverage/checks/modules-future30/matrix-scenario23-full-components-v3/modules-matrix-scenario23-full-source-current-literals-component-independent-review-request30-v3.json'
OUT=Path('/tmp/modules-matrix-scenario23-independent-foundations30-findings-v1.json')
EXTRA=Path('/tmp/modules-matrix-scenario23-independent-foundations30-extra-primary-v1')
assert not OUT.exists() and not EXTRA.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):return {'file':str(p),'sha256':sha(p),'bytes':Path(p).stat().st_size}
def path(q):
 p=Path(q['file']);return p if p.is_absolute() else ROOT/p
closed={str(REQUEST):sha(REQUEST),str(Path(__file__)):sha(__file__)}
def add(q):
 p=path(q);assert p.is_file() and sha(p)==q['sha256']
 if 'bytes' in q:assert p.stat().st_size==q['bytes']
 if p.is_relative_to(ROOT):assert not p.is_symlink() and p.resolve().is_relative_to(ROOT)
 closed[str(p)]=q['sha256'];return p
assert sha(REQUEST)=='87ec7cb8f6f36fe6499026e44ef4584b5041534d326cb3e9499a97fd5e58d0db'
d=json.loads(REQUEST.read_bytes())
for n,h in d['required_evidence_artifacts_sha256'].items():add({'file':n,'sha256':h})
for n,q in d['original_closed_byte_aliases'].items():
 add(q);p=Path(n);p=p if p.is_absolute() else ROOT/p
 assert sha(p)==q['sha256']
source=add(d['source']);body=source.read_text()
sys.path.insert(0,str(ROOT/'book/coverage'));import lean_names
closed[str(ROOT/'book/coverage/lean_names.py')]=sha(ROOT/'book/coverage/lean_names.py')
assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by|run_elab|ofReduceBool|sorryAx)\b',lean_names.without_comments(body))
decls=lean_names.declarations(body);names=[r['name'] for r in decls if r['kind'] in ['theorem','lemma']];other=[r for r in decls if r['kind'] not in ['theorem','lemma']]
assert len(names)==d['public_theorem_count']==23 and names==d['public_theorem_names']
assert len(decls)==d['public_declaration_count']==37 and other==d['other_public_declarations'] and len(other)==14
assert d['genuine_native_codes']==[1,0,1,1,1,0] and d['genuine_warning_headers']==[0,0,13,9,10,11]
for row,code,warnings in zip(d['genuine_original_native_history'],[1,0,1,1,1,0],[0,0,13,9,10,11]):
 a=json.loads(add(row['actual_native']).read_bytes());raw=add(row['raw_log'])
 for k in ['actual_exit_code','actual_runner_exit_code']:assert type(a[k]) is int and a[k]==code
 assert row['actual_exit_code']==code and a['status']==('passed_actual_tmp_lean_only' if code==0 else 'failed_actual_tmp_lean_or_protection')
 assert a['actual_command']==['lake','env','lean',a['source']] and a['actual_workdir']==str(ROOT/'verification/lean')
 assert a['protection_errors']==[] and a['source_unchanged'] is True
 assert sha(add(row['source']))==sha(add(row['source_snapshot']))==a['source_sha256_before']==a['source_sha256_after']==a['source_snapshot_sha256']
 assert sha(raw)==a['raw_log_sha256']
 assert len(re.findall(r'^.*:\d+:\d+: warning:',raw.read_text(),re.M))==warnings==row['actual_warning_headers']
 assert row['original_actual_times']=={k:a[k] for k in ['started_at_utc','finished_at_utc','elapsed_seconds']}
 assert [a[k] for k in ['protected_selected29_proof_sources','unchanged_current65_book_assets','unchanged_installed29_live_owners']]==[1197,31,5]
 for k in ['original_actual_runner','actual_source65_installed29_context']:
  q=d['original_closed_byte_aliases'][a[k]['file']];assert q['sha256']==a[k]['sha256'];add(q)
 for k in ['actual_installed29_selection','actual_frozen29_original_audit']:add(a[k])
 assert all(sha(ROOT/n)==h for n,h in a['installed29_owner_sha256'].items())
assert d['genuine_original_native_history'][-1]['source']['sha256']==sha(source)
old=add(d['exact_old11_entire_byte_prefix']);assert body.encode().startswith(old.read_bytes()) and old.stat().st_size==d['exact_old11_prefix_length_bytes']==8569
assert d['exact_old11_prefix_includes_closing_namespace_end'] is True
assert len(d['uncompiled_historical_sources'])==1 and all(r['compiled'] is False for r in d['uncompiled_historical_sources'])
for r in d['uncompiled_historical_sources']:add(r['source'])
inv=json.loads(add(d['current_inventory']).read_bytes());owner=json.loads(add(d['immutable_original_owner29']).read_bytes())
assert path(d['current_inventory']).read_bytes()==(ROOT/'book/coverage/inventory.json').read_bytes()
assert path(d['immutable_original_owner29']).read_bytes()==(ROOT/'book/coverage/modules.json').read_bytes()
assert d['entire_current_exercise']==next(r for r in inv['exercises'] if r['key']=='verification.html::exercise-19')
assert d['entire_original_owned_exercise_row']==next(r for r in owner['exercises'] if r['inventory_key']=='verification.html::exercise-19')
for u in d['entire_current_material_literals']:assert u==next(r for r in inv['material_source_units'] if r['key']==u['key'])
keys={u['key'] for u in d['entire_current_material_literals']}
assert d['entire_original_material_rows']==[r for r in owner['material_claims'] if any(k in keys for k in r['source_unit_keys'])]
page=add(d['entire_current_page_original_byte_alias']);assert page.read_bytes()==(ROOT/'SafeLearning/verification.html').read_bytes()
lines=page.read_text().splitlines(keepends=True)
for k in ['entire_used_scenario_section_context','entire_exercise_context']:
 c=d[k];assert c['keepends_exact_full_html']==''.join(lines[c['start_line_inclusive']-1:c['end_line_exclusive']-1])
for row in d['complete_selected_sources']:
 assert add(row['source']).read_bytes()==add(row['entire_source']).read_bytes()
for row in d['entire_physical_primary_API_sources']:add(row['entire_physical_API_source'])
extra=[]
base=ROOT/'verification/lean/.lake/packages/mathlib/Mathlib'
for p in [base/'LinearAlgebra/Matrix/Charpoly/Eigs.lean',base/'LinearAlgebra/Matrix/Trace.lean',base/'Basic/Complex/Basic.lean']:
 q=EXTRA/sha(p)/p.name;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(p.read_bytes());extra.append({'original_historical_path':str(p),'entire_physical_source':ref(q)});add(ref(q))
author=Path('/tmp/modules-matrix-scenario23-full-components30-preparation-actual-v3.json');a=json.loads(author.read_bytes())
assert a['status']=='passed' and type(a['actual_exit_code']) is int and a['actual_exit_code']==0 and a['protection_errors']==[]
assert a['helper_sha256_before']==a['helper_sha256_after'] and sha(a['raw_log'])==a['raw_log_sha256']
for p in [author,Path(a['raw_log']),Path(a['actual_command'][1])]:add(ref(p))
for k in ['source_ordinal_reserved','source_applied','whole_promotion_performed','canonical_pairs_executed','whole_current_exercise_requested','compiler_or_parser_started_by_preparation','coverage_complete']:assert d[k] is False
assert d['whole_current_exercise_expected_pending'] is True and len(d['exact_components_requested'])==4
prior=ROOT/'book/coverage/checks/modules-future30/scenario33-independent-foundations-v1/modules-scenario33-full-source-current-literal-components-independent-foundations30-closed-peer-v1.json'
assert sha(prior)=='232d47e4ffdb31cd3412ab707952b5db92b03ddb5fff5ba9b9f84909b905033f';add(ref(prior))
pd=json.loads(prior.read_bytes());assert pd['complete_selected_sources']==d['complete_selected_sources']
# Independent rational size check of the robust trace contradiction.
L=Fraction(64,3);worst_pairing_loss=5+Fraction(2,64)*L
assert worst_pairing_loss==Fraction(17,3) and 11-worst_pairing_loss==Fraction(16,3)>4
specs=[
 (0,10,'Actual robust nonempty open five-model common-gain obstruction','All ten full bodies are read. Multiset root-sum norm is bounded by root cardinality, actual complex algebraic closure/charpoly trace identity and degree four give |trace C|<=4 for genuine root-wise Schur stability. The exact rank-one feedback trace and uniform B perturbation error are derived. Four near-e_i small-trace models imply gain L1<=64/3; the fifth trace>11 then exceeds4 even after the worst17/3 pairing loss. The explicit open event has a nonempty witness with four zero-A plants and one3I plant. This is an adaptive common-gain obstruction for five models, with no claimed pair or controllability result.'),
 (11,18,'Actual positive discrete Lyapunov criterion and no common certificate','All seven energy/Lyapunov full bodies are read. Real and imaginary quadratic energies add, and real PD is positive on every nonzero complex vector. Energy scales by squared eigenvalue norm, while P-C^T P C is the exact energy drop. Actual spectrum/charpoly root correspondence supplies nonzero eigenvectors, so two genuine positive forms derive strict norm<1. The no-common-positive-certificate conclusion composes the five-model obstruction. The paper actual block LMI is not supplied or silently identified with these positive-drop hypotheses.'),
 (18,22,'Actual nondegenerate affine Gaussian20-coordinate probability and full support','All four full bodies are read. Gaussian variance1 has strictly positive density and volume is absolutely continuous with respect to it; therefore it is positive on each nonempty open. Finite product law inherits this. A genuine continuous linear equivalence and affine translation followed by the actual continuous surjective coordinate-to-A/B map carry positivity to the plant law. The exact finite-product/map probability instances apply; continuity supplies genuine measurable pushforward, not a totalized nonmeasurable fallback. This explicit law is separate from GP posterior matrix-normal covariance semantics.'),
 (10,11,'Actual positive open-witness probability of common-gain failure','The actual independent five-sample finite product measure gives positive mass to the nonempty OPEN obstruction, which is pointwise contained in common-gain failure; monotonicity proves the displayed positive measure. The full existential failure event is not newly proved measurable. A positive measurable open witness is enough for the stated obstruction; no quantifier exchange from fixed-gain probability is used.'),
 (22,23,'Actual affine Gaussian positive open-witness probability of common-Lyapunov failure','The exact full final body installs the genuine Gaussian full-support/probability instances and transfers the positive OPEN event through pointwise no-common-certificate inclusion. All five models use one common K and P. The positive measurable witness is explicit, with no claim that the GP posterior is this law or that every scenario program/kernel/certificate property follows.')]
groups=[{'scope':label,'public_theorem_names':names[lo:hi],'approved_in_exact_scope':True,'missing_clauses':[],'mathematical_reason':reason} for lo,hi,label,reason in specs]
assert sorted(n for g in groups for n in g['public_theorem_names'])==sorted(names)
finding={'status':'passed_independent_matrix_scenario23_full_source_current_literal_components_semantic_review','reviewer':'/root/foundations_recovery28','review_finished_at_utc':datetime.now(timezone.utc).isoformat(),'request':ref(REQUEST),'source':ref(source),'public_theorem_count':23,'public_declaration_count':37,'public_theorem_names':names,'other_public_declarations':other,'all23_entire_bodies_and_all14_other_public_declarations_read':True,'all_six_complete_selected_sources_and_used_primary_proof_chains_read':True,'complete_current_exercise_five_literals_and_contexts_read':True,'component_decisions':groups,'independent_trace_contradiction_rational_bounds':{'gain_L1_upper':'64/3','maximal_pairing_loss':'17/3','last_trace_lower':'strictly greater than16/3>4'},'exact_passed_old11_full_byte_prefix':d['exact_old11_entire_byte_prefix'],'prior_Scenario33_full_semantic_peer_exact_body_time_ref':ref(prior),'original_author_preparation_failures':[d['genuine_original_author_preparation_failure'],d['genuine_original_author_preparation_failure2']],'complete_selected_sources':d['complete_selected_sources'],'primary_physical_sources':d['entire_physical_primary_API_sources'],'additional_used_primary_physical_sources':extra,'genuine_original_native_history':d['genuine_original_native_history'],'genuine_native_codes':[1,0,1,1,1,0],'genuine_warning_header_counts':[0,0,13,9,10,11],'uncompiled_historical_sources':d['uncompiled_historical_sources'],'original_author_preparation_actual':ref(author),'all_original_sources_snapshots_logs_failures_and_native_body_times_preserved':True,'whole_current_Exercise19_or_any_material_literal_approved':False,'whole_remaining_associations':d['explicit_remaining_whole_associations'],'paper_full_factual_attribution_or_general_scenario_design_theorem_approved':False,'matrix_pair_or_GP_posterior_or_actual_paper_matrix_LMI_bridge_approved':False,'full_failure_event_measurability_newly_derived':False,'positive_measurable_open_failure_witness_explicit':True,'semantic_decisions_from_full_math_read_not_integrity':True,'compiler_or_parser_launched_by_reviewer':False,'canonical_or_source_or_owner_or_publication_mutation':False,'source_ordinal_reserved':False,'source_applied':False,'coverage_complete':False,'prospective_postfreeze_evidence_not_part_of_frozen29':True,'required_evidence_artifacts_sha256':closed,'original_closed_byte_aliases':d['original_closed_byte_aliases'],'errors':[]}
OUT.write_text(json.dumps(finding,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'findings':ref(OUT),'components':23,'groups':5,'whole_decision':False,'errors':[]}))
