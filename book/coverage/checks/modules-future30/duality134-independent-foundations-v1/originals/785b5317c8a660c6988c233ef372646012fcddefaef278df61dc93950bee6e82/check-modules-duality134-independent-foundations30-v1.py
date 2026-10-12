from pathlib import Path
from datetime import datetime,timezone
import sys,hashlib,json,re
sys.dont_write_bytecode=True
ROOT=Path('/home/oxrexkevin/SafetyBased')
REQUEST=ROOT/'book/coverage/checks/modules-future30/duality134-whole-composition-v2/modules-duality134-full-Exercise7_5-six-units-prospective-composition-review-request30-v3.json'
OUT=Path('/tmp/modules-duality134-independent-foundations30-findings-v1.json');assert not OUT.exists()
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):return {'file':str(p),'sha256':sha(p),'bytes':Path(p).stat().st_size}
closed={str(REQUEST):sha(REQUEST),str(Path(__file__)):sha(__file__)}
def add(q):
 p=Path(q['file']);p=p if p.is_absolute()else ROOT/p
 assert p.is_file()and sha(p)==q['sha256']
 if 'bytes'in q:assert p.stat().st_size==q['bytes']
 if p.is_relative_to(ROOT):assert p.resolve().is_relative_to(ROOT)
 closed[str(p)]=sha(p);return p
assert sha(REQUEST)=='6246f9f2e528ecfc628e8092b2ffcb6f058e4eee2e3cbed842724fb570feb341'
d=json.loads(REQUEST.read_bytes())
for n,h in d['required_evidence_artifacts_sha256'].items():add({'file':n,'sha256':h})
for n,q in d['original_closed_byte_aliases'].items():
 p=add(q);assert Path(n).is_file()and sha(n)==sha(p)
allnames=[];natives=[]
for family in d['families']:
 p=add(family['source']);body=p.read_text()
 assert not re.search(r'\b(?:sorry|admit|native_decide|implemented_by)\b',body)
 assert not re.search(r'^\s*(?:axiom|unsafe)\s',body,re.M)
 namespace=re.findall(r'^namespace ([\w.]+)',body,re.M)[0]
 names=[namespace+'.'+n for n in re.findall(r'^theorem (\w+)',body,re.M)]
 assert names==family['public_theorem_names']and len(names)==family['public_theorem_count'];allnames+=names
 original=json.loads(add(family['exact_full_body_in_original_request']).read_bytes())
 if family['id']!='actual_expected_duality31':assert original['full_source_body']==body
 else:
  original_family=next(f for f in original['families']if f['public_theorem_count']==31)
  assert add(original_family['source']).read_bytes()==p.read_bytes()
 a=json.loads(add(family['actual_best_trial']).read_bytes())
 for k in ['actual_exit_code','actual_runner_exit_code']:assert type(a[k])is int and a[k]==0
 assert a['actual_command']==['lake','env','lean',a['source']]and a['actual_workdir']==str(ROOT/'verification/lean')
 assert sha(p)==a['source_sha256_before']==a['source_sha256_after']==a['source_snapshot_sha256']==sha(a['source_snapshot'])
 assert a['source_unchanged']is True and a['protection_errors']==[]
 assert [a[k]for k in ['protected_selected29_proof_sources','unchanged_current65_book_assets','unchanged_installed29_live_owners']]==[1197,31,5]
 assert a['original_actual_runner']['sha256']=='5eca9a664c2c81d8c67c412a20be5782f6e84ec124a193233a5a2700e602575c'
 assert a['actual_source65_installed29_context']['sha256']=='ed8ca5f56d1f101b1a5898e367162bda47bd6b0845312ce3ba2dda4d58938ae2'
 raw=add({'file':a['raw_log'],'sha256':a['raw_log_sha256']});add({'file':a['source_snapshot'],'sha256':a['source_snapshot_sha256']})
 natives.append({'family':family['id'],'native':family['actual_best_trial'],'true_exit_code':0,'exact_source_sha256':sha(p),'emitted_warning_headers':len(re.findall(r'^.*:\d+:\d+: warning:',raw.read_text(),re.M)),'original_times':{k:a[k]for k in ['started_at_utc','finished_at_utc','elapsed_seconds']}})
assert len(allnames)==len(set(allnames))==d['unique_public_theorem_count']==134
priorrefs=d['original_independent_full_source_and_component_peers']
for label,q in priorrefs.items():
 prior=json.loads(add(q).read_bytes());assert prior['errors']==[]
 assert 'failed'not in prior['status']
for q in [d['original55_full_scope_request'],d['original68_full_scope_request'],d['bounded_Altman_finite_discounted_CMDP_primary_facts'],d['narrow_only_exact_can_oscillate_proposal']]:add(q)
context=json.loads(add(d['current_full_Section3_4_setup_and_SVF_and_exercise_context']).read_bytes())
inv=json.loads((ROOT/'book/coverage/inventory.json').read_bytes());owner=json.loads((ROOT/'book/coverage/modules.json').read_bytes());page=ROOT/'SafeLearning/viability.html';lines=page.read_text().splitlines(keepends=True)
assert next(x for x in inv['exercises']if x['key']=='viability.html::exercise-19')==d['entire_current_exercise']==context['entire_current_exercise_inventory_row']
assert next(x for x in owner['exercises']if x['inventory_key']=='viability.html::exercise-19')==d['entire_original_seven_pending_claim_exercise_row']==context['entire_original_pending_exercise_owner_row']
for u in d['entire_current_material_units']:assert next(x for x in inv['material_source_units']if x['key']==u['key'])==u
for row in d['entire_original_six_pending_material_rows']:assert next(x for x in owner['material_claims']if x['id']==row['id'])==row and row['status']=='pending'
assert ''.join(lines[940:957])==d['full_current_exercise_context']
for key,record in d['entire_current_and_proposed_changed_literals'].items():
 assert record['entire_proposed']['source_text']==record['entire_current']['source_text'].replace('the multiplier and the cost oscillate around the constraint boundary','the multiplier and the cost can oscillate around the constraint boundary')
assert d['exact_one_phrase_substitution']==[{'before':'the multiplier and the cost oscillate around the constraint boundary','after':'the multiplier and the cost can oscillate around the constraint boundary'}]
for k,span in [('full_source_Section3_penalty_setup_lines251_307',(250,307)),('full_source_Section4_theorem_context_lines308_479',(307,479)),('full_source_Section5_and_duality_context_lines480_581',(479,581))]:assert context[k]==''.join(lines[slice(*span)])
prep=json.loads(add(d['actual_author_preparation']).read_bytes())
assert prep['status']=='passed'and type(prep['actual_exit_code'])is int and prep['actual_exit_code']==0 and prep['protection_errors']==[]
assert prep['helper_sha256_before']==prep['helper_sha256_after']and prep['protected_inputs_sha256_before']==prep['protected_inputs_sha256_after']
assert prep['actual_command']==['python3','/tmp/prepare-modules-duality134-whole-composition-request30-v2.py']and prep['actual_workdir']==str(ROOT)
for old,q in d['actual_author_preparation_original_byte_aliases'].items():assert sha(add(q))==sha(old)
assert sha(prep['raw_log'])==prep['raw_log_sha256']
assert all(d[k]is False for k in ['current_whole_exercise_approved','prospective_whole_exercise_approved','whole_material_promotions_performed','source_ordinal_reserved','source_applied','canonical_pairs_executed','owner_or_selection_or_publication_mutation','coverage_complete'])
expected=Path('/tmp/CompleteModulesViabilityDualExpectation30-draft-v10.lean').read_text()
assert '(hSVF : ∀ x u,'in expected and '(hallmaxsafe : ∀ p : ℝ,'in expected
old55=json.loads(add(d['original55_full_scope_request']).read_bytes())
for q in old55['selected_complete_dependency_sources']:add(q)
primaryfacts=json.loads(add(d['bounded_Altman_finite_discounted_CMDP_primary_facts']).read_bytes())
for row in primaryfacts['offline_full_book_originals']:
 assert sha(row['original_path'])==row['sha256']and Path(row['original_path']).stat().st_size==row['bytes']and row['Root_copy']is False
factual_offline=[]
for n in ['/tmp/foundations-dual55-primary30-paternain-1910.13393v1-full-text-v1.txt','/tmp/foundations-dual55-primary30-svf-2105.12204v4-full-text-v1.txt']:
 p=Path(n);factual_offline.append({'original_path':str(p),'sha256':sha(p),'bytes':p.stat().st_size,'Root_copy':False})
missing='The actual generic prior Theorem2/Proposition1 source hypotheses are not connected by a Lean theorem to the hSVF/hallmaxsafe and common-safe-optimum hypotheses used by expected31. These are honest conditional components, not a derived primitive-source safety theorem.'
decisions=[
 {'key':'viability.html::node-1149','current_whole_approved':False,'prospective_whole_approved':False,'approved_components':['Full part(a), exact conditional expectation/ray/saddle/update components and genuine finite examples.'],'remaining_gaps':[missing,'The question includes all a–d; approved components alone do not close the complete requested exercise.']},
 {'key':'viability.html::node-1153','current_whole_approved':True,'prospective_whole_approved':True,'approved_components':['Actual Bochner expected Lagrangian, common pointwise optimizer gives actual dual expectation identity, safe/nonnegative-zero-budget weak duality, genuine finite deterministic discounted common stationary optimizer.'],'remaining_gaps':[]},
 {'key':'viability.html::node-1155','current_whole_approved':False,'prospective_whole_approved':False,'approved_components':['Conditional SVF/common-safe-optimum implication to expected primal=dual; genuine all-history Chain/Dirac2 actual dual max profile and attained safe primal, conservative threshold15/2 and exact optimal rayIci1.'],'remaining_gaps':[missing]},
 {'key':'viability.html::node-1157','current_whole_approved':False,'prospective_whole_approved':False,'approved_components':['Actual nonincreasing convex one-Lipschitz real dual and nonnegative closed-ray theorem under explicit attained-safe-optimum/all-max-safe-above-threshold hypotheses.'],'remaining_gaps':[missing+' In particular, the source-derived nonempty zero-gap ray above the printed threshold is not proved by continuity and integrity alone.']},
 {'key':'viability.html::node-1158','current_whole_approved':False,'prospective_whole_approved':False,'approved_components':['Actual attained-feasible primal + zero-gap implication to complementarity/penalized maximizer/saddle and primal optimality.','Genuine feasibility-alone finite scalar-CMDP stationary and all-history attained strong duality.','True p10 feasible/infeasible/suboptimal ties with explicit p/10 ordinary-multiplier scaling.','True absence of strict Slater for zero nonnegative risk.','Independently verified factual primary attribution to Paternain Theorem1 and Altman3.6/3.7 in their exact domains.'],'remaining_gaps':[missing+' The final SVF contrast is not relabeled as derived from Assumption1.', 'No general continuous-state bounded-risk Slater existence theorem is kernel-proved by the five proposed sources. The primary citation is verified as an attribution, and the finite scalar theorem must keep its finite domain; it does not substitute for that general mathematical existence clause.']},
 {'key':'viability.html::node-1162','current_whole_approved':False,'prospective_whole_approved':False,'approved_components':['Actual expected-risk projected monotone increment and stop iff AE-safe.','Actual countable-clock nontermination with immediate post-exit failure and one common stationary optimizer from every surviving initial clock at every nonnegative penalty.','Actual finite feedback no-repeat first-failure bound, positive-support risk lower bound and finite stopping conditional on all selected optimizers safe above the threshold.','Primary PID possibility attribution and actual positive-budget nonoscillation countermodel support the prospective can-oscillate qualifier.'],'remaining_gaps':['The current universal oscillation sentence is false; the independently reviewed prospective one-phrase correction removes it.',missing+' The finite stopping theorem still takes safe-above-threshold as an interface, rather than deriving it from the generic prior source theorem.']},
 {'key':'viability.html::exercise-19','current_whole_approved':False,'prospective_whole_approved':False,'approved_components':['All previously approved134 kernel-checked mathematical bodies in their unchanged exact domains; full part(a), exact finite-DP/LP/Chain/Clock associations.'],'remaining_gaps':[missing,'The general continuous-state Slater existence clause has primary factual support but is not a kernel theorem in this finite-source composition.','Current universal oscillation needs the prospective can qualifier; that wording change alone does not close the remaining generic mathematical interfaces.']}
]
out={'status':'passed_independent_full_duality134_composition_reader_with_explicit_semantic_pending_decisions','reviewer':'/root/foundations_recovery28','review_finished_at_utc':datetime.now(timezone.utc).isoformat(),'request':ref(REQUEST),'families':d['families'],'unique_public_theorem_count':134,'all134_entire_proof_bodies_and_actual_definitions_read_in_continuing_full_reviews':True,'previous_exact_full_source_semantic_decisions_preserved':priorrefs,'full_current_exercise_and_all6_entire_material_units_and_original_pending_rows_read':True,'full_current_sections3_5_and_proposed_whole_exercise_context_read':True,'original_full_source_context':d['current_full_Section3_4_setup_and_SVF_and_exercise_context'],'individual_decisions':decisions,'whole_current_exercise_approved':False,'whole_prospective_corrected_exercise_approved':False,'prior_components_rejected_or_retimed':False,'semantic_pending_is_not_an_execution_or_reader_failure':True,'genuine_current_source_matching_native_best_records':natives,'all_prior_native_histories_body_and_time_preserved_by_exact_original_request_refs':d['separate_full_original_source_requests'],'original55_full_scope_request':d['original55_full_scope_request'],'original68_full_scope_request':d['original68_full_scope_request'],'primary_factual_attribution_review':{'Paternain':'Full Section2 compact state/action stochastic discounted model, bounded stage rewards, stated Theorem1 Slater hypotheses and complete occupancy/perturbation proof read. The printed theorem states zero duality gap; it is not claimed kernel-derived from finitePoly8.','Altman':'Full used discounted occupation/recovery/compact-polytope LP setup and complete3.3/3.4 Theorems3.6/3.7 proof read. No-Slater attained scalar multiplier is separately genuinely constructed by finitePoly8; it is not attributed solely to the Slater multiplier discussion in3.6.','Massiani':'Full used Section3 uniform common attainment and Section4 Definition3/Proposition1/Assumption1/Theorem2/zeroth-order proof contexts, SectionVB Example1/Remark5 read. These primary results are explicit named prior dependencies, not relabeled as already derived Lean interfaces.','general_theorem_kernel_coverage_claimed':False,'offline_full_primary_reference_bytes_not_published':factual_offline+primaryfacts['offline_full_book_originals'],'bounded_Altman_factual_receipt':d['bounded_Altman_finite_discounted_CMDP_primary_facts']},'scope_limits':['Common source attainment and a safe common optimizer are legitimate explicitly stated source interfaces, but their generic Theorem2 derivation remains separate work.','The expected theorem X can be restricted to viable initial states supporting mu; no safety of unviable initial states is inferred.','Clock common stationary attainment is genuinely quantified over every surviving starting clock; the terminated bookkeeping state is not substituted for another physical viable state.','Finite-CMDP result allows actual random policies/history path laws and uses the positive normalization1-gamma; no continuous-state extension or measurable-selector existence is asserted.','All seven old full component peer bodies/times remain exact. New semantic pending decisions concern the entire composition only.'],'original_closed_byte_aliases':d['original_closed_byte_aliases'],'required_evidence_artifacts_sha256':closed,'actual_author_preparation':d['actual_author_preparation'],'errors':[],'compiler_parser_source_owner_canonical_publication_mutation':False,'prospective_evidence_outside_frozen29':True,'coverage_complete':False}
OUT.write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'findings':ref(OUT),'individual_wholes_approved':[v['key']for v in decisions if v['current_whole_approved']],'whole_prospective_exercise':False,'errors':[]}))
