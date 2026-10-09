import json,hashlib,re,sys,collections
from pathlib import Path
sys.path.insert(0,'book')
from validate import Document,clean_text
from foundations_review import EXTRA,FULL,ATOMS,NONFORMAL,topic,clauses
from foundations_promotions import COMPLETE_EXERCISES,FULL_MATERIAL,PARTIAL_MATERIAL,PARTIAL_EXERCISES,REVIEWED_COMPLETE_MATERIAL,SURROUNDING_PROSE
FULL.update(FULL_MATERIAL)
for key,rows in PARTIAL_MATERIAL.items():ATOMS.setdefault(key,[]).extend(rows)
root=Path('.')
inv=json.load(open('book/coverage/inventory.json'))
old=json.load(open('reports/lean-verification/primers-foundations-coverage.json'))
pages=['primer-basics.html','primer-linalg.html','primer-optimization.html']
source={f'SafeLearning/{p}' for p in pages}|{f'book/chapters/{p}' for p in pages}
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
oldby={x['summary']:x for x in old['exercises']}
newmap={
'book-0-ex-1': [('The complete accepted-reading set is [1/5,24/5].','temperature_reading_rule'),('Reading47/10 is accepted;49/10 permits both a passing47/10 and failing51/10 true value.','reading_examples')],
'book-0-ex-2': [('At temperature24/5 the actuator commands satisfying every permitted disturbance are exactly[-1,-17/25].','chamber_exercise_commands'),('The command-4/5 gives successor endpoints112/25 and122/25.','chamber_exercise_numerics'),('The disturbance-dependent command-7/25-w remains within[-17/25,-7/25] and yields successor5.','anticipative_command')],
'book-0-ex-3': [('Every error sequence obeying the stated initial value and recurrence has the all-index envelope3/50+16/25(1/2)^n.','exercise_error_envelope'),('The weak target7/100 is attained by the bound exactly from index6; the strict target exactly from index7.','error_exercise_minimal_index'),('The explicit bound remains above3/50 and cannot certify1/25 at any finite index.','error_floor_unattainable'),('Equality in the affine envelope is a sequence realizing the original recurrence.','affine_recurrence_realization')],
'book-0-ex-4': [('For nonnegative disturbance capd robust per-state actuator feasibility holds exactly whend<=1/2.','chamber_feedback_range'),('The explicit feedback-x/5 makes the interval invariant for arbitrary allowed disturbance sequences from an allowed initial state.','chamber_invariance')],
'book-a-ex-1': [('The balanced equations reconstruct coordinates(y1+y2)/2 and(y1-y2)/2.','balanced_reconstruction'),('Individual sensor errors bounded byepsilon give first-coordinate error at mostepsilon and Euclidean squared error at mostepsilon^2.','balanced_error_geometry'),('The larger error bound permits a violating true state; the smaller bound certifies the assembly limit.','balanced_assembly_examples')],
'book-a-ex-2': [('Every solution ofx+y=6 has form(3+t,3-t), with nonnegativity exactly-3<=t<=3.','sum_measurement_all_solutions,sum_measurement_identification'),('The unique minimum squared length is18 at(3,3).','sum_measurement_unique_minimum'),('The state(5,1) fits the reading and nonnegativity while violating first-coordinate limit4.','sum_measurement_counterexample')],
'book-a-ex-3': [('The normalized radius1/10 ball gives largest absolute output error sqrt5/10, attained in direction(2,1).','normalized_output_ball_bound,normalized_output_attainer'),('The separate-coordinate box gives valid upper bound3/10 and includes the corner excluded by the Euclidean ball.','normalized_box_bound,balanced_assembly_examples'),('The quoted decimal output error lies in the certified interval(0.223606,0.223608).','normalized_output_decimal_bound')],
'book-a-ex-4': [('The three-sensor Gram matrix and right side equal the quoted normal equations.','normal_equations_three_sensor'),('The rational candidate has the quoted residual, residual orthogonality, and squared state error(29/201)^2.','three_sensor_residual_certificate'),('The full least-squares cost has a sum-of-squares gap and is uniquely minimized by the quoted candidate.','three_sensor_loss_identity,three_sensor_unique_optimum'),('The sensor Gram quadratic form is positive in every nonzero direction; loss differentiation in any direction matches the stated residual condition.','sensor_gram_positive,least_squares_direction_derivative')],
'book-b-ex-1': [('The transfer cost equals1/2-t+5t^2/2=2/5+5(t-1/5)^2/2.','allocation_transfer'),('The constrained global allocation optimum is unique and has the checked KKT certificate.','allocation_unique_optimum,allocation_kkt'),('The transfer derivative is-1+5t and the optimal objective gradient has zero product with every tangent transfer(-t,t).','allocation_tangent_gradient')],
'book-b-ex-2': [('The budget-dependent allocation formulas satisfy feasibility and KKT in active-set range(1/4,4), and globally minimize the original quadratic loss there.','allocation_kkt,allocation_unique_optimum'),('The optimal-value derivative is minus the multiplier, and the exact finite cost decrease includes quadratic remainder2delta^2/5.','allocation_value_derivative,allocation_sensitivity_exact'),('Both quoted budgets have the stated commands, multipliers, values and actual cost decrease29/250.','allocation_numerical_checks')],
'book-b-ex-3': [('The reported point has stationarity residual(1/100,0) and budget violation1/100.','allocation_numerical_checks'),('The minimum Euclidean correction to the sum line subtracts the same amount from both coordinates.','sum_line_projection'),('The repaired point sums to3 and has cost6401/16000 and gap1/16000.','allocation_numerical_checks')],
'book-b-ex-4': [('The universal clearance requirement is equivalent to(a+1)^2<=3-10d, and any feasible command exists exactly ford<=1/5 underd>=0.','robust_clearance_exact,robust_clearance_feasible'),('For every allowed capd, sqrt(3-10d)-1 is feasible and uniquely minimizes the tracking objective over all robustly feasible commands.','clearance_optimum'),('For cap below1/5 the quoted multiplier is positive, satisfies stationarity and complementary slackness, and both domain bounds are inactive.','clearance_kkt'),('The old nonrobust command has worst clearance7/100<1/10 at new disturbance cap3/100.','nonrobust_clearance_failure'),('The robust command, value and multiplier decimals are enclosed by rigorously checked rational intervals.','robust_clearance_decimal_bounds,robust_multiplier_decimal_bound')]
}
logic={
'mb-ex-s1':['finite_set_membership_inclusion'], 'mb-ex-s4':['negations_instantiated'],
'mb-ex-s6':['shrinking_interval_union','shrinking_interval_intersection'], 'mb-ex-s7':['interval_deMorgan'],
'mb-ex-f1':['finite_square_image'], 'mb-ex-f2':['composition_examples'],
'mb-ex-f3':['quarter_iteration_error'], 'mb-ex-f4':['square_interval_image','square_interval_preimage','negative_square_preimage'],
'mb-ex-f5':['square_to_nonnegative_classification','square_from_nonnegative_classification','nonnegative_square_inverse'],
'mb-ex-f6':['alternating_iteration_error','alternating_iteration_minimal'],
'mb-ex-f9':['half_open_contraction_counterexample','selfmap_counterexample','strict_contraction_counterexample','alternating_unit_sequence_not_convergent'],
'mb-ex-p7':['missing_endpoint_contraction'],'mb-ex-p8':['invariant_and_rate_from_local_hypothesis'],
'mb-ex-sequences-3':['telescoping_energy_budget','telescoping_summability','telescoping_state_convergence','excursion_budget_finite','arbitrarily_late_excursion']}
limits={'mb-ex-bounds-1':['half_open_interval_extrema','approaching_one_extrema'],
'mb-ex-topology-1':['half_open_interval_topology'],'mb-ex-topology-2':['half_open_square_no_minimum','square_unique_minimum_on_real'],
'mb-ex-sequences-1':['reciprocal_sequence_limit'],'mb-ex-asymptotics-1':['polynomial_ratio_limit'],
'mb-ex-asymptotics-3':['average_log_sqrt_limit','bounded_average_regret_converges','log_sqrt_product_counterexample','sqrt_sublinear'],
'opt-ex-minmax-1':['open_interval_sup_and_no_argmax','square_closed_interval_argmax']}
finite={'mb-ex-p9':['finite_orbit_collision','orbit_reduce_at_collision','finite_orbit_early_occurrence','finite_state_check_all_time','four_state_first_five','four_state_never_failure','changing_rule_counterexample']}
closed_extra={'mb-ex-s1','mb-ex-s4','mb-ex-s6','mb-ex-s7','mb-ex-f2','mb-ex-f3','mb-ex-f4','mb-ex-f5','mb-ex-f6','mb-ex-p8','mb-ex-p9','mb-ex-bounds-1','mb-ex-topology-1','mb-ex-topology-2','opt-ex-minmax-1'}
exercises=[]
for x in inv['exercises']:
 if x['source'] not in {f'SafeLearning/{p}' for p in pages}:continue
 o=oldby.get(x['label']);claims=[]
 reviewed_key=x['anchor'] if x['anchor'] in COMPLETE_EXERCISES else x['key']
 if x['anchor'] in newmap:
  for i,(st,nms) in enumerate(newmap[x['anchor']],1):
   claims.append(dict(id=f"{x['key']}::math-{i}",statement_in_prose=st,kind='mathematical_model_conclusion',lean_declarations=['SafeLearning.CompleteFoundationsBook.'+n for n in nms.split(',')],status='proved',hypotheses='Exactly the mathematical hypotheses in the cited statements; normalized real-valued stipulated models. Physical validity is separately assumed.',correspondence='Exact symbolic models, quantified ranges, extrema and witnesses are encoded; rational bounds support quoted approximations where present.',remaining_gaps=[]))
  claims.append(dict(id=f"{x['key']}::interpretation",statement_in_prose='Physical calibration, unit choices, timing and recommendations are assumptions and teaching interpretations, not empirical theorems.',kind='pedagogical_and_model_assumption',lean_declarations=[],status='not_a_formal_claim',hypotheses=[],correspondence='No assertion that the hypothetical device exists or has measured performance is inferred.',remaining_gaps=[]))
  status='complete_math'
 elif reviewed_key in COMPLETE_EXERCISES:
  for i,row in enumerate(COMPLETE_EXERCISES[reviewed_key],1):
   claims.append(dict(**row,id=f"{x['key']}::reviewed-math-{i}",kind='individually_reviewed_mathematical_conclusion',status='proved',remaining_gaps=[]))
  for c in claims:c['lean_declarations']=sorted(set(c['lean_declarations']))
  status='complete_math'
 else:
  assert o,x['label']
  refs=[r['name'] for r in o['declarations']]
  for d,namespace in [(logic,'Logic'),(limits,'Limits'),(finite,'Finite')]:refs+=['SafeLearning.CompleteFoundations'+namespace+'.'+n for n in d.get(x['anchor'],[])]
  refs+=EXTRA.get(x['anchor'],[])
  complete=o['status']=='complete_mathematical_conclusions' or x['anchor'] in closed_extra
  ansdoc=Document(o['source_snippet']);ds=list(ansdoc.root.descendants('details'))
  last=ds[-1] if ds else ansdoc.root
  paragraphs=[clean_text(n.text()) for n in last.descendants() if n.tag=='p' or 'math-block' in n.attrs.get('class','').split()]
  if not paragraphs:paragraphs=[o['expected_result']]
  for i,paragraph in enumerate(paragraphs,1):
   for j,st in enumerate(clauses(paragraph),1):
    claims.append(dict(id=f"{x['key']}::solution-{i}-{j}",statement_in_prose=st,kind='source_solution_clause',lean_declarations=refs,status='proved' if complete else 'pending',hypotheses=o['source_assumptions'],correspondence=('Previous exact proof correspondence extended by the named new missing conclusions.' if complete else 'Referenced declarations cover selected subclaims only. This exact source clause remains conservatively pending until each mathematical conclusion has a complete correspondence.'),remaining_gaps=[] if complete else [o['coverage_scope_and_remaining'],'Complete the quoted clause, including any distinct definition, domain, necessity, uniqueness or numerical-enclosure conclusion; the listed references are not blanket coverage.']))
  status='complete_math' if complete else ('partial' if refs else 'pending')
  for i,row in enumerate(PARTIAL_EXERCISES.get(x['key'],[]),1):
   claims.append(dict(**row,id=f"{x['key']}::reviewed-component-{i}",kind='individually_reviewed_mathematical_component',status='proved',remaining_gaps=[]))
 exercises.append(dict(inventory_key=x['key'],source=x['source'],locator=x['locator'],label=x['label'],source_text=x['source_text'],source_text_sha256=x['text_sha256'],status=status,claims=claims))
# Exact exercise overlaps share the reviewed exercise correspondences; teaching
# units are separated into explicit proved atoms and precise pending clauses.
material=[]
for u in inv['material_source_units']:
 if u['source'] not in {f'SafeLearning/{p}' for p in pages}:continue
 owners=[x['inventory_key'] for x in exercises if u['source_text'] in x['source_text']]
 common=dict(source_unit_keys=[u['key']],source=u['source'],locator=u['locator'],source_text=u['source_text'],source_text_sha256=u['text_sha256'],source_sha256=u['source_sha256'])
 if owners:
  owner_rows=[e for e in exercises if e['inventory_key'] in owners]
  closed=all(e['status']=='complete_math' for e in owner_rows)
  rs=sorted({r for e in owner_rows for c in e['claims'] for r in c['lean_declarations']})
  gaps=[] if closed else sorted({g for e in owner_rows for c in e['claims'] for g in c['remaining_gaps']})
  material.append(dict(**common,id=u['key']+'::exercise-overlap',statement_in_prose=u['source_text'],kind='exact_exercise_source_overlap',lean_declarations=rs,status='proved' if closed else 'pending',hypotheses='Exactly the mathematical domains and assumptions of the source exercise and its cited declarations.',correspondence='This exact excerpt is contained in exercise source(s) '+', '.join(owners)+'. Nested prompts/hints/solutions share those mathematical conclusions; no independent theorem is inferred from duplication.',remaining_gaps=gaps))
  continue
 page=Path(u['source']).name;node=int(u['key'].split('node-')[-1]);subject,gap=topic(page,node)
 if u['key'] in REVIEWED_COMPLETE_MATERIAL:
  for i,row in enumerate(REVIEWED_COMPLETE_MATERIAL[u['key']],1):
   material.append(dict(**common,**row,id=u['key']+f'::reviewed-claim-{i}',kind='reviewed_mathematical_assertion',status='proved',remaining_gaps=[]))
  continue
 if u['key'] in FULL:
  material.append(dict(**common,id=u['key']+'::checked',statement_in_prose=u['source_text'],kind='reviewed_mathematical_assertions',lean_declarations=FULL[u['key']],status='proved',hypotheses='The cited declarations explicitly state the mathematical domains and any nonempty/positive/complete-space assumptions. Teaching advice in this excerpt is prose, not an added empirical conclusion.',correspondence='Exact correspondence reviewed for this source unit: '+subject+'. The named declarations prove all of its mathematical assertions.',remaining_gaps=[]))
  continue
 if node in NONFORMAL.get(page,set()):
  material.append(dict(**common,id=u['key']+'::interpretation',statement_in_prose=u['source_text'],kind='cross_reference_or_stipulated_model_interpretation',lean_declarations=[],status='not_a_formal_claim',hypotheses=[],correspondence='This unit introduces a stipulated physical/modeling assumption, directs reading, or describes pedagogical use; it asserts no new mathematical implication beyond the separately audited formulas and examples.',remaining_gaps=[]))
  continue
 for i,(st,rs) in enumerate(ATOMS.get(u['key'],[]),1):
  material.append(dict(**common,id=u['key']+f'::proved-atom-{i}',statement_in_prose=st,kind='reviewed_mathematical_subclaim',lean_declarations=rs,status='proved',hypotheses='Only the precise domains, regularity and positivity assumptions stated in the corresponding declarations.',correspondence='This explicitly named subclaim is covered; the other source clauses remain separate pending records below.',remaining_gaps=[]))
 for i,st in enumerate(clauses(u['source_text']),1):
  material.append(dict(**common,id=u['key']+f'::remaining-clause-{i}',statement_in_prose=st,kind='reviewed_mathematical_clause_or_definition',lean_declarations=[],status='pending',hypotheses='Source context: '+subject+'. All stated mathematical hypotheses must be preserved, including edge cases.',correspondence='Semantic review identifies this exact source clause under '+subject+'. A theorem/example assertion is retained as mathematical work; it is not reclassified as teaching advice merely because it appears in prose.',remaining_gaps=['Supply the complete formal correspondence for '+gap+'. Exact remaining source clause: '+st]))
used_modules={d.split('.')[1] for row in exercises for c in row['claims'] for d in c['lean_declarations']}
used_modules.update(d.split('.')[1] for c in material for d in c['lean_declarations'])
surrounding=[]
for key,review in SURROUNDING_PROSE.items():
 page,node_index=key.split('::node-');path='SafeLearning/'+page
 node=Document(Path(path).read_text()).nodes[int(node_index)-1]
 text=node.text();assert text and not any(u['key']==key for u in inv['material_source_units'])
 claims=[dict(**row,status='proved',remaining_gaps=[]) for row in review['proved']]
 claims += [dict(statement_in_prose=st,lean_declarations=[],status='pending',remaining_gaps=[st]) for st in review['pending']]
 surrounding.append(dict(source=path,locator='::node-'+node_index,line=node.line,
   source_sha256=sha(path),source_text=text,source_text_sha256=hashlib.sha256(text.encode()).hexdigest(),
   scope='Explicit review beyond mechanically selected material-source units; no inventory unit is added or counted.',
   claims=claims,status='partial' if review['pending'] else 'complete_math'))
 used_modules.update(d.split('.')[1] for c in claims for d in c['lean_declarations'])
# In-progress unpublished modules are not formal evidence merely because a
# filename exists. Only modules actually referenced by this audited ledger are
# listed; their actual compile evidence remains a separate required check.
proofs=sorted(str(p) for p in Path('verification/lean/SafeLearning').glob('CompleteFoundations*.lean') if p.stem in used_modules)
out=dict(schema_version=1,status='partial',scope_pages=['SafeLearning/'+p for p in pages],source_sha256={p:sha(p) for p in sorted(source)},proof_files=proofs,proof_sha256={p:sha(p) for p in proofs},exercises=exercises,material_claims=material,surrounding_prose_reviews=surrounding,counts=dict(exercises=len(exercises),exercise_statuses=dict(collections.Counter(x['status'] for x in exercises)),material_source_units=len({k for c in material for k in c['source_unit_keys']}),material_claim_statuses=dict(collections.Counter(c['status'] for c in material))),limits=['Standalone compilation is a separate evidence record; overall kernel replay and axiom audit are owned by the integrator.','Every pending unit or exercise remains a real gap; theorem count is not exercise coverage.','Nested overlapping excerpts share exact source keys and are not counted as independent theorems.','Pending clauses may overlap a proved subclaim; only the explicit reviewed atoms are promoted, while full clause equivalence remains conservative.'])
Path('book/coverage/foundations.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
print(out['counts'])
