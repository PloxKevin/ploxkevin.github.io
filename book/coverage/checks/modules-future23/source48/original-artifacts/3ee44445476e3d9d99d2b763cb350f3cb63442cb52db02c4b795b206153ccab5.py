"""TMP-only whole-literal readers; no Lean or canonical execution."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re

ROOT=Path('/home/oxrexkevin/SafetyBased')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def name2(n):return 'SafeLearning.CompleteModulesNNStabilityLMI23.'+n
def name4(n):return 'SafeLearning.CompleteModulesNNCertificateAudit23.'+n
request_specs=[(2,'7620e797d578804ff9d959a54d4960916f013d9c43b70e20852ecebb983e81c4'),(4,'9fe1acd2c6041e8e2abd86867e36b8b59e2b5a7a0579a18b05e6aefe4e4664de')]
baseline=read(ROOT/'reports/full-coverage/checkpoint-21-manifest.json')
bindings=read(ROOT/'book/coverage/checks/root-owner22-reviewed-candidate-bindings-v3.json')
protected={**bindings['exact_current48_safelearning_assets_sha256'],**bindings['new_immutable_proof_sources_sha256'],**{p:r['sha256'] for p,r in baseline['proof_files'].items()}}
for p,h in protected.items():assert sha(ROOT/p)==h
inventory_path=ROOT/'book/coverage/inventory-after-correction48.json'
inventory_sha=sha(inventory_path)
assert inventory_sha==sha(ROOT/'book/coverage/inventory.json')=='2daa285ff1cbc2ad0db045e00e1271b6cb58ce809f5a8328120286748250c108'
inventory=read(inventory_path)
exercises={r['key']:r for r in inventory['exercises']}
units={r['key']:r for r in inventory['material_source_units']}
reports=[]
for number,expected_request_sha in request_specs:
 request_path=Path(f'/tmp/modules-nn-hard-{number}-whole-source-review-request23-v1.json')
 assert sha(request_path)==expected_request_sha
 request=read(request_path)
 assert request['inventory']['sha256']==inventory_sha
 assert request['exercise']==exercises[request['exercise']['key']]
 assert sha(ROOT/request['source']['file'])==request['source']['sha256']
 for row in request['material_units']:assert row==units[row['key']]
 source_path=Path(request['new_source']['file'])
 assert sha(source_path)==request['new_source']['sha256']
 text=source_path.read_text()
 assert not re.search(r'\b(sorry|axiom)\b',text)
 ns='SafeLearning.CompleteModulesNNStabilityLMI23' if number==2 else 'SafeLearning.CompleteModulesNNCertificateAudit23'
 theorem_names=[ns+'.'+n for n in re.findall(r'^theorem (\w+)',text,re.M)]
 assert theorem_names==request['new_public_theorem_names']
 assert len(theorem_names)==(11 if number==2 else 9)
 snapshots=[]
 failures=[]
 entries=[{'actual_record':request['actual_standalone_record'],'raw_log':request['raw_log'],'source_snapshot':request['source_snapshot'],'actual_exit_code':0}]+request['actual_failure_history']
 for entry in entries:
  for kind in ['actual_record','raw_log','source_snapshot']:
   reference=entry[kind]
   assert sha(reference['file'])==reference['sha256']
  record=read(entry['actual_record']['file'])
  assert type(record['actual_exit_code']) is int and record['actual_exit_code']==entry['actual_exit_code']
  assert record['command']==['lake','env','lean',str(source_path)]
  assert record['actual_workdir']==str(ROOT/'verification/lean')
  assert record['source']==str(source_path)
  assert record['source_sha256_before']==record['source_sha256_after']==record['source_snapshot_sha256']==sha(entry['source_snapshot']['file'])
  assert record['source_snapshot']==entry['source_snapshot']['file']
  assert record['log']==entry['raw_log']['file'] and record['log_sha256']==entry['raw_log']['sha256']
  assert record['started_at_utc']<record['finished_at_utc'] and record['elapsed_seconds']>0
  snapshots.append({'actual_record':entry['actual_record'],'full_original_record_body':record,'raw_log':entry['raw_log'],'full_original_raw_log':Path(entry['raw_log']['file']).read_text(),'source_snapshot':entry['source_snapshot']})
  if entry['actual_exit_code']:
   assert Path(entry['raw_log']['file']).read_text()
   failures.append(entry['actual_record'])
  else:
   assert record==request['actual_standalone_record_body']
   assert Path(entry['source_snapshot']['file']).read_bytes()==source_path.read_bytes()
   assert Path(entry['raw_log']['file']).read_bytes()==b''
 imports={}
 for module,row in request['protected_import_sources'].items():
  assert sha(ROOT/row['file'])==row['sha256']
  imports[module]=row
 if number==2:
  hypotheses=['The forced scalar loop is F(x)=6x/5−activation(x)/2; actualOrbit is its iterate from the supplied initial state.','For local attraction, initial²≤radius² and QC(x,activation(x))≥0 for every x²≤radius². This uniform certified-set premise is required before the induction; it does not assume the desired trajectory conclusion.','The ratio-sector statement for nonzero x is represented by w=d*x with d∈[1/2,1], which also preserves the zero-equilibrium extension.']
  specs=[
   ('1119','proved','All question clauses are answered: exact closed-loop Lyapunov/QC expansion, actual negative-definite matrix, and the conditional local conclusion for every certified initial point.',theorem_names,hypotheses),
   ('1120','nonformal','Optional study navigation only; it asserts no additional theorem about a linked general controller.',[],[]),
   ('1126','proved','The selected full generic symmetric-plane positive-definite pivot/determinant criterion applies to the negative of a symmetric matrix. Negating a real2x2 matrix preserves its determinant and reverses its first diagonal; hence the negative-first-diagonal/positive-determinant criterion is the exact negative-definite interpretation. The current numerical matrix uses this criterion explicitly.',[name2('actual_negative_definiteness_from_the_true_two_by_two_criterion'),'SafeLearning.CompleteFoundationsQuadraticForms.plane_pd_criterion','SafeLearning.CompleteFoundationsQuadraticForms.generic_symmetric_plane_criterion'],['The matrix is real symmetric2x2; negative definiteness means its negative is PosDef.']),
   ('1130','proved','Exact rational expansions give11/25x²−6/5xw+1/4w², −x²+3xw−2w² and their sum−14/25x²+9/5xw−7/4w². These equal the printed decimals without approximation.',[name2('actual_lyapunov_and_qc_expansions')],['x,w are arbitrary real numbers.']),
   ('1132','proved','The actual Matrix(Fin2)(Fin2) has the printed entries and determinant17/100. Official matrix spectrum is exactly(−231±sqrt46561)/200. Rigorous one-sided square-root and absolute-error bounds justify both printed approximate eigenvalues; negative definiteness is separately proved through PosDef of−M.',[name2('actual_printed_matrix_and_determinant'),name2('actual_negative_definiteness_from_the_true_two_by_two_criterion'),name2('actual_exact_full_official_spectrum'),name2('actual_source_eigenvalue_roundings_are_rigorous')],['The decimal eigenvalues are approximations, with exact error tolerances proved in the source.']),
   ('1134','proved','The ratio-sector substitution gives a nonnegative QC. The actual quadratic form is negative away from zero, so ΔV≤ΔV+QC<0; a stronger uniform margin yields V(F(x))≤93/100V(x). Assuming the proposed sublevel is contained in the local validity domain, induction proves actual forced-orbit invariance and a geometric energy envelope for every initial point in that set, then a true Tendsto theorem gives convergence. The last no-global sentence is local-domain advice: the premise supplies no sector information outside the set, and no outside initial-state conclusion is inferred. The literal does not specify an exterior fixture to be solved.',[name2(n) for n in ['actual_sector_qc_is_nonnegative','actual_on_sector_the_energy_strictly_decreases','actual_uniform_energy_margin','actual_on_sector_one_step_geometric_energy_bound','actual_contained_local_sector_implies_all_time_invariance_and_energy_bound','actual_contained_local_sector_trajectory_converges']],hypotheses)
  ]
  components=[
   {'clause':'Exact energy/QC algebra and official negative-definite matrix spectrum','lean_declarations':theorem_names[:5],'hypotheses':[],'reason':'All algebraic coefficients, determinant, generic2x2criterion and rigorous printed eigenvalue approximations are proved on the actual matrix.','missing_clauses':[]},
   {'clause':'Sector implication and actual local-loop stability','lean_declarations':theorem_names[5:],'hypotheses':hypotheses,'reason':'The one-step inequality uses the QC at the current state. All-initial-condition induction keeps actual forced iterates in the same certified set and proves geometric energy decay and convergence. No global-sector premise or conclusion has been silently added.','missing_clauses':[]}
  ]
  limits=['Local convergence is conditional on the uniform local-QC validity premise and certified initial set. No particular radius/domain was supplied by the literal, so no concrete numerical radius is fabricated.','No separate exterior clamp/orbit theorem is present in this source; the literal no-global sentence is reviewed as scope advice.','The full generic hint also binds the selected quadratic-forms import. No unreviewed general neural training stability statement is inferred.']
 else:
  hypotheses=['The three channels are shifted ReLUs with base pre-activations(0,0,1); valid diagonal QC weights are nonnegative.','The hard-IQC sum is asserted for every finite horizon of the supplied actual filter history. Generic summation retains V0 and the full filterState argument; it does not infer this premise for arbitrary filter initialization.','Perturbed matrices M,E are real Hermitian; the original quadratic-form upper bound is−margin||x||², the perturbation upper bound isdelta||x||², anddelta<margin. For the intended retained strict certificate, take a proven positive original margin.','The small-update counterexample quantifies everyepsilon∈(0,1), changing the scalar stability form weight²−1 from negative to positive.']
  specs=[
   ('998','nonformal','This is an identical optional review-link row outside the Hard4 parent exercise. It is valid navigation only and is explicitly not counted as a new mathematical claim.',[],[]),
   ('1159','proved','Each requested missing justification and repair is addressed by the actual three-channel mismatch/repaired QCs, the all-prefix IQC with a negative individual sample and retained-history summation, and the strict-margin perturbation theorem plus arbitrarily small update sign counterexample.',theorem_names,hypotheses),
   ('1160','nonformal','Optional review navigation only; no theorem about the linked article or general neural controller is inferred.',[],[]),
   ('1166','nonformal','An audit instruction naming the three checks, with no additional theorem or numerical assertion. The requested checks are carried out in the worked solution and formal components.',[],[]),
   ('1170','proved','The first two actual channel functions coincide with ReLU(s); the third is ReLU(s+1)−1. At−1/2 their values are0 and−1/2. A valid repeated-channel QC for the equal-shift pair is proved for arbitrary two inputs, and a nonnegative weighted sum of individual sector QCs covers all three channels. A concrete unequal-shift pair gives the proposed repeated QC value−3/5, so repetition alone cannot justify that coupling.',theorem_names[:4],hypotheses[:1]),
   ('1172','proved','The true literal hard-IQC model has every finite prefix sum nonnegative while sample1 is−1/4. The finite telescope consumes dissipation and the hard premise on the same complete filter history, preserving terminal storage and V0. Changing the initial previous filter sample changes the example from+1/4 to−1/4, demonstrating why the initial-state premise cannot be discarded. No pointwise IQC sign or general stability convergence theorem is inferred.',theorem_names[4:7],hypotheses[1:2]),
   ('1174','proved','A proven quadratic-form perturbation bounddelta below the original margin gives PosDef of−(M+E), a genuine certificate-preservation result. Conversely, for every sufficiently small positiveepsilon, two scalar weights separated byepsilon change weight²−1 from negative to positive, with exact form change2epsilon. The weight-bound is therefore not assumed to control a general network LMI or preserve its local bounds/equilibrium; the literal valid repair requires either a rechecked changed certificate or an independently established bound.',theorem_names[7:],hypotheses[2:])
  ]
  components=[
   {'clause':'Repetition mismatch, explicit invalid coupled constraint and valid repairs','lean_declarations':theorem_names[:4],'hypotheses':hypotheses[:1],'reason':'The literal function equality/inequality, separating values, genuine pairwise repeated QC and all-channel diagonal QC are checked rather than assumed.','missing_clauses':[]},
   {'clause':'Hard IQC time quantifier and retained filter-history summation','lean_declarations':theorem_names[4:7],'hypotheses':hypotheses[1:2],'reason':'An actual zero-history hard-IQC fixture separates all-prefix positivity from individual sample positivity. The finite telescope is conditional on the true hard premise for the supplied filter history and retains the initial storage.','missing_clauses':[]},
   {'clause':'Matrix perturbation repair and small-update counterexample','lean_declarations':theorem_names[7:],'hypotheses':hypotheses[2:],'reason':'The repair is a genuine strict matrix quadratic-form argument, and the explicit arbitrarily small scalar sign-change fixture refutes certificate reuse based only on numerical update size. Recomputing/rechecking is procedural advice, not an invented theorem about a particular neural weight parametrization.','missing_clauses':[]}
  ]
  limits=['No pointwise nonnegativity is inferred from a hard-IQC sum.','The generic filter-history telescope does not synthesize filter dynamics or establish the hard premise for arbitrary initialization; it uses precisely the stated premises.','The perturbation theorem proves the resulting symmetric matrix is negative definite when the stated bounds hold. No general neural-weight Lipschitz bound, equilibrium preservation, local-domain preservation or controller convergence follows merely from a small numerical update.','The activation-practices import is existing unselected future23 evidence and must be explicitly selected and paired in a later offer; checkpoint22 inclusion is not inferred.']
 by_key={row['key']:row for row in request['material_units']}
 decisions=[]
 for suffix,kind,reason,declarations,unit_hypotheses in specs:
  key='nn-in-the-loop.html::node-'+suffix
  row=by_key[key]
  assert hashlib.sha256(row['source_text'].encode()).hexdigest()==row['text_sha256']
  decisions.append({'source_unit_key':key,'entire_inventory_record':row,'source':row['source'],'source_sha256':row['source_sha256'],'unit_text_sha256':row['text_sha256'],'source_text':row['source_text'],'line':row['line'],'locator':row['locator'],'review_status':'approved_complete_source' if kind=='proved' else 'approved_nonformal_source_scope','material_status':kind,'whole_unit_approved':True,'per_unit_reason':reason,'hypotheses':unit_hypotheses,'lean_declarations':declarations,'missing_clauses':[]})
 assert set(by_key)=={r['source_unit_key'] for r in decisions}
 output=Path(f'/tmp/nn-hard{number}-independent-foundations-whole-source-review23-v1.json')
 assert not output.exists()
 report={'schema_version':1,'status':f'passed_independent_whole_nn_hard{number}_source48_review_future23','reviewer':'/root/config21_next','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'errors':[],'inventory':str(inventory_path.relative_to(ROOT)),'inventory_sha256':inventory_sha,'request':str(request_path),'request_sha256':expected_request_sha,'entire_exercise_inventory_record':request['exercise'],'record':{'exercise_key':request['exercise']['key'],'exercise_text_sha256':request['exercise']['text_sha256'],'source':request['source']['file'],'source_sha256':request['source']['sha256'],'review_status':'approved_complete_source','whole_exercise_approved':True,'independent_whole_source_review_passed':True,'hypotheses':hypotheses,'lean_declarations':theorem_names,'reviewed_components':components,'missing_clauses':[],'per_exercise_reason':'All exact current question, hint and worked-solution clauses were read against the full proof bodies and the actual import definitions. Navigation and procedural/local-domain scope advice are classified explicitly, and the actual conditional mathematical statements match the literal without introducing a general-controller conclusion.'},'material_units':decisions,'proof_source':request['new_source'],'complete_source_body':text,'all_complete_public_theorem_bodies_read':True,'new_public_theorem_count':len(theorem_names),'actual_original_standalone_and_failure_history':snapshots,'failed_actual_command_count':len(failures),'passed_actual_command_count':1,'actual_success_log_empty':True,'protected_import_sources':imports,'protected_all31_current48_assets_and1089_old_plus24_reviewed22_sources_exact':True,'no_current_source_inventory_owner_ledger_or_coverage_offer_writes':True,'canonical_or_named_execution_claimed':False,'selected_in_checkpoint22':False,'coverage_complete':False,'limits':limits+['Whole-literal semantic approval is not a canonical proof-pair binding, source selection, ledger promotion, kernel/axiom aggregate audit or publication.','All failed commands/source snapshots/raw logs and the actual passing EMPTY log remain byte-exact; the request reviewer label is preserved even though the parent assigned this independent reviewer.'],'actual_checker':str(Path(__file__)),'actual_checker_sha256':sha(Path(__file__))}
 for entry in entries:
  for kind in ['actual_record','raw_log','source_snapshot']:assert sha(entry[kind]['file'])==entry[kind]['sha256']
 assert sha(request_path)==expected_request_sha and sha(source_path)==request['new_source']['sha256']
 for p,h in protected.items():assert sha(ROOT/p)==h
 report['records']=[report['record']]
 for component in components:component['approval']='approved_complete_actual_mathematical_source_component'
 with output.open('x') as f:f.write(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
 reports.append({'hard':number,'review':str(output),'sha256':sha(output),'status':report['status'],'units':len(decisions),'public_theorems':len(theorem_names),'whole_exercise_approved':True})
print(json.dumps({'status':'independent_TMP_whole_literal_reviews_completed','reviews':reports}))
