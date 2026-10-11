from pathlib import Path
import datetime,hashlib,json,re,shutil
ROOT=Path('/home/oxrexkevin/SafetyBased')
OUT=Path('/tmp/mpc-shift-domain-audit28-v1')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p):return {'file':str(p),'sha256':sha(p)}
inventory=ROOT/'book/coverage/inventory-after-correction55.json'
assert sha(inventory)=='82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf'
inv=json.loads(inventory.read_text())
source=ROOT/'SafeLearning/lyapunov-mpc.html'
assert sha(source)=='63a1ac8be7f5cf8b490dd1dd872d416affee95f6de0d5ba3c1c618f4b86cd79f'
ex=next(r for r in inv['exercises'] if r['key']=='lyapunov-mpc.html::exercise-18')
keys=['lyapunov-mpc.html::node-'+str(i) for i in [735,737,739,753,755,866,868,1387]]
units=[next(r for r in inv['material_source_units'] if r['key']==k) for k in keys]
original13=Path('/tmp/CompleteCoreMPCFirstSuccessor27-draft-v3.lean')
canonical11=ROOT/'verification/lean/SafeLearning/CompleteCoreMPCFirstSuccessor27.lean'
delta=Path('/tmp/CompleteCoreMPCOrderedMargins28-draft-v1.lean')
assert sha(original13)=='d5f50f0340f1a818a341ddd7fc46091da2f8bc5500e8d29aa5589a4f4a05c398'
assert sha(canonical11)=='09fc59984a9e53f86e8ddfa82b2bee79f163aeffd5dc173b88eb6d8fc9c8000c'
assert original13.read_bytes().startswith(canonical11.read_bytes())
header='import SafeLearning.CompleteCoreMPCFirstSuccessor27\n\nset_option autoImplicit false\nnoncomputable section\n\n'
suffix=original13.read_text()[len(canonical11.read_text()):]
reversed_delta=delta.read_text()[len(header):].replace('SafeLearning.CompleteCoreMPCOrderedMargins28','SafeLearning.CompleteCoreMPCFirstSuccessor27')
assert reversed_delta==suffix
prior=Path('/tmp/root-mpc-first-successor13-two-new-components-independent-applied-review27-v1.json')
assert sha(prior)=='dd3492f4d3c163c4c96aaff158e941b7e1ba79be55cf7552aeffd504162aaff2'
oldgap=Path('/tmp/lyapunov-two-core-exercises26-independent-applied-full-gap-review-v1.json')
drafts=[delta,Path('/tmp/CompleteCoreMPCLocalGeometry28-draft-v1.lean'),Path('/tmp/CompleteCoreMPCShiftedPrediction28-draft-v1.lean'),Path('/tmp/CompleteCoreMPCShiftedPrediction28-draft-v2.lean')]
selected=[canonical11,ROOT/'verification/lean/SafeLearning/CompleteCoreMPCHybridMatrixInfinityInput26.lean',ROOT/'verification/lean/SafeLearning/CompletePredictiveSafety.lean',ROOT/'verification/lean/SafeLearning/CompleteLyapunovExerciseModels.lean',ROOT/'verification/lean/SafeLearning/CompleteAppliedTerminalPlanShift.lean']
originals=[original13,prior,oldgap,*drafts,*selected,Path('/tmp/root-mpc-first-successor27-trial2.json'),Path('/tmp/root-mpc-first-successor27-trial2.log'),Path('/tmp/root-mpc-first-successor27-trial2-source.lean'),Path('/tmp/root-mpc-first-successor27-trial3.json'),Path('/tmp/root-mpc-first-successor27-trial3.log'),Path('/tmp/root-mpc-first-successor27-trial3-source.lean'),Path('/tmp/hertneck-thesis20-primary-v1.pdf'),Path('/tmp/hertneck-thesis20-primary-v1.txt'),Path('/tmp/hertneck-thesis20-primary-download-v1.json'),Path('/tmp/hertneck-thesis20-item-api-v1.json'),Path('/tmp/hertneck-thesis20-bundles-api-v1.json'),Path('/tmp/hertneck-thesis20-bitstreams-api-v1.json'),ROOT/'sources/text/hertneck.txt',inventory,source]
OUT.mkdir(exist_ok=False);aliases={}
for p in originals:
 assert p.is_file(),str(p)
 d=sha(p);target=OUT/'original-closed-bytes'/d/p.name;target.parent.mkdir(parents=True,exist_ok=True)
 if not target.exists():shutil.copyfile(p,target)
 assert sha(target)==d
 aliases[str(p)]=ref(target)
trial2=json.loads(Path('/tmp/root-mpc-first-successor27-trial2.json').read_text());trial3=json.loads(Path('/tmp/root-mpc-first-successor27-trial3.json').read_text())
assert type(trial2['actual_exit_code']) is int and trial2['actual_exit_code']==1
assert type(trial3['actual_exit_code']) is int and trial3['actual_exit_code']==0
assert trial3['raw_log_sha256']==sha(Path('/tmp/root-mpc-first-successor27-trial3.log'))
paper=(ROOT/'sources/text/hertneck.txt').read_text().splitlines();thesis=Path('/tmp/hertneck-thesis20-primary-v1.txt').read_text().splitlines()
record={
 'status':'prepared_tmp_full_current55_mpc_shift_domain_gap_audit_and_uncompiled_components',
 'errors':[],'prepared_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'author':'/root/applied_next','current_inventory':ref(inventory),'source':ref(source),
 'entire_exercise_record':ex,'entire_material_records':units,
 'complete_original_gap_review_body_and_time':json.loads(oldgap.read_text()),
 'original_gap_review':ref(oldgap),
 'original13_component_peer':ref(prior),'entire_original13_peer_body_and_time':json.loads(prior.read_text()),
 'original_two_trial_records_and_times':[trial2,trial3],
 'uncompiled_proof_drafts':[{'source':ref(p),'entire_source':p.read_text(),'public_theorem_count_static_only':len(re.findall(r'^theorem ',p.read_text(),re.M)),'compiler_or_kernel_execution':False} for p in drafts],
 'delta2_exact_original_statement_proof_bytes_preserved':True,
 'duplicate_original11_namespace_selected':False,
 'full_current_source_context_lines499_540':'\n'.join(source.read_text().splitlines()[498:540]),
 'full_current_exercise_context_lines932_956':'\n'.join(source.read_text().splitlines()[931:956]),
 'primary_paper':ref(ROOT/'sources/text/hertneck.txt'),
 'full_primary_paper_problem_assumptions_proof_context_lines78_234':'\n'.join(paper[77:234]),
 'primary_thesis':ref(Path('/tmp/hertneck-thesis20-primary-v1.pdf')),
 'primary_thesis_text':ref(Path('/tmp/hertneck-thesis20-primary-v1.txt')),
 'primary_thesis_proof_context_lines729_1048':'\n'.join(thesis[728:1048]),
 'primary_thesis_numbering_scope':'Thesis Assumptions1/3/4/5 and Theorem7 correspond to paper Assumptions1/2/3/4 and Theorem5 recursive-feasibility portion; thesis uses separate state/input tightening coefficients.',
 'selected_sources_full_bodies_read':[{'source':ref(p),'entire_source':p.read_text()} for p in selected],
 'resolved_scope_clarifications':[
  {'id':'actual_input_erosion_is_in_source735_context','reason':'Current node735 explicitly defines Ut=U⊖W. Node739 gives the polytopic representation. No source-wide missing-erosion error or source correction is asserted; the formal derivation must instantiate this actual linked relation.'},
  {'id':'constant_order_from_genuine_local_pair','reason':'For a nontrivial Euclidean state space the Hx≤1 domain contains an explicit ball about0, continuity of Vδ(·,0,v) and δloc>0 supply a distinct local pair; the actual local lower/upper inequalities then yield cL≤cU. Draft only, not compiled. Zero-dimensional or zero state-row perturbation cases need direct treatment rather than this distinct-pair lemma.'}
 ],
 'remaining_formal_and_domain_gaps':[
  {'id':'tracking_successor_state_domain_before_lower_bound','reason':'The actual kth tracking state must lie in X before applying the local lower quadratic bound. Contraction controls Vδ at the next actual state but the printed lower bound is quantified only over X×X×U; using it to derive that next-state membership is circular. The thesis recursive proof also orders contraction/lower-bound estimation before its constraint calculation. No general output-domain extension or state membership is silently inferred.'},
  {'id':'continuous_tracking_homotopy_not_supplied','reason':'A first-exit argument along a perturbed-input/tracking trajectory would require continuity of the actual feedback-composed successor path. The primary/site Assumption1 states continuity of Vδ in the first state argument but does not state continuity of κ. An arbitrary line segment in successor space is not the actual κ-generated successor family and does not inherit the contraction inequality. This is a proof obligation, not a claim that the original theorem has been refuted.'},
  {'id':'actual_full_horizon_constraints_and_terminal_candidate','reason':'The new draft constructs the actual shifted feedback trajectory from the disturbed initial successor and the old extended plan without feasibility premises. Per-stage state and input bounds, terminal absorption, and a bona fide OriginalFeasiblePrediction for the new horizon remain to be proved from domain-valid contraction and margins.'},
  {'id':'optimizer_and_robust_replanning_recursion','reason':'Once a feasible candidate is constructed, continuous finite-horizon cost and compact original input constraints must establish actual attained optimizers. Robust online recursion and the original robustOneStepCertificate must then be derived; the selected MPC30 source currently takes that certificate as a premise.'},
  {'id':'whole_exercise18_probability_composition','reason':'Whole Exercise18 remains pending until the true generic robust certificate is derived and composed with the genuine fixed IID/retraining validation and switched finite-entry/terminal-matrix result. The existing scalar plan-shift and scalar tube sources are limited models and do not supply this generic certificate.'}
 ],
 'constructor_plan':[
  'Extend the old feasible plan by its actual terminal controller step; terminal invariance at zero disturbance supplies the final nominal pair and reference input domains.',
  'Use actual Ut⊖W and the old first input to prove both ordinary and perturbed input admissibility; apply input∞ Lipschitz to get the Euclidean first successor radius.',
  'Derive cL≤cU from a genuine distinct local pair or handle the degenerate state/radius case directly; apply the exact epsilon formula and state margin to establish the first successor in X before local bootstrap.',
  'Generate y0 from the actual disturbed plant and generate every y(j+1) from f(yj,κ(yj,z(j+1),v(j+1))); derive input-row membership before each contraction.',
  'Resolve the original-domain successor step explicitly. Only afterward use the output lower bound, geometric tightening increment, and terminal disturbance ball to construct the next feasible plan.',
  'Prove attained optimal-plan existence and recursive feasibility, then apply the existing actual finite-entry matrix safety/convergence and genuine validation composition.'
 ],
 'whole_exercise18_approved':False,'whole_material_units_approved':False,
 'new_kernel_or_canonical_execution_claimed':False,'current27_cutoff_changed':False,
 'original_closed_byte_aliases':aliases,
 'scope':'TMP-only fresh source/proof analysis and uncompiled draft preparation. Preserve every original trial/review body/time. No current source/owner/proof/selection/PUB/Git mutation and no compiler or whole promotion.'}
p=OUT/'mpc-shift-domain-audit28-v1.json'
with p.open('x') as f:f.write(json.dumps(record,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'file':str(p),'sha256':sha(p),'original_copies':len(aliases),'compiler_executed':False,'whole_exercise_approved':False}))
