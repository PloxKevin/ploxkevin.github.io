from pathlib import Path
import json, hashlib, re, shutil
from datetime import datetime, timezone

ROOT=Path('/home/oxrexkevin/SafetyBased')
OUT=Path('/tmp/foundations-residual17-full-review28-v1')
OUT.mkdir(exist_ok=True)
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p):
    p=Path(p)
    if not p.is_absolute(): p=ROOT/p
    return {'file':str(p),'sha256':sha(p)}
def read(p):
    p=Path(p)
    if not p.is_absolute(): p=ROOT/p
    return json.loads(p.read_text())
inv=read('book/coverage/inventory.json')
found=read('book/coverage/foundations.json')
assert sha(ROOT/'book/coverage/inventory.json')=='82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf'
source=Path('/tmp/foundations-residual-weighting-identification27-draft-v4.lean')
assert sha(source)=='371c46ecacd0919b4f9a18394a4dfda4e803e15ca0428f66a3b75031e32d9a7d'
trialpath=Path('/tmp/foundations-residual-weighting-identification28-trial3.json')
trial=read(trialpath)
assert type(trial['actual_exit_code']) is int and trial['actual_exit_code']==0
assert type(trial['actual_runner_exit_code']) is int and trial['actual_runner_exit_code']==0
assert trial['protection_errors']==[] and trial['source_unchanged'] is True
assert sha(Path(trial['raw_log']))==trial['raw_log_sha256']
assert sha(Path(trial['source_snapshot']))==sha(source)
names=re.findall(r'^theorem (\w+)',source.read_text(),re.M)
assert len(names)==17
ns='SafeLearning.CompleteFoundationsResidualWeightingIdentification27.'
def declarations(indices): return [ns+names[n] for n in indices]
keys=['primer-linalg.html::node-'+str(n) for n in [1288,1290,1293]]
units=[u for u in inv['material_source_units'] if u['key'] in keys]
assert len(units)==3
clauses=[
  {'source_unit_key':keys[0],'lean_declarations':declarations([0,1,2,3,4,15]),
   'literal_complete_correspondence':[
       'The source extends the preceding almost-sum 2x2 design [[1,1],[1,1.1]] by the actual direct z2 row [0,1]. rectangularH is exactly that 3x2 design. Column injectivity and actual range finrank2 establish its two-dimensional column space.',
       'For the permitted noisy reading (6,6.2,2.1), three coordinate equations are inconsistent, so y is outside that actual range. This is an existential possibility witness for the printed may, not a claim that every noisy reading is outside the range.',
       'actualResidual is the actual Euclidean measurement vector H z-y. Its squared norm equals the sum of channel squares and has the attained unique printed teaching estimate (261/67,422/201). The existing generic finite-matrix least-squares operator bridge proves attainment/uniqueness for all full-column-rank finite matrices and all readings, so the least-squares claim is not restricted to the fixed numerical estimate.',
       'The distinct estimate (5,2) fits readings (7,7.2,2) exactly; the same readings arise from true (4,2) with nonzero additive sensor error (1,1,0). Hence zero measurement residual need not be zero displacement error. No guarantee about model correctness or physical state is inferred.'
   ],'reused_declarations':[
       'SafeLearning.CompleteFoundationsBook.three_sensor_unique_optimum',
       'SafeLearning.CompleteFoundationsMatrixResidualBridge27.actual_independent_matrix_columns_have_one_attained_unique_least_squares_estimate',
       'SafeLearning.CompleteFoundationsMatrixResidualBridge27.actual_matrix_squared_residual_is_the_generic_loss']},
  {'source_unit_key':keys[1],'lean_declarations':declarations([5,6,7,8,9]),
   'literal_complete_correspondence':[
       'Equal residual weights are the unweighted Euclidean squared norm; comparability of channel errors and appropriateness of weights are modeling guidance, not a theorem that all channels have comparable errors. The generic finite-channel formula proves that scaling row i by scale_i changes its squared-loss coefficient to scale_i squared.',
       'For two channel residuals x and x-2, unweighted x squared+(x-2) squared has unique minimizer1, whereas scaling the first channel by3 gives 9x squared+(x-2) squared with unique minimizer1/5. Both strict cross-criterion inequalities establish an actual changed estimate; no optimal sensor-weight policy is assumed.',
       'For every positive epsilon and state-error target M, delta=epsilon/(2M)>0 gives the actual real two-dimensional diagonal continuous linear map diag(delta,1), with injective action, state vector norm M and residual norm epsilon/2<epsilon. A finite-dimensional square injective linear map is invertible, although the exported theorem explicitly states injectivity. This proves the printed existential small-residual/large-error possibility; delta is allowed to depend on epsilon and M.',
       'Residual size concerns the measurement mismatch; sensitivity additionally concerns the map and its weak direction. The weighting example and quantified weak-map witness establish the mathematical distinctions underlying the remaining decision guidance, without asserting a universal fixed-map error amplification bound.'
   ]},
  {'source_unit_key':keys[2],'lean_declarations':declarations([10,11,12,13,14,16]),
   'literal_complete_correspondence':[
       'sumRow is the actual one-row [1,1] matrix. sumPlus is the actual [1/2,1/2] column. All four real Moore-Penrose identities are proved directly, and any matrix satisfying them is proved equal to sumPlus. Real transpose symmetry is exactly the real Moore-Penrose self-adjoint requirement.',
       'Multiplying the unique Moore-Penrose inverse by the actual reading6 gives vector (3,3). All sum6 Euclidean vectors are exactly (3+t,3-t), and the actual squared norm is18+2t squared.',
       'For every feasible Euclidean x, the norm is at least that of(3,3), with equality exactly at(3,3). A distinct feasible vector(4,2) demonstrates that the measurement itself does not identify equal displacements. The unique estimate uses the explicit minimum-norm criterion; reporting a full family is the alternative descriptive guidance.'
   ],'reused_declarations':[
       'SafeLearning.CompleteFoundationsBook.sum_measurement_all_solutions',
       'SafeLearning.CompleteFoundationsBook.sum_measurement_unique_minimum']}
]
dependencies=[ROOT/'verification/lean/SafeLearning/CompleteFoundationsBook.lean',ROOT/'verification/lean/SafeLearning/CompleteFoundationsSpectralModels.lean',ROOT/'verification/lean/SafeLearning/CompleteFoundationsMatrixResidualOrthogonality27.lean']
rawfiles=[source,trialpath,Path(trial['raw_log']),Path(trial['source_snapshot']),Path(trial['original_actual_runner']['file']),ROOT/'SafeLearning/primer-linalg.html',*dependencies]
prior=[]
for n in [1,2]:
    p=Path('/tmp/foundations-residual-weighting-identification27-trial'+str(n)+'.json')
    t=read(p)
    assert type(t['actual_exit_code']) is int and t['actual_exit_code']==1
    assert t['protection_errors']==[]
    assert sha(Path(t['raw_log']))==t['raw_log_sha256']
    assert sha(Path(t['source_snapshot']))==t['source_snapshot_sha256']
    prior.append({'record':ref(p),'entire_original_record_and_time':t,'entire_raw_log':Path(t['raw_log']).read_text(),'entire_failed_source':Path(t['source_snapshot']).read_text()})
    rawfiles += [p,Path(t['raw_log']),Path(t['source_snapshot']),Path(t['original_actual_runner']['file'])]
aliases={}
for p in dict.fromkeys(rawfiles):
    h=sha(p); target=OUT/'original-closed-bytes'/h/p.name
    target.parent.mkdir(parents=True,exist_ok=True)
    if target.exists(): assert target.read_bytes()==p.read_bytes()
    else: shutil.copyfile(p,target)
    aliases[str(p)]={'file':str(target),'sha256':h}
context=(ROOT/'SafeLearning/primer-linalg.html').read_text().splitlines()
packet={
  'status':'prepared_tmp_actual17_body_three_full_literal_source_review_request',
  'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'author':'/root/foundations_recovery28',
  'current_inventory':ref(ROOT/'book/coverage/inventory.json'),'current_foundations_owner':ref(ROOT/'book/coverage/foundations.json'),
  'current_corrections':ref(ROOT/'book/coverage/material-corrections.json'),
  'proof_source':ref(source),'entire_source':source.read_text(),'public_theorem_count':17,
  'full_source_units':units,'current_existing_claims_unchanged':[c for c in found['material_claims'] if any(k in keys for k in c.get('source_unit_keys',[]))],
  'full_local_teaching_context_lines1333_to1395':'\n'.join(context[1332:1395]),
  'source_unit_correspondences':clauses,
  'full_reused_dependency_sources':[{'source':ref(p),'entire_source':p.read_text()} for p in dependencies],
  'actual_standalone_record':ref(trialpath),'entire_original_actual_record_and_time':trial,
  'raw_log':ref(Path(trial['raw_log'])),'entire_raw_log':Path(trial['raw_log']).read_text(),
  'actual_warning_count':Path(trial['raw_log']).read_text().count(' warning:'),
  'genuine_previous_failed_trials':prior,'original_closed_byte_aliases':aliases,
  'same_literal_source53_to55':[{'key':u['key'],'text_sha256':u['text_sha256']} for u in units],
  'newly_requested_material_units':keys,'separate_already_completed_node1289_not_reopened':True,
  'all_body_author_review_completed':True,'independent_whole_unit_approval':False,
  'canonical_installation_or_aggregate_verification_claimed':False,
  'review_request':'Read all17 full theorem bodies and all definitions, all three unchanged literal units and teaching context, all reused full dependency sources, exact prior failure bodies/times/raw and genuine trial3. Decide every printed clause, including modeling guidance, finite rectangular generic attainment, residual-versus-state distinction, quantified weak-map scope and actual Moore-Penrose action. Approve whole units only if every literal clause has exact correspondence; integrity/native compilation alone is not source correspondence.',
  'scope':'TMP-only actual standalone source and semantic peer request. No live owner/source/proof/coverage/Git changes.'
}
p=OUT/'foundations-residual17-full-review28-v1.json'
assert not p.exists()
p.write_text(json.dumps(packet,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'packet':ref(p),'public_theorem_count':17,'literal_units':3,'original_byte_aliases':len(aliases),'warnings':packet['actual_warning_count'],'actual_exit_code':0}))
