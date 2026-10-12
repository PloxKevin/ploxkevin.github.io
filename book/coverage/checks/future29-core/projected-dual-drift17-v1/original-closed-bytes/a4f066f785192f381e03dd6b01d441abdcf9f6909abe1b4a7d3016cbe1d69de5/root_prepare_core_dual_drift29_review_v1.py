from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,importlib.util
ROOT=Path('/home/oxrexkevin/SafetyBased');DEST=ROOT/'book/coverage/checks/future29-core/projected-dual-drift17-v1'
SELF=Path(__file__);SOURCE=Path('/tmp/CompleteCoreProjectedDualDrift29-draft-v5.lean')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p):return {'file':str(p.relative_to(ROOT)),'sha256':sha(p)}
assert not DEST.exists();DEST.mkdir(parents=True)
originals={}
paths=[SELF,SOURCE,Path('/tmp/root_tmp_lean_current60_owner28_runner_v1.py'),Path('/tmp/root_tmp_lean_current60_owner28_context_v1.json')]
for i in range(1,6):
 record=Path(f'/tmp/root-core-projected-dual-drift29-trial{i}.json');d=json.loads(record.read_bytes())
 assert d['actual_exit_code']==[1,0,0,1,0][i-1] and d['actual_runner_exit_code']==[1,0,0,1,0][i-1] and d['protection_errors']==[]
 assert d['source_sha256_before']==d['source_sha256_after']==d['source_snapshot_sha256']
 assert sha(Path(d['source_snapshot']))==d['source_snapshot_sha256'] and sha(Path(d['raw_log']))==d['raw_log_sha256']
 paths.extend([record,Path(d['source_snapshot']),Path(d['raw_log']),Path(d['source'])])
for p in dict.fromkeys(paths):
 h=sha(p);t=DEST/'original-closed-bytes'/h/p.name;t.parent.mkdir(parents=True,exist_ok=True)
 with t.open('xb') as f:f.write(p.read_bytes())
 assert sha(t)==h;originals[str(p)]=ref(t)
spec=importlib.util.spec_from_file_location('actual_names',ROOT/'book/coverage/lean_names.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
decls=module.declarations(SOURCE.read_text());assert len(decls)==17 and sum(d['kind'] in ['theorem','lemma'] for d in decls)==12
core=json.loads((ROOT/'book/coverage/core.json').read_bytes())
literals=[]
for r in core['material_claims']:
 if any(k in ['cmdp.html::node-749','cmdp.html::node-750','cmdp.html::node-752'] for k in r['source_unit_keys']):literals.append(r)
assert len(literals)==3
request={'status':'full_precise_projected_dual_drift17_semantic_review_request','prepared_at_utc':datetime.now(timezone.utc).isoformat(),
 'final_actual_source':originals[str(SOURCE)],'source_level_public_names':decls,
 'exact_original_tmp_receipts_sources_logs_and_helpers':originals,
 'literal_units':literals,
 'current_root_references':{str(ROOT/n):ref(ROOT/n) for n in ['book/coverage/core.json','book/coverage/inventory.json','book/coverage/material-corrections.json','reports/full-coverage/checkpoint-28-selection.json','reports/full-coverage/checkpoint-28-manifest.json','reports/full-coverage/lean-checkpoint-28/verification-original.json']},
 'components_requested':[
 {'id':'actual-entrywise-epoch-update','names':['step','multiplier','epochViolation','actual_epoch_coordinate_formula','actual_projected_dual_cumulative_deficit'],'scope':'Exact finite epoch equation 749 and deterministic projected-update cumulative deficit. T=0 is algebraically allowed by total inverse; the operational epoch bound uses T>0. The actual reward sequence is arbitrary with all finite coordinates.'},
 {'id':'actual-violation-norm-dimension-factor','names':['actual_euclidean_energy_identity','actual_euclidean_violation_bound','actual_scalar_violation_bounds_require_the_dimension_factor','actual_bounded_epoch_average'],'scope':'Actual Euclidean, not Pi infinity, violation bound implies sum of squares bound on actual epoch average. Componentwise B gives m*B^2. No random epoch unbiasedness or confidence assumed.'},
 {'id':'actual-finite-horizon-energy-complementarity','names':['projected_scalar_square_bound','actual_projected_step_energy_bound','actual_all_multiplier_coordinates_nonnegative','actual_energy_telescope','actual_finite_horizon_complementary_slackness'],'scope':'Actual max projection squared energy, telescope and finite-N pathwise complementary slackness. No integrals, conditional expectation or a.s feasibility inference.'},
 {'id':'actual-slater-maximizer-drift-algebra','names':['actual_slater_maximizer_pairing_drift'],'scope':'Exact maximizer Lagrangian comparison plus primitive reward upper bound, coordinate nonnegative multipliers and Slater margin derive inner-product drift. gChosen is actual chosen long-run value violation; translating sampled epoch values needs actual A3 and remains pending.'}],
 'whole_unit_request_only':'cmdp.html::node-749',
 'whole_generic_theorem_750_752_or_exercise21_claimed':False,
 'primary_source':{'url':'https://arxiv.org/pdf/2102.11941','version':'arXiv2102.11941v2 2023-09-21','scope':'Original Theorem1 and AppendixI finite energy, complementary-slackness and Slater algebra; full probability theorem is still pending.'},
 'limits':['No selected source/canonical cache/aggregate/owner/source60 mutation.','Raw five trials and warning text preserve their actual original bodies, commands, cwd, times and status.','Full stochastic execution theorem, tail moment control and fixed-price selector path realization remain pending.'],
 'coverage_complete':False}
p=DEST/'core-projected-dual-drift17-full-semantic-review-request29-v1.json'
with p.open('xb') as f:f.write((json.dumps(request,indent=2)+'\n').encode())
print(json.dumps({'status':request['status'],'request':ref(p),'declarations':len(decls),'theorems':12,'originals':len(originals),'coverage_complete':False}))
