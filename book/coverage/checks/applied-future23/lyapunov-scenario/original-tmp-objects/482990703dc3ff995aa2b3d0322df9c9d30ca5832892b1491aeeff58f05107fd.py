from pathlib import Path
from datetime import datetime, timezone
import sys,hashlib,json
ROOT=Path('/home/oxrexkevin/SafetyBased')
sys.path.insert(0,str(ROOT/'book/coverage'))
from lean_names import declarations
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
ref=lambda p:{'file':str(p),'sha256':sha(p)}
original=Path('/tmp/applied-lyapunov-scenario-validation23-two-source-readiness-v1.json')
assert sha(original)=='68c7eeed2cd3a95407cc85a17c192ec4c1617fb9653cd15f34818717e4229691'
base=json.loads(original.read_text())
source=Path('/tmp/CompleteLyapunovScenarioSupport23.lean')
record=Path('/tmp/applied-lyapunov-scenario-support23-trial2.json')
passed=json.loads(record.read_text());assert passed['actual_exit_code']==0
assert sha(source)==sha(passed['source_file'])==passed['source_sha256_before']==passed['source_sha256_after']=='038615c0dacea25bfb8eb28b4770ac8f523a290ec20e1804f3848194f95ba38d'
assert sha(passed['raw_log_file'])==passed['raw_log_sha256']
assert sha(passed['runner_file'])==passed['runner_sha256']
failed_path=Path('/tmp/applied-lyapunov-scenario-support23-trial1.json')
failed=json.loads(failed_path.read_text());assert failed['actual_exit_code']==1
assert sha(failed['source_file'])==failed['source_sha256_before']==failed['source_sha256_after']
assert sha(failed['raw_log_file'])==failed['raw_log_sha256']
decl=declarations(source.read_text());theorems=[d['name'] for d in decl if d['kind'] in ('theorem','lemma')];assert len(theorems)==9
manifest_path=ROOT/'reports/full-coverage/checkpoint-21-manifest.json';manifest=json.loads(manifest_path.read_text())
for name,row in manifest['proof_files'].items():assert sha(ROOT/name)==row['sha256']
dep='verification/lean/SafeLearning/CompleteFoundationsIndependentTrials.lean'
dep_row=manifest['proof_files'][dep];assert sha(ROOT/dep)==dep_row['sha256']
for name,digest in dep_row['evidence_sha256'].items():assert sha(ROOT/name)==digest
inv=ROOT/base['inventory']['file'];assert sha(inv)==base['inventory']['sha256']
question=base['entire_inventory_record'];assert sha(ROOT/question['source'])==question['source_sha256']
unit=next(u['entire_inventory_record'] for u in base['material_units'] if u['source_unit_key']=='lyapunov-mpc.html::node-1397')
ns='SafeLearning.CompleteLyapunovScenarioSupport23.'
groups=[
 {'component_id':'actual_lower_bound_scalar_linear_scenario_optimizer','lean_declarations':[ns+n for n in ['actual_scalar_scenario_optimizer_is_the_sample_maximum','actual_scalar_scenario_optimizer_is_unique','actual_sample_maximum_is_attained_by_a_sample']],'hypotheses':['Arbitrary nonempty finite sample index set; arbitrary real sampled lower bounds. The actual program minimizes the scalar objective x subject to every sampled inequality s_i≤x.'],'per_component_reason':'The actual feasible set is defined from all sampled constraints. Its attained unique least scalar objective is derived to equal the finite sample maximum; the optimizer and attainment are not assumed.'},
 {'component_id':'actual_at_most_one_supporting_sample_in_this_scalar_program','lean_declarations':[ns+n for n in ['actual_support_constraint_is_a_strict_unique_maximum','actual_strict_unique_maximum_is_a_support_constraint','actual_at_most_one_sample_constraint_is_supporting','actual_support_sample_count_is_at_most_one']],'hypotheses':['A sample is supporting precisely when removing its inequality permits an objective strictly below the original sample maximum.','Arbitrary nonempty finite scalar lower-bound program; tied maxima are allowed.'],'per_component_reason':'Supporting constraints are proved equivalent to strict unique maxima. At most one supports the program; with ties at the maximum no constraint supports it. This is a genuine scalar program result, not a conclusion assumed from the variable count.'},
 {'component_id':'actual_fixed_threshold_missed_region_probability','lean_declarations':[ns+n for n in ['actual_sample_maximum_threshold_event_is_exactly_all_misses','actual_independent_scalar_scenario_threshold_failure_probability']],'hypotheses':['The threshold q is fixed before sampling. There are n>0 real sample coordinates; the events {q<X_i} are measurable, mutually independent, and each has actual probability epsilon in[0,1].'],'per_component_reason':'The event that the actual sample optimizer is at most q is proved equal to missing all fixed strict-upper-tail events. The selected genuine independent-event law derives exact probability (1-epsilon)^n and exponential upperbound. Independence and the actual common event probability are explicit.'}
]
assert set(theorems)==set(n for g in groups for n in g['lean_declarations'])
out=Path('/tmp/applied-lyapunov-scenario-support23-independent-review-request-v1.json')
packet={'status':'genuine_tmp_standalone_zero_scalar_support_supplement_ready_for_independent_component_review','created_at_utc':datetime.now(timezone.utc).isoformat(),'review_request':'Read all nine full bodies, actual scalar program/support definitions and the complete question/answer(a). Classify only explicit components; retain the general scenario theorem, random optimized violation event and original false equality gaps.','original_two_source_packet':ref(original),'original_two_source_packet_created_at_utc':base['created_at_utc'],'original_packet_bytes_and_times_unchanged':True,'inventory':base['inventory'],'exercise_key':base['exercise_key'],'entire_inventory_record':question,'material_units':[{'source_unit_key':unit['key'],'entire_inventory_record':unit,'whole_unit_approved':False,'missing_clauses':['The source states a general one-variable scenario theorem, whereas this supplement proves the actual scalar lower-bound program.','The fixed-threshold tail-miss identity is not a proof that the random scenario optimizer has violation probability above epsilon with probability (1-epsilon)^n for arbitrary convex programs/distributions.','Original logarithm and ratio finite-decimal exact equalities remain false.']}],'proof_source':ref(source),'public_declarations':decl,'public_theorem_count':9,'actual_standalone_record':ref(record),'entire_actual_record':passed,'source_snapshot':ref(passed['source_file']),'raw_log':ref(passed['raw_log_file']),'raw_log_description':'One genuine Set.mem_setOf_eq deprecation warning; actual exit0, log nonempty.','historical_failed_trials':[{'record':ref(failed_path),'entire_original_record':failed,'source_snapshot':ref(failed['source_file']),'raw_log':ref(failed['raw_log_file']),'failure_description':'Original trial1: sup_lt implicit argument mismatch and Ne.symm syntax. Exact failed bytes retained.'}],'components':groups,'selected_dependency':{'source_file':dep,'sha256':sha(ROOT/dep),'entire_selected21_row':dep_row,'evidence_scope':'Retained genuine selected compiler/source evidence for the identical IndependentTrials source; no new dependency execution is claimed.'},'protected_selected_sources':{'manifest':ref(manifest_path),'count':1089,'all_source_hashes_exact':True},'primary_source_correspondence':base['primary_source_correspondence'],'limits':['No whole exercise or source unit promotion.','No general Campi–Garatti scenario theorem, GP posterior construction or validation-until-pass guarantee.','Only a genuine standalone TMP execution; no new named build, aggregate23, canonical input or owner mapping mutation.']}
with out.open('x') as f:f.write(json.dumps(packet,indent=2)+'\n')
print(json.dumps({'status':'prepared','file':str(out),'sha256':sha(out),'public_theorems':9,'source_sha256':sha(source)}))
