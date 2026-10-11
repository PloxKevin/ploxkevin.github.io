from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,sys,traceback
ROOT=Path('/home/oxrexkevin/SafetyBased');TMP=Path('/tmp');START=datetime.now(timezone.utc).isoformat()
REQUEST=TMP/'modules-nn-two-layer-lft23-full-source-review-request-v1.json'
OUT=TMP/'modules-nn-two-layer-lft23-full-source-independent-foundations-review-v1.json';FAIL=TMP/'modules-nn-two-layer-lft23-independent-foundations-checker-failure-v1.json'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def path(n):return Path(n) if Path(n).is_absolute() else ROOT/n
def ref(p):return {'file':str(p),'sha256':sha(p)}
def check(r):
 p=path(r.get('file',r.get('path')));assert sha(p)==r['sha256'] and not p.is_symlink(),r;return p
def write(p,d):
 with p.open('x') as f:f.write(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
def actual_tmp(p,passed):
 r=read(p);source=path(r['source']);log=path(r['raw_log']);runner=path(r['actual_runner'])
 assert r['actual_command']==['lake','env','lean',str(source)] and r['actual_workdir']==str(ROOT/'verification/lean')
 assert sha(source)==r['source_sha256_before']==r['source_sha256_after'] and sha(log)==r['raw_log_sha256'] and sha(runner)==r['actual_runner_sha256']
 assert (r['actual_exit_code']==0)==passed
 if passed:assert not re.search(r'\berror(?:\(|:)',log.read_text())
 else:assert re.search(r'\berror(?:\(|:)',log.read_text())
 return {'reference':ref(p),'entire_original_actual_record':r,'source_snapshot':ref(source),'entire_original_source':source.read_text(),'raw_log':ref(log),'actual_runner':ref(runner)}
def main():
 assert not OUT.exists() and not FAIL.exists() and sha(REQUEST)=='26058852f2e35ca2f472ae9674453704d1fa9a7d3b81df9a7e645c0ca0ae740d'
 q=read(REQUEST);invpath=ROOT/'book/coverage/inventory-after-correction51.json';assert sha(invpath)==sha(ROOT/'book/coverage/inventory.json')=='d746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41'
 inv=read(invpath);original=read(check(q['current_inventory']));exercise=q['full_original_exercise']
 assert exercise==next(r for r in inv['exercises'] if r['key']==exercise['key'])==next(r for r in original['exercises'] if r['key']==exercise['key'])
 units={r['key']:r for r in inv['material_source_units']};assert len(q['full_physical_source_units'])==6
 for unit in q['full_physical_source_units']:assert units[unit['key']]==unit
 base=check(q['new_actual_source']);body=base.read_text();assert body==q['new_actual_source_body'] and sha(base)=='1704948362aaf26e80d57721223e666c88328a969a5158e1469e9e0ce784c761'
 companion=TMP/'modules-two-layer-lft-consequences23-trial3.lean';assert sha(companion)=='115dfc482ed74d340bccefd3d13a296a5d0bcb783d0602a496e5d5fe3cd115d5';companionbody=companion.read_text()
 ns='SafeLearning.CompleteModulesNNTwoLayerLFT23.';cs='SafeLearning.CompleteModulesNNTwoLayerLFTConsequences23.'
 names=[ns+n for n in re.findall(r'^theorem\s+(\w+)',body,re.M)];extra=[cs+n for n in re.findall(r'^theorem\s+(\w+)',companionbody,re.M)]
 assert len(names)==13 and len(extra)==3 and names==q['new_public_theorem_names']
 actual=[actual_tmp(check(q['actual_standalone_record']),True),actual_tmp(TMP/'modules-two-layer-lft-consequences23-trial3.json',True)]
 failed=[]
 for h in q['actual_failed_histories']:
  for r in h.values():check(r)
  failed.append(actual_tmp(check(h['record']),False))
 failed.extend(actual_tmp(TMP/f'modules-two-layer-lft-consequences23-trial{n}.json',False) for n in [1,2])
 assert actual[0]['raw_log']['sha256']=='e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855'
 log=path(actual[1]['raw_log']['file']).read_text();assert len(re.findall(r'^.*?:\d+:\d+: warning:',log,re.M))==1
 canonical=[]
 for i,label in enumerate(['standalone','named']):
  p=TMP/f'modules-nn-two-layer-lft23-canonical-{label}-actual1.json';r=read(p);source=path(r['source']);snap=path(r['source_snapshot']);log=path(r['log'])
  assert r['actual_exit_code']==0 and source.read_bytes()==base.read_bytes()==snap.read_bytes() and sha(source)==r['source_sha256_before']==r['source_sha256_after']==r['source_snapshot_sha256']
  assert r['command']==(['lake','env','lean','SafeLearning/CompleteModulesNNTwoLayerLFT23.lean'] if i==0 else ['lake','build','SafeLearning.CompleteModulesNNTwoLayerLFT23']) and r['actual_workdir']==str(ROOT/'verification/lean')
  assert sha(log)==r['log_sha256'] and not re.search(r'\berror(?:\(|:)',log.read_text());canonical.append({'reference':ref(p),'entire_original_actual_record':r,'raw_log':ref(log),'source_snapshot':ref(snap)})
 dependency=[]
 for n,r in q['fixed_direct_dependency_proof_rows'].items():
  p=ROOT/n;assert sha(p)==r['sha256'];dependency.append({'reference':ref(p),'entire_direct_dependency_body_read':p.read_text(),'original_requested_proof_row':r})
 contexts=[]
 for c in q['local_primary_contexts']:
  p=check(c['source']);lines=p.read_text().splitlines();assert '\n'.join(lines[c['lines_start']-1:c['lines_end']])==c['exact_lines'];contexts.append(c)
 localhyp=['Arbitrary finite compatible dimensions, real plant/network matrices and biases, arbitrary real activation, and every initial state x; the feed-forward uniqueness theorem assumes no slope or invertibility condition.','Bias cancellation is conditional on an actually attained equilibrium xs=A*xs+B*(W2*seconds+b2); the literal solve-then-shift instruction does not claim that every arbitrary network has an equilibrium.','Matrix dimensions/counts use symmetric storage coordinates and one diagonal multiplier per neuron. Local-sector translation uses the actual chosen interval/domain and offset-sector premise, not an assumed global sector or computed numerical bound.','Common slope/sector bounds are explicit for valid equal-offset repeated-channel constraints. Unequal offsets are allowed; an actual ReLU shifted-channel constraint counterexample establishes that repeated-channel multipliers need not remain valid.']
 reasons={
 1181:('The full question is answered by actual affine maps, the direct homogeneous-coordinate matrix action, exact plant substitution, arbitrary-activation unique layer-forward solution, RV/Rphi actions/dimensions, W0C substitution and equilibrium-conditioned shifting with true local sector translation and unequal-shift QC counterexample.',names+extra),
 1185:('The genuine Matrix.of bias column and Matrix.fromCols/fromBlocks define the exact printed augmented matrix. Its action on(x,w1,w2,1) is proved for every compatible real matrix/vector, giving(u,v1,v2) with all three bias columns.',[ns+'actual_N_maps_are_the_printed_blocks',ns+'actual_affine_LFT_equations',extra[0]]),
 1186:('All zero/W2/W0/W1 blocks are the literal blocks. The actual plant substitution produces Ax+(BW2)w2+Bb2. Nvw has exactly the strict lower-block entries; arbitrary activation gives a constructed unique pair of forward layer outputs for every x, proving well-posedness without an algebraic-loop or slope assumption.',[ns+'actual_block_lower_triangular_entries',ns+'actual_N_maps_are_the_printed_blocks',ns+'actual_affine_LFT_equations',ns+'actual_arbitrary_activation_forward_substitution_is_the_unique_solution',extra[1]]),
 1189:('Actual RV and Rphi multiplication on the stacked state is exactly(x,u) and(v1,v2,w1,w2) in the bias-free setting. The theorem is an actual matrix action for arbitrary compatible dimensions.',[ns+'actual_RV_and_Rphi_actions']),
 1191:('RV and Rphi are defined by the printed zero, identity and W2/W0/W1 blocks. Their true matrix actions prove the entire displayed block matrices and all index placements.',[ns+'actual_RV_and_Rphi_actions']),
 1192:('The typed stability matrix has actual size nx+n1+n2; a genuine symmetric-storage coordinate bijection and cardinal calculation give nx(nx+1)/2+n1+n2 independent variables. The containment matrices are indexed by n1 and have size1+nx. Actual output composition replaces W0 by W0*C. At an attained equilibrium all bias columns cancel in deviations, each shifted neuron has exactly the displayed shifted activation, and local offset-sector inequalities translate iff to centered inequalities on the translated domain. Global common slopes and equal-offset repeated QC are explicit sufficient cases; actual unequal-ReLU-shift QC failure proves that reuse is not generally valid. Solving an equilibrium and computing per-neuron local sectors remain the literal implementation instructions, with those inputs/assumptions explicit; no general optimizer or global stability theorem is asserted.',[ns+'actual_LMI_dimensions_and_independent_parameter_count',ns+'actual_symmetric_storage_coefficients_are_exactly_the_free_unordered_entries',ns+'actual_output_feedback_replaces_first_weight_by_the_matrix_product',ns+'actual_bias_columns_cancel_in_equilibrium_deviations',ns+'actual_shifted_neuron_equation_and_inherited_common_slopes',ns+'actual_equal_offsets_share_the_same_shifted_nonlinearity',ns+'actual_equal_offset_common_slope_group_keeps_the_repeated_qc',ns+'actual_unequal_offsets_can_destroy_a_repeated_nonlinearity',extra[2],'SafeLearning.CompleteModulesNNCertificateAudit23.actual_repeated_constraint_across_unequal_shift_channels_can_fail'])}
 material=[]
 for u in q['full_physical_source_units']:
  number=int(u['key'].split('-')[-1]);reason,declarations=reasons[number]
  material.append({'source_unit_key':u['key'],'entire_inventory_record':u,'whole_unit_approved':True,'material_status':'proved','lean_declarations':declarations,'hypotheses':localhyp,'per_unit_reason':reason,'missing_clauses':[]})
 manifest=read(ROOT/'reports/full-coverage/checkpoint-22-manifest.json');assert len(manifest['proof_files'])==1113
 for n,r in manifest['proof_files'].items():assert sha(ROOT/n)==r['sha256']
 held={n:h for n,h in manifest['working_inputs_sha256'].items() if n in {'book/coverage/core.json','book/coverage/modules.json','book/coverage/applied.json','book/coverage/foundations.json'}}
 for n,h in held.items():assert sha(ROOT/n)==h
 result={'status':'passed_full_two_layer_lft23_exercise_and_six_whole_literals_thirteen_original_plus_three_requested_bridge_bodies','reviewer':'/root/config21_next','started_at_utc':START,'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'actual_checker':ref(Path(__file__)),'errors':[],'original_request':ref(REQUEST),'entire_original_request_body_time':q,'current_inventory':ref(invpath),'original_source50_inventory':q['current_inventory'],'entire_current51_exercise_and_six_records_equal_original50':True,'entire_original_exercise_record':exercise,'whole_exercise_approved':True,'exercise_status':'proved','lean_declarations':names+extra+['SafeLearning.CompleteModulesNNCertificateAudit23.actual_repeated_constraint_across_unequal_shift_channels_can_fail'],'hypotheses':localhyp,'correspondence':reasons[1181][0],'remaining_gaps':[],'material_units':material,'full_source_reviews':[{'source':ref(base),'entire_source_and_all13_bodies':body,'public_declarations':names},{'source':ref(companion),'entire_source_and_all3_bodies':companionbody,'public_declarations':extra}],'actual_two_TMP_passing_records':actual,'all_four_real_failed_trials_and_original_bodies':failed,'original_base_canonical_pair':canonical,'companion_canonical_or_named_execution_inferred':False,'full_direct_dependency_reviews':dependency,'full_original_literal_context_and_primary_remark2_read':contexts,'provisional_three_direct_bridges_then_distinct_companion':{'requested_bridges':['printed homogeneous augmented matrix action','literal plant substitution matrix product','arbitrary local offset-sector iff on the true translated domain'],'original13_source_bytes_unchanged':True,'all_three_direct_bodies_now_passed_and_fully_read':True,'no_original_complete_peer_was_retimed':True},'request_original_inline_preparation_failure_retained':q['preparation_history'],'held22_ledgers_sha256':held,'protected_all1113_selected22_sources_exact':True,'working_HTML_inventory_ledgers_written':False,'coverage_complete':False,'limits':['The whole exercise asks LFT representation, feed-forward well-posedness, matrix dimensions and offset/output-feedback changes. No global controller stability or numerical Algorithm1/SDP optimization theorem is inferred.','Equilibrium attainment and local-sector inputs remain explicit literal instructions/hypotheses. All-initial-state forward uniqueness is genuine for arbitrary activations, with no hidden slope premise.','The base has genuine canonical pair0. The distinct three-body companion currently has genuine TMP standalone0 with one warning; a future named/canonical pair must be separately evidenced before owner selection.','All original failed/passed histories/source bodies/request times and fixed direct dependencies remain unchanged. This review itself does not install an owner mapping or select proof files.']}
 write(OUT,result);print(json.dumps({'status':result['status'],'review':ref(OUT),'whole_units':6,'whole_exercise_approved':True,'new_bodies':16,'companion_scope':'TMP standalone only'}))
if __name__=='__main__':
 try:main()
 except Exception:
  msg=traceback.format_exc()
  if not FAIL.exists():write(FAIL,{'status':'failed','started_at_utc':START,'failed_at_utc':datetime.now(timezone.utc).isoformat(),'actual_checker':ref(Path(__file__)),'failure':msg})
  sys.stderr.write(msg);sys.exit(1)
