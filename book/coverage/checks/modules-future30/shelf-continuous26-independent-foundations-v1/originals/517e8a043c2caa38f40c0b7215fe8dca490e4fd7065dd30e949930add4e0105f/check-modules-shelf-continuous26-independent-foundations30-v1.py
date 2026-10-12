from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,sys
ROOT=Path('/home/oxrexkevin/SafetyBased')
REQUEST=ROOT/'book/coverage/checks/modules-future30/shelf-continuous-control-association-v1/modules-shelf-continuous-control-full-association-and-prospective-whole-composition-review-request30-v1.json'
OUT=Path('/tmp/modules-shelf-continuous26-independent-foundations30-findings-v1.json')
assert not OUT.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def path(q):
 p=Path(q['file']);return p if p.is_absolute() else ROOT/p
def ref(p):return {'file':str(p),'sha256':sha(p),'bytes':Path(p).stat().st_size}
closed={str(REQUEST):sha(REQUEST),str(Path(__file__)):sha(__file__)}
def add(q):
 p=path(q);assert p.is_file() and sha(p)==q['sha256']
 if 'bytes' in q:assert p.stat().st_size==q['bytes']
 if p.is_relative_to(ROOT):assert not p.is_symlink() and p.resolve().is_relative_to(ROOT)
 closed[str(p)]=q['sha256'];return p
assert sha(REQUEST)=='ac9b1a36854e48ae8e59bb7948daa306ac35175314f00ecb1fb447eba60a8d75'
d=json.loads(REQUEST.read_bytes())
for n,h in d['required_evidence_artifacts_sha256'].items():add({'file':n,'sha256':h})
for n,q in d['original_closed_byte_aliases'].items():
 add(q);assert Path(n).is_file() and sha(n)==q['sha256']
source=add(d['source']);body=source.read_text()
assert sha(source)=='b9c8e5c1f0a10e13c30f4e807640d53ed51556c247b32f86a1d6b3bcc7c2f494'
sys.path.insert(0,str(ROOT/'book/coverage'))
import lean_names
closed[str(ROOT/'book/coverage/lean_names.py')]=sha(ROOT/'book/coverage/lean_names.py')
assert not re.search(r'\b(?:sorry|admit|axiom)\b',lean_names.without_comments(body))
decls=lean_names.declarations(body)
names=[x['name'] for x in decls if x['kind'] in ['theorem','lemma']]
other=[x for x in decls if x['kind'] not in ['theorem','lemma']]
assert len(names)==d['actual_public_theorem_count']==26 and names==d['actual_public_theorem_names']
assert len(decls)==d['actual_public_declaration_count']==38 and other==d['actual_public_other_declarations']
assert len(other)==12 and len([x for x in other if x['kind']=='structure'])==1
histories=[]
for row,code,warnings in zip(d['genuine_original_native_history'],[1,1,0],[2,0,0]):
 a=json.loads(add(row['actual_native']).read_bytes());raw=add(row['raw_log'])
 for field in ['actual_exit_code','actual_runner_exit_code']:assert type(a[field]) is int and a[field]==code
 assert row['actual_exit_code']==code and a['status']==('passed_actual_tmp_lean_only' if code==0 else 'failed_actual_tmp_lean_or_protection')
 assert a['actual_command']==['lake','env','lean',a['source']] and a['actual_workdir']==str(ROOT/'verification/lean')
 assert a['protection_errors']==[] and a['source_unchanged'] is True
 assert sha(add(row['source']))==sha(add(row['source_snapshot']))==a['source_sha256_before']==a['source_sha256_after']==a['source_snapshot_sha256']
 assert sha(raw)==a['raw_log_sha256']
 assert len(re.findall(r'^.*:\d+:\d+: warning:',raw.read_text(),re.M))==warnings==row['actual_warning_headers']
 assert row['original_actual_times']=={k:a[k] for k in ['started_at_utc','finished_at_utc','elapsed_seconds']}
 assert [a[k] for k in ['protected_selected29_proof_sources','unchanged_current65_book_assets','unchanged_installed29_live_owners']]==[1197,31,5]
 for key in ['original_actual_runner','actual_source65_installed29_context']:
  q=d['original_closed_byte_aliases'][a[key]['file']];assert q['sha256']==a[key]['sha256'];add(q)
 for key in ['actual_installed29_selection','actual_frozen29_original_audit']:add(a[key])
 assert all(sha(ROOT/n)==h for n,h in a['installed29_owner_sha256'].items())
 histories.append(row)
assert histories[-1]['source']['sha256']==sha(source)
assert not add(histories[-1]['raw_log']).read_bytes()
oldreqpath=add(d['original_shelf57_full_request']);oldpeerpath=add(d['original_shelf57_full_independent_intentional_gap_peer'])
oldpeer=json.loads(oldpeerpath.read_bytes());oldreq=json.loads(oldreqpath.read_bytes())
assert oldpeer['errors']==[] and oldpeer['actual_controller_value_association_gap']==d['original_gap_to_actual_proof_association']['original_peer_gap_exact']
assert 'passed_independent_shelf57' in oldpeer['status']
oldactual=json.loads(add(oldpeer['actual_independent_reader']).read_bytes())
assert oldactual['status']=='passed' and type(oldactual['actual_exit_code']) is int and oldactual['actual_exit_code']==0 and oldactual['protection_errors']==[]
assert d['original_verdict_body_and_time_preserved'] is True
rounding=json.loads(add(d['original_rounding8phrase_independent_peer']).read_bytes())
assert rounding['errors']==[]
context=json.loads(add(d['entire_current_and_prospective_context']).read_bytes())
inv=json.loads(add(d['current_inventory']).read_bytes())
assert (ROOT/'book/coverage/inventory.json').read_bytes()==path(d['current_inventory']).read_bytes()
owner=json.loads(add(d['immutable_original_owner29']).read_bytes())
assert path(d['immutable_original_owner29']).read_bytes()==(ROOT/'book/coverage/modules.json').read_bytes()
assert add(d['current_page_original_byte_alias']).read_bytes()==(ROOT/'SafeLearning/viability.html').read_bytes()
assert context['entire_current_exercise_inventory_row']==next(x for x in inv['exercises'] if x['key']=='viability.html::exercise-17')
for u in context['four_entire_current_material_inventory_rows']:assert u==next(x for x in inv['material_source_units'] if x['key']==u['key'])
keys={u['key'] for u in context['four_entire_current_material_inventory_rows']}
assert context['five_entire_affected_old_owner_material_rows_including_the_prior_proved_component']==[r for r in owner['material_claims'] if any(k in keys for k in r['source_unit_keys'])]
page=(ROOT/'SafeLearning/viability.html').read_text().splitlines(keepends=True)
for field,lo,hi in [('entire_current_exercise_context_lines907_921',907,921),('entire_supplied_shelf_model_context_lines148_166',148,166),('entire_supplied_analytic_threshold_context_lines423_438',423,438)]:assert context[field]==''.join(page[lo-1:hi])
for row in d['entire_primary_API_sources']:add(row['entire_actual_physical_API_source'])
assert all(d[k] is False for k in ['source_ordinal_reserved','source_applied','compiler_or_parser_launched_by_this_preparation','canonical_pairs_executed','whole_promotion_performed','coverage_complete'])
specs=[
 (0,4,'Actual positive-speed travel-time and earliest-wall bound','The finite interval integral and genuine speed alternatives derive x(t)<=x0+v*t for t>=0. Positive v converts this into the strict pre-arrival wall inequality. No desired earliest arrival or value bound is an admissibility field.'),
 (4,9,'Constructed admissible right-driving integral trajectory','The constant-v indicator is interval integrable on every finite interval. Endpoint-null congruence and adjacent interval additivity compute its actual finite integral as v*min(t,reachTime). From x0 in[0,L] and v>0, the continuous trajectory is safe, stops and absorbs atL, with actual admissible velocities.'),
 (9,11,'Genuine positive-time infinite exponential discount','For tau>0 the negative exponential coefficient gives actual IntegrableOn on every Ioi cutoff and its improper tail integral tau*exp(-a/tau). The underlying convergence/complex-to-real proof and integrability route have been read.'),
 (11,15,'Actual safe weighted reward and integrability','Continuous state makes the strict pre-wall set measurable. The actual reward is the indicator of this set times the negative discount. Indicator integrability derives both safe and right-driving integrability, and the constructed wall-hit iff identifies the actual right reward.'),
 (15,17,'Actual infinite right return and every-safe-control bound','The infinite integral is computed as the difference of two genuine exponential tail integrals, with endpoint-null interval equality, including travelTime0. Every supplied safe integral-control path has pre-arrival reward equal to right driving and later reward<=0. Integral monotonicity applies to proved integrable functions and derives the upper bound.'),
 (17,19,'Actual constrained optimum and attained sSup','The constructed right-driving safe control supplies a member of safeReturns at the exact formula, and the preceding every-safe-control inequality bounds the entire set. IsGreatest and its actual sSup equality are conclusions, not premises.'),
 (19,21,'Actual attained ledge infimum and default formula','With L>=0, v>0 and tau>0, the true optimal-value image over[0,L] has a least value at0. Exponential monotonicity proves the lower bound for every initial safe state. IsLeast derives the actual sInf, and the default L1/v1/5 formula is a proved specialization.'),
 (21,23,'Supplied safe controls satisfy printed integral velocity dynamics','The explicit velocity has the actual safe, falling and absorbing branches. On the safe domain it agrees with supplied actual velocity, including the stopped wall; endpoint-null integral congruence derives the printed integral equation. The proof is in this direction for the explicitly specified safe integral-control model, and does not assert generic existence/uniqueness or a converse for every external command representation.'),
 (23,26,'Actual clipped motion, stationary feedback and full travel-distance formula','The actual right trajectory equals min(x0+v*t,L); its command is v before the wall and0 there. It is a genuine stationary safe feedback maximizer. Positive v/tau and x0 in[0,L] derive the full tau*(exp((x0-L)/(v*tau))-1) actual optimal value.')]
groups=[{'scope':label,'public_theorem_names':names[lo:hi],'approved_in_exact_scope':True,'missing_clauses':[],'mathematical_reason':reason} for lo,hi,label,reason in specs]
assert [n for g in groups for n in g['public_theorem_names']]==names
finding={'status':'passed_independent_shelf26_full_continuous_control_association_components_semantic_review','reviewer':'/root/foundations_recovery28','review_finished_at_utc':datetime.now(timezone.utc).isoformat(),'request':ref(REQUEST),'source':ref(source),'public_theorem_count':26,'public_declaration_count':38,'public_theorem_names':names,'other_public_declarations':other,'all26_entire_bodies_12_other_declarations_and_model_fields_read':True,'entire_current_and_prospective_context_read':True,'entire_used_primary_proof_bodies_and_integrability_endpoint_typeclass_scopes_read':True,'primary_full_physical_sources':d['entire_primary_API_sources'],'semantic_scope_determined_by_full_mathematical_read_not_integrity':True,'component_decisions':groups,'actual_model_scope':d['actual_model_scope'],'no_desired_return_value_optimality_or_attainment_premise':True,'actual_safe_control_admissibility_and_absorbing_event_convention_explicit':True,'safe_control_to_printed_integral_dynamics_direction_only':True,'generic_unsafe_controller_optimality_or_discontinuous_ODE_uniqueness_approved':False,'original_shelf57_intentional_semantic_gap_peer':d['original_shelf57_full_independent_intentional_gap_peer'],'original_shelf57_full_request':d['original_shelf57_full_request'],'original_semantic_gap_verdict_and_original_reader_body_time_preserved':True,'original8phrase_narrow_rounding_peer':d['original_rounding8phrase_independent_peer'],'genuine_original_native_history':histories,'genuine_native_codes':[1,1,0],'genuine_warning_header_counts':[2,0,0],'all_original_failure_sources_raws_snapshots_and_native_times_preserved':True,'whole_current1130_or_current_or_prospective_exercise7_3_decision_made_by_this_component_review':False,'whole_composition_reserved_for_separate_Applied_full_literal_review':True,'canonical_or_source_or_owner_or_publication_mutation':False,'compiler_or_parser_launched_by_reviewer':False,'source_ordinal_reserved':False,'source_applied':False,'coverage_complete':False,'prospective_postfreeze_evidence_not_part_of_frozen29':True,'required_evidence_artifacts_sha256':closed,'original_closed_byte_aliases':d['original_closed_byte_aliases'],'errors':[]}
OUT.write_text(json.dumps(finding,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'findings':ref(OUT),'approved_public_components':26,'public_declarations':38,'whole_decision':False,'errors':[]}))
