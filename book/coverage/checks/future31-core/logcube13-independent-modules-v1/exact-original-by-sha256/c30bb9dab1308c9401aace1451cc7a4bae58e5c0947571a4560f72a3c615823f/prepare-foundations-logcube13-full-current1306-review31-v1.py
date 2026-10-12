from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re
ROOT=Path('/home/oxrexkevin/SafetyBased')
OUT=Path('/tmp/foundations-logcube13-full-current1306-review31-v1')
CONTEXT=Path('/tmp/root_tmp_lean_current79_owner30_finalcss_context_v1.json')
assert not OUT.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):
 p=Path(p);return {'file':str(p),'sha256':sha(p),'bytes':p.stat().st_size}
assert sha(CONTEXT)=='73ab502d42458069b9c5a9cfaa9a501c588558493eba0ea635b0a1eb869e6e72'
c=json.loads(CONTEXT.read_bytes())
held={**c['pins_sha256'],**c['held_current_source_sha256'],**c['owners_sha256']}
assert all(sha(ROOT/n)==h for n,h in held.items())
started=datetime.now(timezone.utc).isoformat()
inventory=ROOT/'book/coverage/inventory-after-correction79.json'
assert sha(inventory)==sha(ROOT/'book/coverage/inventory.json')
source=ROOT/'book/coverage/checks/future30-core/source66-79-contract-v3/candidate-after-correction70.html'
assert source.read_bytes()==(ROOT/'SafeLearning/primer-basics.html').read_bytes()
owner=ROOT/'book/coverage/checks/future30-foundations/current79-completed90-association-v1/foundations30-completed90-current79-pair-bound-candidate-v1.json'
assert owner.read_bytes()==(ROOT/'book/coverage/foundations.json').read_bytes()
inv=json.loads(inventory.read_bytes());raw=json.loads(owner.read_bytes())
key='primer-basics.html::node-1306'
literal=next(x for x in inv['material_source_units'] if x['key']==key)
rows=[x for x in raw['material_claims'] if key in x['source_unit_keys']]
assert len(rows)==1 and rows[0]['status']=='pending'
assert literal['text_sha256']==rows[0]['source_text_sha256']=='d18310ae8c08388bd1eace83c2bc1e4235055f853c0e75d015e62a0cdbaffec9'
final=Path('/tmp/CompleteFoundationsLogCubeCrossover31-draft-v8.lean')
assert sha(final)=='bedf2c17fe5a780e8272b0cfab0221cfda41e5f8618e7e0223d6dc0f59c9a3bc'
assert final.read_bytes().startswith(Path('/tmp/CompleteFoundationsLogCubeCrossover31-draft-v7.lean').read_bytes())
names=re.findall(r'^theorem\s+(\w+)',final.read_text(),re.M)
defs=re.findall(r'^def\s+(\w+)',final.read_text(),re.M)
assert len(names)==13 and len(set(names))==13 and defs==['cubeRootRatio']
histories=[];files=[]
for i,code in enumerate([1,1,1,1,0,0],1):
 p=Path(f'/tmp/foundations-logcube1306-owner30-trial{i}.json');d=json.loads(p.read_bytes())
 assert type(d['actual_exit_code']) is int and d['actual_exit_code']==d['actual_runner_exit_code']==code
 assert d['protection_errors']==[]
 assert d['source_sha256_before']==d['source_sha256_after']==d['source_snapshot_sha256']==sha(d['source'])==sha(d['source_snapshot'])
 assert sha(d['raw_log'])==d['raw_log_sha256']
 assert d['actual_command']==['lake','env','lean',d['source']]
 assert d['actual_workdir']==str(ROOT/'verification/lean')
 warnings=len(re.findall(r'^.*:\d+:\d+: warning:',Path(d['raw_log']).read_text(),re.M))
 histories.append({'native':ref(p),'source':ref(d['source']),'snapshot':ref(d['source_snapshot']),
  'raw_log':ref(d['raw_log']),'actual_exit_code':code,'started_at_utc':d['started_at_utc'],
  'finished_at_utc':d['finished_at_utc'],'elapsed_seconds':d['elapsed_seconds'],
  'emitted_diagnostic_warning_headers':warnings})
 files += [p,Path(d['source']),Path(d['source_snapshot']),Path(d['raw_log'])]
assert histories[-1]['source']['sha256']==sha(final)
OUT.mkdir();aliases={};closed={}
def archive(p):
 p=Path(p);h=sha(p);q=OUT/'originals'/h/p.name;q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists():assert sha(q)==h
 else:q.write_bytes(p.read_bytes())
 aliases[str(p)]=ref(q);closed[str(q)]=h;return ref(q)
selected=ROOT/'verification/lean/SafeLearning/CompleteFoundationsRatesCosts.lean'
primary_names=[
 'Analysis/Asymptotics/Defs.lean','Analysis/Asymptotics/Basic.lean','Analysis/Asymptotics/Lemmas.lean',
 'Analysis/SpecialFunctions/Pow/Asymptotics.lean','Analysis/SpecialFunctions/Pow/Real.lean',
 'Analysis/SpecialFunctions/Log/Basic.lean','Analysis/SpecialFunctions/Log/Deriv.lean',
 'Analysis/Real/Sqrt.lean','Analysis/SpecialFunctions/Sqrt.lean',
 'Analysis/Complex/ExponentialBounds.lean','Analysis/Calculus/Deriv/Pow.lean',
 'Analysis/Calculus/Deriv/Mul.lean','Analysis/Calculus/Deriv/MeanValue.lean',
 'Topology/Order/IntermediateValue.lean']
primary=[ROOT/'verification/lean/.lake/packages/mathlib/Mathlib'/n for n in primary_names]
for p in [CONTEXT,selected,*files,*primary,
 *[Path(f'/tmp/CompleteFoundationsLogCubeCrossover31-draft-v{i}.lean') for i in range(1,9)]]:archive(p)
for p in [inventory,source,owner]:closed[str(p)]=sha(p)
context=''.join(source.read_text().splitlines(keepends=True)[1337:1388])
assert literal['source_text'].split(':')[0].startswith('Comparing rates.')
clauses={
 'exact_log_cube_little_o_square_root':names[0],
 'exact_square_root_over_two_thirds_ratio_limit':names[1],
 'actual_derivative_without_asymptotic_interval_premise':names[2],
 'actual_increasing_branch_until_exp_six':names[3],
 'actual_decreasing_branch_after_exp_six':names[4],
 'exact_log_endpoint_decomposition_and_certified_log_bounds':names[5],
 'strict_comparison_at_four_and_twenty_four_million':names[6],
 'every_real_budget_from_four_to_twenty_four_million_strict_comparison':names[7],
 'exact_square_root_little_o_two_thirds_power':names[8],
 'strict_reverse_comparison_at_twenty_four_and_a_half_million':names[9],
 'strict_ratio_decrease_after_twenty_four_million':names[10],
 'unique_upper_crossover_in_exact_twenty_four_to_twenty_four_and_a_half_million_bracket':names[11],
 'little_o_permits_arbitrary_value_at_any_prescribed_finite_budget':names[12]}
packet={
 'status':'genuine_passed13_full_current1306_literal_independent_whole_mathematical_review_pending',
 'author':'/root/foundations_recovery28','final_actual_passed_source':aliases[str(final)],
 'public_theorem_count':13,'public_theorem_names':names,'actual_definition_names':defs,
 'current_source':ref(source),'live_source_byte_alias':{'file':'SafeLearning/primer-basics.html','sha256':sha(source)},
 'current_inventory':ref(inventory),'current_installed30_foundations_owner':ref(owner),
 'entire_current_literal':literal,'entire_current_pending_rows':rows,
 'full_context_lines1338_1388':context,
 'context_serialization':'Exact concatenation of source.splitlines(keepends=True)[1337:1388].',
 'full13_exact_literal_correspondence':clauses,
 'entire_complete_selected_dependency':aliases[str(selected)],
 'complete_used_primary_files':{n:aliases[str(p)] for n,p in zip(primary_names,primary)},
 'genuine_original_compiler_histories':histories,
 'actual13_retains_entire_passed12_bytes_plus_finite_point_asymptotic_limitation_proof':True,
 'diagnostic_warning_header_definition':r'^.*:\d+:\d+: warning: counted with MULTILINE; all entire raw logs retained.',
 'final_actual_raw_EMPTY_and_no_emitted_warning_headers':Path(histories[-1]['raw_log']['file']).read_bytes()==b'',
 'all_original_byte_aliases':aliases,'all_physical_original_inputs_sha256':closed,
 'current1242_finalCSS31_raw30_protection_context':aliases[str(CONTEXT)],
 'prepared_started_at_utc':started,'prepared_finished_at_utc':datetime.now(timezone.utc).isoformat(),
 'requested_current_whole_material_key':key,
 'requested_review':'Read all13 bodies/definition, full selected RatesCosts dependency, used primary proof-body chains, complete current1306 and stated context, all genuine original sources/native/raw/snapshot/times. Decide entire1306 only if both exact little-o clauses, every real T in the finite interval, the printed approximate upper crossover and the no-fixed-budget-consequence explanation are fully discharged. The approximation is supported by the unique upper crossover bracket24M..24.5M and strict endpoint inequalities, not an unproved floating value. No1308/1325/rate-table/curricular/algorithm attribution promotion, source correction, canonical installation or runtime aggregate is requested.',
 'current_whole_approved_by_author':False,'source_correction_or_owner_mutation_performed':False,
 'canonical_installation_or_new_aggregate_claimed':False,'coverage_complete':False}
assert all(sha(ROOT/n)==h for n,h in held.items())
assert all(sha(p)==h for p,h in closed.items())
target=OUT/'foundations-logcube13-full-source-entire-current1306-whole-independent-review-request31-v1.json'
target.write_text(json.dumps(packet,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'request':ref(target),'source':ref(final),
 'native_codes':[h['actual_exit_code'] for h in histories],
 'warnings':[h['emitted_diagnostic_warning_headers'] for h in histories],
 'no_current_writes':True}))
