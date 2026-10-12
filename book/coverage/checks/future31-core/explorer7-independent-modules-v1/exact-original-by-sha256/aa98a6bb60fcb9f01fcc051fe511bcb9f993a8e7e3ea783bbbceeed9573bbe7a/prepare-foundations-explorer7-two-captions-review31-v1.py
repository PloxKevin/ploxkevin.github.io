from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re
ROOT=Path('/home/oxrexkevin/SafetyBased');OUT=Path('/tmp/foundations-explorer7-two-captions-review31-v1')
CONTEXT=Path('/tmp/root_tmp_lean_current79_owner30_finalcss_context_v1.json')
assert not OUT.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):
 p=Path(p);return {'file':str(p),'sha256':sha(p),'bytes':p.stat().st_size}
assert sha(CONTEXT)=='73ab502d42458069b9c5a9cfaa9a501c588558493eba0ea635b0a1eb869e6e72'
c=json.loads(CONTEXT.read_bytes());held={**c['pins_sha256'],**c['held_current_source_sha256'],**c['owners_sha256']}
assert all(sha(ROOT/n)==h for n,h in held.items());started=datetime.now(timezone.utc).isoformat()
inventory=ROOT/'book/coverage/inventory-after-correction79.json'
source=ROOT/'book/coverage/checks/future30-core/source66-79-contract-v3/candidate-after-correction70.html'
owner=ROOT/'book/coverage/checks/future30-foundations/current79-completed90-association-v1/foundations30-completed90-current79-pair-bound-candidate-v1.json'
assert sha(inventory)==sha(ROOT/'book/coverage/inventory.json')
assert source.read_bytes()==(ROOT/'SafeLearning/primer-basics.html').read_bytes()
assert owner.read_bytes()==(ROOT/'book/coverage/foundations.json').read_bytes()
inv=json.loads(inventory.read_bytes());raw=json.loads(owner.read_bytes())
keys=['primer-basics.html::node-1437','primer-basics.html::node-1452']
literals={k:next(x for x in inv['material_source_units'] if x['key']==k) for k in keys}
rows=[x for x in raw['material_claims'] if any(k in x['source_unit_keys'] for k in keys)]
assert len(rows)==2 and all(x['status']=='pending' for x in rows)
final=Path('/tmp/CompleteFoundationsExplorerCaptionModels31-draft-v2.lean')
assert sha(final)=='947c84f2460fc96e43dd10713305196285770d8fcd51340a3ce5d4ffbdb6244e'
names=re.findall(r'^theorem\s+(\w+)',final.read_text(),re.M);defs=re.findall(r'^def\s+(\w+)',final.read_text(),re.M)
assert len(names)==7 and len(set(names))==7 and len(defs)==3
history=[];files=[]
for i,code in enumerate([1,0],1):
 p=Path(f'/tmp/foundations-explorer-captions31-owner30-trial{i}.json');d=json.loads(p.read_bytes())
 assert type(d['actual_exit_code']) is int and d['actual_exit_code']==d['actual_runner_exit_code']==code
 assert d['protection_errors']==[]
 assert d['source_sha256_before']==d['source_sha256_after']==d['source_snapshot_sha256']==sha(d['source'])==sha(d['source_snapshot'])
 assert sha(d['raw_log'])==d['raw_log_sha256']
 assert d['actual_command']==['lake','env','lean',d['source']] and d['actual_workdir']==str(ROOT/'verification/lean')
 history.append({'native':ref(p),'source':ref(d['source']),'snapshot':ref(d['source_snapshot']),
  'raw_log':ref(d['raw_log']),'actual_exit_code':code,'started_at_utc':d['started_at_utc'],
  'finished_at_utc':d['finished_at_utc'],'elapsed_seconds':d['elapsed_seconds'],
  'emitted_diagnostic_warning_headers':len(re.findall(r'^.*:\d+:\d+: warning:',Path(d['raw_log']).read_text(),re.M))})
 files += [p,Path(d['source']),Path(d['source_snapshot']),Path(d['raw_log'])]
assert history[-1]['source']['sha256']==sha(final)
OUT.mkdir();aliases={};closed={}
def archive(p):
 p=Path(p);h=sha(p);q=OUT/'originals'/h/p.name;q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists():assert sha(q)==h
 else:q.write_bytes(p.read_bytes())
 aliases[str(p)]=ref(q);closed[str(q)]=h;return ref(q)
selected=[ROOT/'verification/lean/SafeLearning'/n for n in ['CompleteFoundationsBanachModels.lean','CompleteFoundationsGeometricExample.lean']]
primary_names=['Analysis/SpecificLimits/Basic.lean','Algebra/Field/GeomSum.lean',
 'Topology/MetricSpace/Contracting.lean','Logic/Function/Iterate.lean',
 'Topology/MetricSpace/Lipschitz.lean','Order/Filter/AtTopBot/Basic.lean']
primary=[ROOT/'verification/lean/.lake/packages/mathlib/Mathlib'/n for n in primary_names]
js_result=Path('/tmp/foundations-explorer-horizon-exact31-v1/actual-extracted-JS-one-percent-horizons-all200-exact-reference-v1.json')
j=json.loads(js_result.read_bytes())
assert sha(js_result)=='488d22bcda06d23644fe4015546265304743cbc1077c6163f3936e718be53157'
assert j['actual_exit_code']==0 and j['all200_exact_admitted_horizons_verified'] is True
assert j['source']['sha256']==sha(source) and len(j['individual_checks'])==200
js_native=Path('/tmp/foundations-explorer-horizons-exact31-actual-v1.json');jn=json.loads(js_native.read_bytes())
assert type(jn['actual_exit_code']) is int and jn['actual_exit_code']==0 and jn['protection_errors']==[]
js_files=[js_result,js_native,js_native.with_suffix('.log'),
 Path('/tmp/check-foundations-explorer-horizons-exact31-v1.py'),Path('/tmp/run-check-foundations-explorer-horizons-exact31-v1.py'),
 Path(j['raw_stdout']['file']),Path(j['raw_stderr']['file'])]
for p in [CONTEXT,*selected,*primary,*files,*js_files,
 Path('/tmp/CompleteFoundationsExplorerCaptionModels31-draft-v1.lean')]:archive(p)
for p in [inventory,source,owner]:closed[str(p)]=sha(p)
lines=source.read_text().splitlines(keepends=True)
context=''.join(lines[1459:1497]);widget=''.join(lines[1780:1964])
assert 'gamma' not in context or r'\gamma' in context
assert 'var T99 = '+j['actual_source_expression'] in widget
packet={
 'status':'actual_passed7_entire_two_current_explorer_captions_independent_mathematical_review_pending',
 'author':'/root/foundations_recovery28','final_actual_passed_source':aliases[str(final)],
 'public_theorem_count':7,'public_theorem_names':names,'actual_definition_names':defs,
 'current_source':ref(source),'current_inventory':ref(inventory),'current_installed30_foundations_owner':ref(owner),
 'entire_current_literals':literals,'entire_current_pending_rows':rows,
 'full_explorer_context_lines1460_1497':context,'full_explorer_JS_lines1781_1964':widget,
 'context_serialization':'Exact source.splitlines(keepends=True) slices[1459:1497] and[1780:1964].',
 'entire_complete_selected_dependencies':[aliases[str(p)] for p in selected],
 'complete_used_primary_files':{n:aliases[str(p)] for n,p in zip(primary_names,primary)},
 'genuine_original_compiler_histories':history,
 'diagnostic_warning_header_definition':r'^.*:\d+:\d+: warning: counted with MULTILINE; complete raw logs retained.',
 'two_literal_correspondence':{
  keys[0]:{'actual_shifted_Banach_bound':names[5],'actual_cobweb_transitions_and_fixed_diagonal':names[6],
   'domain':'Closed nonempty invariant real subset, actual global Lipschitz factor L<1 there, starting the genuine iterate at k0. The complete Banach theorem derives the fixed point and convergence; neither is assumed.'},
  keys[1]:{'actual_prefix_tail_and_sum':names[0],'actual_positive_limit_fractions':names[1],
   'actual_first_horizon_minimum_and_all_subsequent_guarantee':names[2],
   'actual_zero_discount_edge':names[3],'positive_discount_exact_log_criterion':names[4],
   'domain':'Every real0<=gamma<1, every natural horizon; actual HTML gamma slider0..0.995 includeszero.'}},
 'actual_all200_admitted_slider_horizons_exact_arithmetic_validation':aliases[str(js_result)],
 'actual_all200_validation_native':aliases[str(js_native)],
 'validation_scope':'Actual source-extracted JavaScript expression executed with Node at each of the200 admitted slider values, compared with independent exact Fraction powers at both adjacent horizons. This supplementary finite implementation check is not substituted for the generic Lean minimum theorem or claimed as a new Lean/axiom audit.',
 'visual_scope':'The two captions identify the plotted mathematical quantities and color/line roles. Full current widget formulas/color assignments and invariant-domain notes are supplied. Float-bit equality of the cosine fixed-point approximation is not claimed. No neighboring1453 empirical iterations/cycles/chaos statement is approved by these proofs.',
 'all_original_byte_aliases':aliases,'all_physical_original_inputs_sha256':closed,
 'current1242_finalCSS31_raw30_protection_context':aliases[str(CONTEXT)],
 'prepared_started_at_utc':started,'prepared_finished_at_utc':datetime.now(timezone.utc).isoformat(),
 'requested_individual_current_whole_material_keys':keys,
 'requested_review':'Read every7 full proof/3definitions, both complete selected dependencies and actual used primary bodies, the entire two current captions/pending rows and full actual explorer HTML/JS context. Decide each whole literal independently only if all mathematical domain, zero-discount, shifted-index, visual-role and first-horizon claims are discharged. Treat the actual200 exact arithmetic validation as supplementary implementation evidence, retain every original compiler failure/time and current owner pending rows, and identify any remaining domain/visual gap instead of inferring it from code integrity. No1430parent/1453/other numerical or algorithm/chaos promotion, source correction or current owner/canonical write is requested.',
 'current_whole_approved_by_author':False,'source_or_owner_or_canonical_mutation_performed':False,'coverage_complete':False}
assert all(sha(ROOT/n)==h for n,h in held.items());assert all(sha(p)==h for p,h in closed.items())
p=OUT/'foundations-explorer7-full-source-current1437-1452-two-captions-independent-review-request31-v1.json'
p.write_text(json.dumps(packet,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'request':ref(p),'final_source':ref(final),'native_codes':[x['actual_exit_code'] for x in history],
 'warnings':[x['emitted_diagnostic_warning_headers'] for x in history],'no_current_writes':True}))
