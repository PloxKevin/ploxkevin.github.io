from pathlib import Path
import hashlib,json,re
R=Path('/home/oxrexkevin/SafetyBased');B=R/'book/coverage/checks/modules-future30/thermal40-full-scope-v1'
assert not B.exists();B.mkdir(parents=True)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
aliases={}
def copy(p):
 p=Path(p);h=sha(p);q=B/'original-closed-bytes'/h/p.name;q.parent.mkdir(parents=True,exist_ok=True)
 if not q.exists():
  with q.open('xb') as f:f.write(p.read_bytes())
 assert sha(q)==h
 r={'file':q.relative_to(R).as_posix(),'sha256':h,'bytes':q.stat().st_size};aliases[str(p)]=r;return r
S=Path('/tmp/CompleteModulesThermalPenaltyBellmanWhole30-draft-v5.lean')
assert sha(S)=='daf012d3c3430f537e59d3d106ff2941255a94bcf22366dcab94d334b007803e'
t=S.read_text();ns='SafeLearning.CompleteModulesThermalPenaltyBellmanWhole30'
names=re.findall(r'^theorem\s+(\w+)',t,re.M);defs=re.findall(r'^(?:def|abbrev)\s+(\w+)',t,re.M)
assert (len(names),len(defs))==(40,20)
invpath=R/'book/coverage/inventory-after-correction65.json';I=json.loads(invpath.read_bytes())
ownerpath=R/'book/coverage/checks/modules-future29/current65-pair-bound-v7/modules29-current65-two-source-pair-bound-candidate-v1.json'
assert sha(ownerpath)==sha(R/'book/coverage/modules.json')=='13a1955d1920b9eafec20b5b38d7e10800354db71188c154f0967a93bccbc22d'
M=json.loads(ownerpath.read_bytes());exkey='viability.html#book-m7-b2';keys=['viability.html::node-'+str(n) for n in [838,839,864,871,875]]
e=next(r for r in M['exercises'] if r['inventory_key']==exkey);assert e['status']=='partial' and len(e['claims'])==4
rows=[next(r for r in I['material_source_units'] if r['key']==k) for k in keys]
affected=[r for r in M['material_claims'] if set(r.get('source_unit_keys',[]))&set(keys)];assert len(affected)==5
page=R/'SafeLearning/viability.html';assert sha(page)==e['source_sha256']=='0b0a8a5710cd4ce278e30c1c7a5534ba5f4388c7956d60a1e701c02b572490c0'
P=Path('/tmp/modules-thermal-threshold-unnumbered-proposal30-v1/modules-thermal-threshold-unnumbered-full29-proposal30-v1.json')
assert sha(P)=='6f23c3401ddc756c7801d3ed8e830b387a644c475c7ab1efe8b9365a53ff2879';p=json.loads(P.read_bytes())
assert p['fresh_changed_literal_keys']=={'exercises':[exkey],'material_source_units':[keys[-1]]}
for v in p.values():
 if isinstance(v,dict) and {'file','sha256'}<=v.keys():
  z=Path(v['file']);z=z if z.is_absolute() else R/z;assert sha(z)==v['sha256'];copy(z)
pn=Path('/tmp/modules-thermal-threshold-unnumbered-proposal30-preparation-actual-v1.json');a=json.loads(pn.read_bytes());assert a['actual_exit_code']==0 and a['protection_errors']==[]
for z in [P,pn,a['raw_log'],'/tmp/prepare-modules-thermal-threshold-unnumbered-proposal30-v1.py','/tmp/run-modules-thermal-threshold-unnumbered-proposal30-preparation-v1.py']:copy(z)
context={'entire_current_thermal_commissioning_and_B2_lines674_709':''.join(page.read_text().splitlines(keepends=True)[673:709]),
 'entire_current_exercise_inventory_row':next(r for r in I['exercises'] if r['key']==exkey),
 'entire_current_partial_exercise_owner_row':e,'five_entire_current_material_inventory_rows':rows,'five_entire_old_affected_material_claim_rows':affected,
 'entire_prospective_corrected_B2_literal':p['entire_current_and_proposed_literal_records'][exkey]['entire_proposed'],
 'entire_prospective_corrected_node875_literal':p['entire_current_and_proposed_literal_records'][keys[-1]]['entire_proposed']}
C=B/'modules-thermal40-full-current-and-prospective-context-v1.json';C.write_text(json.dumps(context,indent=2,ensure_ascii=False)+'\n')
history=[]
for j in range(1,6):
 z=Path('/tmp/modules-thermal-penalty-bellman-whole30-owner29-trial'+str(j)+'.json');n=json.loads(z.read_bytes())
 assert n['actual_exit_code']==[1,0,1,0,0][j-1] and n['protection_errors']==[] and n['source_unchanged']
 assert n['actual_command']==['lake','env','lean',n['source']] and n['actual_workdir']==str(R/'verification/lean')
 assert sha(n['source'])==n['source_sha256_before']==n['source_sha256_after']==n['source_snapshot_sha256']==sha(n['source_snapshot'])
 assert sha(n['raw_log'])==n['raw_log_sha256'];raw=Path(n['raw_log']).read_text()
 history.append({'actual_native':copy(z),'actual_source':copy(n['source']),'actual_source_snapshot':copy(n['source_snapshot']),
  'actual_raw_log':copy(n['raw_log']),'actual_exit_code':n['actual_exit_code'],
  'actual_warning_count':len(re.findall(r'^.*?:\d+:\d+: warning:',raw,re.M)),
  'original_times':{k:n[k] for k in ['started_at_utc','finished_at_utc','elapsed_seconds']},'original_body_and_times_untouched':True})
assert Path('/tmp/modules-thermal-penalty-bellman-whole30-owner29-trial5.log').read_bytes()==b''
end=b'end SafeLearning.CompleteModulesThermalPenaltyBellmanWhole30\n'
prefixes=[]
for version in [2,4]:
 z=Path('/tmp/CompleteModulesThermalPenaltyBellmanWhole30-draft-v'+str(version)+'.lean');old=z.read_bytes();assert old.endswith(end) and S.read_bytes().startswith(old[:-len(end)])
 prefixes.append({'original':copy(z),'preserved_exact_bytes_through_last_original_theorem':len(old)-len(end),'only_closing_namespace_end_moved_for_append':True})
selected=[copy(R/'verification/lean/SafeLearning'/(name+'.lean')) for name in ['CompleteFoundationsTelescopingApplications','CompleteFoundationsTelescopingModels','CompleteFoundationsLessonSeries','CompleteFoundationsSeries','CompleteModulesBook']]
primary=[]
for name in ['Topology/Order/OrderClosed.lean','Topology/Algebra/InfiniteSum/NatInt.lean','Topology/Algebra/InfiniteSum/Ring.lean','Topology/Algebra/InfiniteSum/Group.lean','Algebra/Order/BigOperators/Group/Finset.lean','Order/Bounds/Basic.lean','Analysis/SpecificLimits/Basic.lean']:
 z=R/'verification/lean/.lake/packages/mathlib/Mathlib'/name
 primary.append({'original_external_package_path_historical_metadata':str(z),'exact_physical_byte_alias':copy(z)})
for z in ['/tmp/root_tmp_lean_current65_owner29_context_v1.json','/tmp/root_tmp_lean_current65_owner29_runner_v1.py',__file__,'/tmp/run-modules-thermal40-full-request30-preparation-v1.py']:copy(z)
d={'status':'prepared_actual_passed_thermal40_full_source_and_literals_for_independent_semantic_review_only',
 'source':copy(S),'source_sha256':sha(S),'public_theorem_count':40,'public_definition_and_abbreviation_count':20,'public_declaration_count':60,
 'public_theorem_names':[ns+'.'+n for n in names],'public_definition_and_abbreviation_names':[ns+'.'+n for n in defs],
 'exercise_keys':[exkey],'material_unit_keys':keys,'entire_current_and_prospective_context':copy(C),'current_page_original_byte_alias':copy(page),
 'original_owner29_candidate':{'file':ownerpath.relative_to(R).as_posix(),'sha256':sha(ownerpath)},
 'current_inventory':{'file':invpath.relative_to(R).as_posix(),'sha256':sha(invpath)},
 'genuine_lean_native_history':history,'earlier_passed_proof_body_prefixes':prefixes,'selected_complete_dependency_sources':selected,'primary_used_API_full_sources':primary,
 'unnumbered_narrow_wording_proposal':copy(P),'actual_narrow_wording_author_parser':copy(pn),
 'full_scope_review_requests':[
  {'scope':'current entire Exercise7.B2 and current node875','whole_scope_expected_pending':True,
   'remaining_gap':'The current worked strict inequality substitutes rounded8.852459 as an exact safe value and gives a threshold strictly above5657/244. Actual exact rational threshold is required before the unchanged approximate23.184426 figure.'},
  {'scope':'prospective corrected entire Exercise7.B2 and corrected node875 conditional on actual later source application',
   'conclusions':['The exact deterministic complete-state thermal model includes all original rewards, the cooling interlock, failure penalty at its actual transition reward time, and absorbing zero future reward.',
    'Finite reward/state value functions give actual summable infinite discounted returns. Genuine finite telescoping and terminal decay prove a Bellman upper bound for every allowed action stream/history, not just stationary policies.',
    'The safe cycle is an actual allowed perpetually viable trajectory and attains its exact infinite return. Both gamma.8 and gamma.9 safe values are IsGreatest over every safe history, and the cooling detour is genuinely inferior.',
    'For nonnegative penalty p, every actual infinite-return optimal first action at58 cools iff p>5657/244. Above threshold the complete cycle value globally bounds and is attained among all allowed histories. Below or at threshold the actual always-run trajectory is a global infinite-return optimum, with a separately proved complete value table.',
    'At the boundary an actual unsafe optimizing trajectory starts58->60->failure and has the same true infinite return as the safe cycle; no tie-breaking safety is assumed.',
    'Penalty24 has exact unsafe return41/5=8.2 below540/61 and every true optimizing first action cools. The actual best safe gamma.9 value5130/271 is greater than the gamma.8 value; its rush-separation threshold23767/2439 is strictly less than5657/244.',
    'Both printed six-decimal safe-value/threshold approximations have strict half-unit rounding proofs. Exact rational threshold is supplied before its approximate decimal in the prospective literal.']},
  {'scope':'current nodes838/839/864/871','conclusions':['Actual gamma.9 infinite safe cycle return5130/271 and rigorous18.929889 rounding, not an assumed arithmetic comparison value.',
    'Safe actions at58/54 are forced, and gamma.9 cooling at56 gives strictly less complete safe value than running; the entire best-safe-return claim is proved.',
    'Actual gamma.9 always-run return25+.9(3-p) follows from a complete true-infinite-return Bellman equality. At penalty5 it is the actual global optimum over every admissible history, equals23.2 and exceeds every safe return.',
    'The current exercise question and hint are fully answered by the actual strict optimal-first-action theorem, p24 instance and unsafe maximizing equality witness.']},
  {'scope':'old partial exercise proved-component gap association; old claims/body/history retained without mutation',
   'associations':[{'claim_id':e['claims'][3]['id'],'old_gap':e['claims'][3]['remaining_gaps'],'mathematical_discharge_requested':True,
    'proposed_actual_support':[ns+'.actual_bellman_upper_bound_bounds_every_history_dependent_return',ns+'.actual_safe_cycle_is_best_over_all_safe_histories8',ns+'.actual_cycle_is_the_attained_optimum_over_every_admissible_history',ns+'.actual_rush_is_the_attained_optimum_below_threshold8',ns+'.actual_all_true_infinite_return_optimal_first_actions_are_safe_iff8',ns+'.actual_boundary_rush_policy_is_an_unsafe_infinite_return_maximizer']}]}],
 'domain_scope':['Deterministic exact transitions, full thermal state, no hidden interlock memory or disturbance, as explicitly supplied by the commissioning source.','Penalties are nonnegative; the strict-threshold sufficient branch itself uses p>5657/244 and hence is positive.','Every actual action stream satisfying the model is covered, including deterministic history-dependent controllers.'],
 'original_closed_byte_aliases':aliases,'required_evidence_artifacts_sha256':{r['file']:r['sha256'] for r in aliases.values()},
 'source_number_reserved':False,'source_applied':False,'canonical_pairs_executed':False,'whole_promotion_performed':False,
 'independent_full_semantic_review_pending':True,'coverage_complete':False,'supplementary_after_frozen29_manifest':True}
for r in [d['original_owner29_candidate'],d['current_inventory']]:d['required_evidence_artifacts_sha256'][r['file']]=r['sha256']
O=B/'modules-thermal40-full-source-literal-independent-review-request30-v1.json';O.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'request':O.relative_to(R).as_posix(),'sha256':sha(O),'bytes':O.stat().st_size,'closed_refs':len(d['required_evidence_artifacts_sha256']),'aliases':len(aliases),'warning_counts':[x['actual_warning_count'] for x in history]}))
