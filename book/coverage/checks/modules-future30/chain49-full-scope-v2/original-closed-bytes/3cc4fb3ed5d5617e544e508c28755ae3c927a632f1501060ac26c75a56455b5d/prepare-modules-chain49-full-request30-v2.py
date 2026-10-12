from pathlib import Path
import hashlib,json,re
R=Path('/home/oxrexkevin/SafetyBased');B=R/'book/coverage/checks/modules-future30/chain49-full-scope-v2'
assert not B.exists();B.mkdir(parents=True)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
aliases={}
def copy(p):
 p=Path(p);h=sha(p);q=B/'original-closed-bytes'/h/p.name;q.parent.mkdir(parents=True,exist_ok=True)
 if not q.exists():
  with q.open('xb') as f:f.write(p.read_bytes())
 assert sha(q)==h
 r={'file':q.relative_to(R).as_posix(),'sha256':h,'bytes':q.stat().st_size};aliases[str(p)]=r;return r
S=Path('/tmp/CompleteModulesChainPenaltyWhole30-draft-v6.lean')
assert sha(S)=='c8957f6d83ae4c71bc8083ab35848387a5768e1b961420179d5d4752e408d21f'
t=S.read_text();ns='SafeLearning.CompleteModulesChainPenaltyWhole30'
names=re.findall(r'^theorem\s+(\w+)',t,re.M);defs=re.findall(r'^(?:def|abbrev)\s+(\w+)',t,re.M)
assert (len(names),len(defs))==(49,23)
invpath=R/'book/coverage/inventory-after-correction65.json';I=json.loads(invpath.read_bytes())
assert sha(invpath)=='5f68ee3c68c1da1275a0a2667fe43b42263b8fc31800a834371de5bfbed01b68'
ownerpath=R/'book/coverage/checks/modules-future29/current65-pair-bound-v7/modules29-current65-two-source-pair-bound-candidate-v1.json'
assert sha(ownerpath)==sha(R/'book/coverage/modules.json')=='13a1955d1920b9eafec20b5b38d7e10800354db71188c154f0967a93bccbc22d'
M=json.loads(ownerpath.read_bytes());exkey='viability.html::exercise-18';keys=['viability.html::node-'+str(n) for n in [1135,1139,1141,1143,1144]]
e=next(r for r in M['exercises'] if r['inventory_key']==exkey);assert e['status']=='pending' and len(e['claims'])==10
rows=[next(r for r in I['material_source_units'] if r['key']==k) for k in keys]
affected=[r for r in M['material_claims'] if set(r.get('source_unit_keys',[]))&set(keys)];assert len(affected)==6 and sum(r['status']=='pending' for r in affected)==5
page=R/'SafeLearning/viability.html';assert sha(page)==e['source_sha256']=='0b0a8a5710cd4ce278e30c1c7a5534ba5f4388c7956d60a1e701c02b572490c0'
P=Path('/tmp/modules-chain-long-horizon-value-unnumbered-proposal30-v1/modules-chain-long-horizon-value-unnumbered-full29-proposal30-v1.json')
assert sha(P)=='d843a0f57ead24bb17b87d86f512c05d2c23d05495c5d3f591650d925a5614d6';p=json.loads(P.read_bytes())
assert p['fresh_changed_literal_keys']=={'exercises':[exkey],'material_source_units':[keys[-1]]}
for v in p.values():
 if isinstance(v,dict) and {'file','sha256'}<=v.keys():
  z=Path(v['file']);z=z if z.is_absolute() else R/z;assert sha(z)==v['sha256'];copy(z)
pn=Path('/tmp/modules-chain-long-horizon-value-unnumbered-proposal30-preparation-actual-v1.json');a=json.loads(pn.read_bytes());assert a['actual_exit_code']==0 and a['protection_errors']==[]
for z in [P,pn,a['raw_log'],'/tmp/prepare-modules-chain-long-horizon-value-unnumbered-proposal30-v1.py','/tmp/run-modules-chain-long-horizon-value-unnumbered-proposal30-preparation-v1.py']:copy(z)
context={'entire_current_chain_exercise_context_lines919_940':''.join(page.read_text().splitlines(keepends=True)[918:940]),
 'entire_current_exercise_inventory_row':next(r for r in I['exercises'] if r['key']==exkey),
 'entire_original_pending_exercise_owner_row':e,'five_entire_current_material_inventory_rows':rows,'six_entire_old_affected_material_claim_rows_including_existing_proved_component':affected,
 'entire_prospective_corrected_exercise_literal':p['entire_current_and_proposed_literal_records'][exkey]['entire_proposed'],
 'entire_prospective_corrected_node1144_literal':p['entire_current_and_proposed_literal_records'][keys[-1]]['entire_proposed'],
 'entire_current_reward_bound_and_theorem2_context_lines299_405':''.join(page.read_text().splitlines(keepends=True)[298:405])}
C=B/'modules-chain49-full-current-and-prospective-context-v1.json';C.write_text(json.dumps(context,indent=2,ensure_ascii=False)+'\n')
history=[]
for j in range(1,7):
 z=Path('/tmp/modules-chain-penalty-whole30-owner29-trial'+str(j)+'.json');n=json.loads(z.read_bytes())
 assert n['actual_exit_code']==[1,1,1,1,0,0][j-1] and n['protection_errors']==[] and n['source_unchanged']
 assert n['actual_command']==['lake','env','lean',n['source']] and n['actual_workdir']==str(R/'verification/lean')
 assert sha(n['source'])==n['source_sha256_before']==n['source_sha256_after']==n['source_snapshot_sha256']==sha(n['source_snapshot'])
 assert sha(n['raw_log'])==n['raw_log_sha256'];raw=Path(n['raw_log']).read_text()
 history.append({'actual_native':copy(z),'actual_source':copy(n['source']),'actual_source_snapshot':copy(n['source_snapshot']),
  'actual_raw_log':copy(n['raw_log']),'actual_exit_code':n['actual_exit_code'],
  'actual_warning_count':len(re.findall(r'^.*?:\d+:\d+: warning:',raw,re.M)),
  'original_times':{k:n[k] for k in ['started_at_utc','finished_at_utc','elapsed_seconds']},'original_body_and_times_untouched':True})
end=b'end SafeLearning.CompleteModulesChainPenaltyWhole30\n';old=Path('/tmp/CompleteModulesChainPenaltyWhole30-draft-v5.lean').read_bytes()
assert old.endswith(end) and S.read_bytes().startswith(old[:-len(end)])
prefix={'original':copy('/tmp/CompleteModulesChainPenaltyWhole30-draft-v5.lean'),'preserved_exact_bytes_through_last_original_theorem':len(old)-len(end),'only_closing_namespace_end_moved_for_append':True}
thermal=Path('/tmp/CompleteModulesThermalPenaltyBellmanWhole30-draft-v5.lean')
generic=t[t.index('section GenuineInfiniteDiscountedReturns'):t.index('end GenuineInfiniteDiscountedReturns')+len('end GenuineInfiniteDiscountedReturns')]
other=thermal.read_text();tg=other[other.index('section GenuineInfiniteDiscountedReturns'):other.index('end GenuineInfiniteDiscountedReturns')+len('end GenuineInfiniteDiscountedReturns')]
assert generic.replace('  ≤  ',' ≤ ')==tg
selected=[copy(R/'verification/lean/SafeLearning'/(name+'.lean')) for name in ['CompleteFoundationsTelescopingApplications','CompleteFoundationsTelescopingModels','CompleteFoundationsLessonSeries','CompleteFoundationsSeries','CompleteModulesBook']]
primary=[]
for name in ['Topology/Order/OrderClosed.lean','Topology/Algebra/InfiniteSum/NatInt.lean','Topology/Algebra/InfiniteSum/Ring.lean','Topology/Algebra/InfiniteSum/Group.lean','Algebra/Order/BigOperators/Group/Finset.lean','Order/Bounds/Basic.lean','Analysis/SpecificLimits/Basic.lean']:
 z=R/'verification/lean/.lake/packages/mathlib/Mathlib'/name
 primary.append({'original_external_package_path_historical_metadata':str(z),'exact_physical_byte_alias':copy(z)})
for z in ['/tmp/root_tmp_lean_current65_owner29_context_v1.json','/tmp/root_tmp_lean_current65_owner29_runner_v1.py',__file__,'/tmp/run-modules-chain49-full-request30-preparation-v2.py']:copy(z)
paper=[]
for z,h in [('/tmp/applied-safe-value-functions-v4-primary27.pdf','76b2dc286779cca3de25f045ecc7b46c0dc0ec116694b7a3e21aaec78a1826e3'),('/tmp/applied-safe-value-functions-v4-primary27.txt','be801eac2afb9d9364a6f696ca2466d87db21a0da0a0896ef5ccaea3c9e4e7b4')]:
 assert sha(z)==h;paper.append(copy(z))
d={'status':'prepared_actual_passed_chain49_full_source_and_literals_for_independent_semantic_review_only',
 'source':copy(S),'source_sha256':sha(S),'public_theorem_count':49,'public_definition_and_abbreviation_count':23,'public_declaration_count':72,
 'public_theorem_names':[ns+'.'+n for n in names],'public_definition_and_abbreviation_names':[ns+'.'+n for n in defs],
 'exercise_keys':[exkey],'material_unit_keys':keys,'entire_current_and_prospective_context':copy(C),'current_page_original_byte_alias':copy(page),
 'original_owner29_candidate':{'file':ownerpath.relative_to(R).as_posix(),'sha256':sha(ownerpath)},
 'current_inventory':{'file':invpath.relative_to(R).as_posix(),'sha256':sha(invpath)},
 'genuine_lean_native_history':history,'earlier_passed_proof_body_prefix':prefix,
 'generic_discounted_return_bridges_copied_exactly_except_whitespace':{'original_passed_source':copy(thermal),'body_sha256_after_whitespace_normalization':hashlib.sha256(tg.encode()).hexdigest(),'distinct_namespace_no_TMP_import_or_cache_install':True},
 'selected_complete_dependency_sources':selected,'primary_used_API_full_sources':primary,
 'actual_primary_safe_value_paper_original_bytes':paper,'primary_paper_used_scope':'Full source Zb and Theorem2/Lemma2 reward-bound proof context. This request does not promote the general theorem beyond this fully solved chain model.',
 'independent_narrow_wording_parser_peer':copy(R/'book/coverage/checks/future30-core/chain-long-horizon-value-independent-foundations-v1/modules-chain-long-horizon-value-unnumbered-narrow-literal-parser-independent-foundations30-closed-peer-v1.json'),'unnumbered_narrow_wording_proposal':copy(P),'actual_narrow_wording_author_parser':copy(pn),
 'full_scope_review_requests':[
  {'scope':'current entire Exercise7.4 and current node1144','whole_scope_expected_pending':True,
   'remaining_gap':'The printed long-horizon equation says -3.439+6.561=3.12 exactly. Its exact value is3.122=1561/500. The theorem2 bracket likewise must use exact3.122 before its unchanged approximate -2.2 result.'},
  {'scope':'prospective corrected entire Exercise7.4 and corrected node1144 conditional on actual later source application',
   'conclusions':['Actual seven physical cells and the original L/R/S transitions, slope and goal action convention are modeled. A separate post-payment cliff index projects to original absorbing cell0 and has zero future reward; one-time failure payment is collected at its literal worked time2 rather than charged forever.',
    'Actual finite reward/value bounds prove summability and genuine infinite discounted return. Bellman telescoping bounds every admissible history-dependent trajectory, and equality paths actually attain the bound.',
    'At gamma.5 the safe walk is perpetually viable and attains exact -7/4 from2. Its full value table is the greatest actual safe return over every safe history. The actual admissible jump attains -3/2-p/4, is globally optimal iff p<=1 for nonnegative p, and strictly beats walking iff p<1.',
    'The full piecewise optimal value table is a greatest actual return over all admissible histories. Optimal actual suffixes are proved optimal from the true first-term/infinite-tail identity; the unique viable exit is2L. This proves EVERY actual optimal history safe iff p>1, not only that some stationary safe policy is optimal.',
    'At p1 actual safe and unsafe trajectories both attain the global maximum. The safe penalty set has true greatest lower bound1, which is not itself safe. Actual state3 left return is -7/4-p/8 below its safe -3/2 for nonnegative p.',
    'Actual original physical unsafe reward supremum0 and unsafe-pair reward supremum0 are attained at the cliff; safe-pair reward infimum-1 is attained. The slope has exact one-step physical failure horizon; the safe value infimum-7/4 is attained at2. The theorem2 formula thus equals15/2, is sufficient via actual all-history safety, and is a factor7.5 above the true infimum1.',
    'The reward slacks at the actual slope and2L are each1 relative to the global0 reward bounds. The attained true unsafe optimal-value supremum is max(-p,-1-p/2); actual strictZb holds iff p>11/2, with true infimum11/2 not attained.',
    'At gamma.9 the actual walk has exact infinite return1561/500=3.122 (two-decimal approximation3.12), and is the greatest actual safe return. Its complete global value table is the greatest return over every admissible history for all nonnegative p; every actual optimal history is safe, including p0.',
    'The actual jump has infinite return -19/10-(81/100)p<0. Zero is an attained least safe nonnegative penalty. Actual safe value infimum1561/500 at2 gives theorem2 threshold-9049/4050<0, rigorously inside the rounding interval for the original -2.2 target.']},
  {'scope':'current nodes1135/1139/1141/1143','entire_current_literal_review_requested':True,
   'conclusions':['Actual original model, all history-dependent safe/global return extrema, true jump admissibility and optimum/tie/strict-infimum safety decisions close the entire model and gamma.5 worked answer.',
    'Actual reward extrema, failure horizon and attained safe/unsafe values give the precise conservative theorem2 threshold and its stated two reward slacks. The intermediate strictZb condition and its unattained infimum are genuine.']}],
 'domain_scope':['Discounts1/2 and9/10, as printed. Penalties are nonnegative when the source asks for safe penalized optimization.','Only S is allowed at goal6, following the printed action convention; cells2-5 have all L/R/S, the slope leads to failure for every action.','Arbitrary deterministic history-dependent action streams satisfying the model are covered. The augmented paid-cliff index records only whether the one-time penalty has already been collected; its physical projection is original absorbing cell0.'],
 'native_trial4_real_source_arithmetic_discrepancy_preserved':history[3],
 'genuine_original_author_preparation1_failed_on_overlap_row_count':copy('/tmp/modules-chain49-full-request30-preparation-actual-v1.json'),
 'genuine_original_author_preparation1_raw':copy('/tmp/modules-chain49-full-request30-preparation-actual-v1.log'),
 'genuine_original_author_preparation1_helper':copy('/tmp/prepare-modules-chain49-full-request30-v1.py'),
 'genuine_original_author_preparation1_wrapper':copy('/tmp/run-modules-chain49-full-request30-preparation-v1.py'),
 'original_closed_byte_aliases':aliases,'required_evidence_artifacts_sha256':{r['file']:r['sha256'] for r in aliases.values()},
 'source_number_reserved':False,'source_applied':False,'canonical_pairs_executed':False,'whole_promotion_performed':False,
 'independent_full_semantic_review_pending':True,'coverage_complete':False,'supplementary_after_frozen29_manifest':True}
for r in [d['original_owner29_candidate'],d['current_inventory']]:d['required_evidence_artifacts_sha256'][r['file']]=r['sha256']
O=B/'modules-chain49-full-source-literal-independent-review-request30-v1.json';O.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'request':O.relative_to(R).as_posix(),'sha256':sha(O),'bytes':O.stat().st_size,'closed_refs':len(d['required_evidence_artifacts_sha256']),'aliases':len(aliases),'warning_counts':[x['actual_warning_count'] for x in history]}))
