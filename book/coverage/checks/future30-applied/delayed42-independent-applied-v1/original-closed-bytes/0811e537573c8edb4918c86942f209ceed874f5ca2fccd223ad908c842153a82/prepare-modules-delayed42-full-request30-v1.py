from pathlib import Path
import hashlib, json, re
R=Path('/home/oxrexkevin/SafetyBased')
B=R/'book/coverage/checks/modules-future30/delayed42-full-scope-v1'
assert not B.exists()
B.mkdir(parents=True)
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
aliases={}
def copy(p):
 p=Path(p);h=sha(p);q=B/'original-closed-bytes'/h/p.name
 q.parent.mkdir(parents=True,exist_ok=True)
 if not q.exists():
  with q.open('xb') as f:f.write(p.read_bytes())
 assert sha(q)==h
 r={'file':q.relative_to(R).as_posix(),'sha256':h,'bytes':q.stat().st_size}
 aliases[str(p)]=r
 return r
S=Path('/tmp/CompleteModulesDelayedSquareWhole30-draft-v4.lean')
assert sha(S)=='6662787112f67e50c1485c25b2eec7950242b4bc2bcfa17f356aee1555700cad'
t=S.read_text();ns='SafeLearning.CompleteModulesDelayedSquareWhole30'
theorems=re.findall(r'^theorem\s+(\w+)',t,re.M)
defs=re.findall(r'^def\s+(\w+)',t,re.M)
abbrevs=re.findall(r'^abbrev\s+(\w+)',t,re.M)
assert (len(theorems),len(defs),len(abbrevs))==(42,13,1)
I=json.loads((R/'book/coverage/inventory-after-correction65.json').read_bytes())
ownerpath=R/'book/coverage/checks/modules-future29/current65-pair-bound-v7/modules29-current65-two-source-pair-bound-candidate-v1.json'
assert sha(ownerpath)==sha(R/'book/coverage/modules.json')=='13a1955d1920b9eafec20b5b38d7e10800354db71188c154f0967a93bccbc22d'
M=json.loads(ownerpath.read_bytes())
E=next(r for r in M['exercises'] if r['inventory_key']=='nn-in-the-loop.html#book-m14-b2')
assert E['status']=='partial' and len(E['claims'])==7
keys=['nn-in-the-loop.html::node-'+str(i) for i in [909,916,920]]
rows=[next(r for r in I['material_source_units'] if r['key']==k) for k in keys]
affected=[r for r in M['material_claims'] if set(r.get('source_unit_keys',[])) & set(keys)]
assert len(affected)==3
page=R/'SafeLearning/nn-in-the-loop.html'
assert sha(page)==E['source_sha256']
lines=page.read_text().splitlines(keepends=True)
proposalpath=Path('/tmp/modules-delayed-roots-unnumbered-proposal30-v1/modules-delayed-roots-unnumbered-full29-proposal30-v1.json')
proposal=json.loads(proposalpath.read_bytes())
assert proposal['fresh_changed_literal_keys']=={'exercises':['nn-in-the-loop.html#book-m14-b2'],'material_source_units':['nn-in-the-loop.html::node-920']}
for v in proposal.values():
 if isinstance(v,dict) and set(['file','sha256']).issubset(v):
  p=Path(v['file']);p=p if p.is_absolute() else R/p
  assert sha(p)==v['sha256'];copy(p)
proposalref=copy(proposalpath)
proposalnative=Path('/tmp/modules-delayed-roots-unnumbered-proposal30-preparation-actual-v1.json')
pn=json.loads(proposalnative.read_bytes());assert pn['actual_exit_code']==0 and pn['protection_errors']==[]
for p in [proposalnative,Path(pn['raw_log']),Path('/tmp/prepare-modules-delayed-roots-unnumbered-proposal30-v1.py'),Path('/tmp/run-modules-delayed-roots-unnumbered-proposal30-preparation-v1.py')]:copy(p)
context={'entire_current_plant_and_exercise_context_lines779_815':''.join(lines[778:815]),
 'entire_current_exercise_literal':next(r for r in I['exercises'] if r['key']==E['inventory_key']),
 'entire_current_exercise_owner_row':E,'three_entire_current_material_inventory_rows':rows,
 'three_entire_old_material_claim_rows':affected,
 'entire_prospective_corrected_exercise_literal':proposal['entire_current_and_proposed_literal_records'][E['inventory_key']]['entire_proposed'],
 'entire_prospective_corrected_node920_literal':proposal['entire_current_and_proposed_literal_records'][keys[2]]['entire_proposed']}
C=B/'modules-delayed42-full-current-and-prospective-context-v1.json';C.write_text(json.dumps(context,indent=2,ensure_ascii=False)+'\n')
history=[]
for j in range(1,5):
 p=Path('/tmp/modules-delayed-square-whole30-current65-owner29-trial'+str(j)+'.json')
 n=json.loads(p.read_bytes())
 assert n['actual_exit_code']==[1,0,1,0][j-1] and n['protection_errors']==[] and n['source_unchanged']
 assert n['actual_command']==['lake','env','lean',n['source']] and n['actual_workdir']==str(R/'verification/lean')
 assert sha(n['source'])==n['source_sha256_before']==n['source_sha256_after']==n['source_snapshot_sha256']==sha(n['source_snapshot'])
 assert sha(n['raw_log'])==n['raw_log_sha256']
 raw=Path(n['raw_log']).read_text()
 history.append({'actual_native':copy(p),'actual_source':copy(n['source']),
  'actual_source_snapshot':copy(n['source_snapshot']),'actual_raw_log':copy(n['raw_log']),
  'actual_exit_code':n['actual_exit_code'],'actual_warning_count':len(re.findall(r'^.*?:\d+:\d+: warning:',raw,re.M)),
  'original_body_and_times_untouched':True})
assert Path('/tmp/modules-delayed-square-whole30-current65-owner29-trial4.log').read_bytes()==b''
selected=[copy(R/'verification/lean/SafeLearning'/ (name+'.lean')) for name in ['CompleteModulesDynamics','CompleteModulesBook','CompleteFoundationsNormDuality']]
primary=[]
for name in ['LinearAlgebra/Matrix/Charpoly/Coeff.lean','LinearAlgebra/Matrix/Charpoly/Basic.lean',
 'Data/Matrix/Mul.lean','Analysis/Complex/Norm.lean','Analysis/Real/Sqrt.lean',
 'Logic/Function/Iterate.lean','Analysis/Normed/Group/Continuity.lean','Analysis/InnerProductSpace/PiL2.lean']:
 p=R/'verification/lean/.lake/packages/mathlib/Mathlib'/name
 primary.append({'original_external_package_path_historical_metadata':str(p),'exact_physical_byte_alias':copy(p)})
copy('/tmp/root_tmp_lean_current65_owner29_context_v1.json');copy('/tmp/root_tmp_lean_current65_owner29_runner_v1.py');copy(Path(__file__))
d={'status':'prepared_actual_passed_delayed42_full_source_and_literal_for_independent_semantic_review_only',
 'source':copy(S),'source_sha256':sha(S),'public_theorem_count':42,'public_definition_count':13,
 'public_abbreviation_count':1,'public_declaration_count':56,
 'public_theorem_names':[ns+'.'+n for n in theorems],'public_definition_names':[ns+'.'+n for n in defs],
 'public_abbreviation_names':[ns+'.'+n for n in abbrevs],
 'exercise_key':E['inventory_key'],'material_unit_keys':keys,'entire_current_and_prospective_context':copy(C),
 'current_page_original_byte_alias':copy(page),'original_owner29_candidate':{'file':str(ownerpath.relative_to(R)),'sha256':sha(ownerpath)},
 'current_inventory':{'file':'book/coverage/inventory-after-correction65.json','sha256':sha(R/'book/coverage/inventory-after-correction65.json')},
 'genuine_lean_native_history':history,'selected_complete_dependency_sources':selected,'primary_used_API_full_sources':primary,
 'unnumbered_narrow_wording_proposal':proposalref,'actual_narrow_wording_author_parser':copy(proposalnative),
 'full_scope_review_requests':[
  {'scope':'current node909 whole and current node916 whole','conclusions':['Exact plant/controller composition and actual augmented matrix action.','Arbitrary independently initialized current and controller-memory coordinates, with no prior admissible-history condition.','Every augmented trajectory converges in the genuine Euclidean topology; the equilibrium is Lyapunov stable with a uniform epsilon/delta estimate.','Every initial-square command is hardware feasible, next-error bound3/5 is attained at both opposite-sign corners, and the requested square is not invariant.','Exact actual characteristic polynomial, complete iff description of both distinct conjugate roots, actual eigenvectors and strict unit-circle magnitudes.']},
  {'scope':'current entire Exercise14.B2 and current node920','whole_scope_expected_pending':True,'remaining_gap':'Current text presents .312250 as an exact imaginary part. Genuine sqrt39/20 is unequal to that rational; original source remains unchanged.'},
  {'scope':'prospective corrected entire Exercise14.B2 and corrected node920 conditional on actual later source application','conclusions':['All five full prompt requirements and every hint/answer clause, not only an escape witness.','Exact roots9/20±i sqrt39/20 and rigorous six-decimal imaginary and magnitude rounding enclosures.','Actual nominal escaping next error.6, command.75≤.8 and still-convergent escaping trajectory; saturation is not required for the violation.','A nontrivial storage sublevel in both coordinates is invariant, all its trajectories stay in the square, its temperature projection is35–45 and its actuator remains feasible.']},
  {'scope':'two old partial component gap associations only, no old statement/declaration/hypothesis/time changes',
   'associations':[{'claim_id':E['claims'][5]['id'],'old_gap':E['claims'][5]['remaining_gaps'],'exact_support':['actual_characteristic_factorization','actual_complex_roots_iff','actual_two_complex_roots','exact_root_magnitudes','all_initialized_augmented_trajectories_tend_zero']},
    {'claim_id':E['claims'][6]['id'],'old_gap':E['claims'][6]['remaining_gaps'],'exact_support':['roots_real_and_imaginary_parts','imaginary_part_six_decimal_rounding','root_magnitude_six_decimal_rounding','rounded_imaginary_decimal_is_not_exact']}]}],
 'original_closed_byte_aliases':aliases,'required_evidence_artifacts_sha256':{r['file']:r['sha256'] for r in aliases.values()},
 'source_number_reserved':False,'source_applied':False,'canonical_pairs_executed':False,'whole_promotion_performed':False,
 'independent_full_semantic_review_pending':True,'coverage_complete':False,'supplementary_after_frozen29_manifest':True}
for r in [d['original_owner29_candidate'],d['current_inventory']]:d['required_evidence_artifacts_sha256'][r['file']]=r['sha256']
O=B/'modules-delayed42-full-source-literal-independent-review-request30-v1.json'
O.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'request':str(O.relative_to(R)),'sha256':sha(O),'bytes':O.stat().st_size,'closed_refs':len(d['required_evidence_artifacts_sha256']),'aliases':len(aliases),'warning_counts':[x['actual_warning_count'] for x in history]}))
