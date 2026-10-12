from pathlib import Path
import hashlib,json,re
R=Path('/home/oxrexkevin/SafetyBased')
B=R/'book/coverage/checks/modules-future30/coupled-tanh62-full-scope-v1'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
aliases={}
def copy(p):
 p=Path(p); h=sha(p); q=B/'original-closed-bytes'/h/p.name
 q.parent.mkdir(parents=True,exist_ok=True)
 if not q.exists():
  with q.open('xb') as f:f.write(p.read_bytes())
 assert sha(q)==h
 ref={'file':q.relative_to(R).as_posix(),'sha256':h,'bytes':q.stat().st_size}
 aliases[str(p)]=ref
 return ref
I=json.loads((R/'book/coverage/inventory.json').read_bytes()); M=json.loads((R/'book/coverage/modules.json').read_bytes())
assert sha(R/'book/coverage/modules.json')=='13a1955d1920b9eafec20b5b38d7e10800354db71188c154f0967a93bccbc22d'
E=next(x for x in M['exercises'] if x['inventory_key']=='lipsdp.html::exercise-17')
assert E['status']=='pending' and len(E['claims'])==4
keys=['lipsdp.html::node-'+str(i) for i in [1297,1301,1302,1303,1304]]
rows=[next(x for x in I['material_source_units'] if x['key']==k) for k in keys]
affected=[x for x in M['material_claims'] if set(x.get('source_unit_keys',[])).intersection(keys)]
assert all(x['status']=='pending' for x in E['claims'])
S=Path('/tmp/CompleteModulesCoupledTanhCounterexample30-draft-v10.lean')
assert sha(S)=='8b937abc9032a4daf436ad94209ed8db34e0ac03908930be68c5380fe240028e'
text=S.read_text(); namespace='SafeLearning.CompleteModulesCoupledTanhCounterexample30'
pubtheorems=re.findall(r'^theorem\s+(\w+)',text,re.M)
private=re.findall(r'^private theorem\s+(\w+)',text,re.M)
defs=re.findall(r'^def\s+(\w+)',text,re.M)
assert (len(pubtheorems),len(private),len(defs))==(61,1,19)
history=[]
for j in range(1,6):
 p=Path('/tmp/modules-coupled-tanh'+('61' if j<=2 else '62')+'-current65-owner29-trial'+str(j)+'.json')
 n=json.loads(p.read_bytes()); assert n['protection_errors']==[] and n['source_unchanged'] is True
 assert n['actual_command']==['lake','env','lean',n['source']] and n['actual_workdir']==str(R/'verification/lean')
 assert n['actual_exit_code']==(0 if j==5 else 1)
 for k in ['source','source_snapshot','raw_log']: copy(Path(n[k]))
 assert sha(Path(n['source']))==n['source_sha256_before']==n['source_sha256_after']==n['source_snapshot_sha256']
 assert sha(Path(n['raw_log']))==n['raw_log_sha256']
 history.append({'actual_native':copy(p),'actual_source':aliases[n['source']], 'actual_source_snapshot':aliases[n['source_snapshot']],'actual_raw_log':aliases[n['raw_log']], 'actual_exit_code':n['actual_exit_code'],'actual_warning_count':Path(n['raw_log']).read_text().count('warning:'),'original_body_and_times_untouched':True})
assert Path('/tmp/modules-coupled-tanh62-current65-owner29-trial5.log').read_bytes()==b''
for j in range(1,11):
 p=Path('/tmp/CompleteModulesCoupledTanhCounterexample30-draft-v'+str(j)+'.lean')
 if p.exists():copy(p)
tool_observations=copy('/tmp/modules-coupled-tanh-v9-prewrite-tool-observations-v1.json')
runtime=Path('/tmp/modules-coupled-tanh-exercise12-3-runtime30-actual-v1.json'); runtime_data=json.loads(runtime.read_bytes())
assert runtime_data['actual_exit_code']==0 and runtime_data['protection_errors']==[]
runtime_refs=[copy(runtime),copy('/tmp/modules-coupled-tanh-exercise12-3-runtime30-result-v1.json'),copy('/tmp/modules-coupled-tanh-exercise12-3-runtime30-v1.py'),copy('/tmp/run-modules-coupled-tanh-exercise12-3-runtime30-v1.py'),copy('/tmp/modules-coupled-tanh-exercise12-3-runtime30-actual-v1.log')]
selected_names=['CompleteModulesInvalidQC','CompleteModulesTanhNumerics','CompleteModulesTanhAsymptotic','CompleteModulesTanhChords','CompleteModulesTheory','CompleteModulesLipSDPNetwork','CompleteModulesLipSDP','CompleteModulesDiagonalQC','CompleteModulesTanhSharpBounds','CompleteModulesTanhExtrema']
selected=[]
for name in selected_names:
 p=R/'verification/lean/SafeLearning'/ (name+'.lean')
 if p.exists():selected.append(copy(p))
mathlib=['Analysis/SpecialFunctions/Artanh.lean','Analysis/Calculus/LocalExtr/Basic.lean','Topology/Order/LocalExtr.lean','LinearAlgebra/Matrix/Charpoly/Basic.lean','LinearAlgebra/Matrix/PosDef.lean','Analysis/Calculus/MeanValue.lean','Analysis/Real/Sqrt.lean','Analysis/Complex/Exponential.lean','Analysis/Complex/Trigonometric.lean']
primary_api=[]
for name in mathlib:
 p=R/'verification/lean/.lake/packages/mathlib/Mathlib'/name
 assert p.is_file(),str(p)
 primary_api.append({'original_external_package_path_historical_metadata':str(p),'exact_physical_byte_alias':copy(p)})
paper=copy(R/'book/coverage/checks/future28-foundations/source63-independent-foundations29-v1/original-bytes/eee4df99f0f0b5f4e872902368a4d6d5718f502c05b1fb4c89650a4c46a0ecfb/pauli_lcss.txt')
page=R/'SafeLearning/lipsdp.html';assert sha(page)==E['source_sha256']
page_alias=copy(page);lines=page.read_text().splitlines(keepends=True)
context={'entire_current_exercise_html':''.join(lines[969:988]),'entire_section5_html':''.join(lines[349:412]),'current_full_exercise_owner_row':E,'five_exact_full_inventory_rows':rows,'all_affected_original_material_claim_rows':affected}
contextpath=B/'modules-coupled-tanh62-entire-current-source-context-v1.json';assert not contextpath.exists();contextpath.write_text(json.dumps(context,ensure_ascii=False,indent=2)+'\n')
contextref={'file':contextpath.relative_to(R).as_posix(),'sha256':sha(contextpath),'bytes':contextpath.stat().st_size}
copy('/tmp/root_tmp_lean_current65_owner29_context_v1.json');copy('/tmp/root_tmp_lean_current65_owner29_runner_v1.py')
copy(Path(__file__))
candidate=R/'book/coverage/checks/modules-future29/current65-pair-bound-v7/modules29-current65-two-source-pair-bound-candidate-v1.json'
assert sha(candidate)==sha(R/'book/coverage/modules.json')
full_scopes=[
 {'scope':'whole current Exercise12.3 / exercise17 and whole node1297','conclusions':['Every exact requirement and its dependencies, not merely counterexample sign.','Actual ReLU points/deltas/form=-3; actual tanh affine weights/bias/network; actual T products/full matrix/eigenvalues with multiplicities.','Negative semidefinite coupled family at every positive rho, arbitrary sqrt-rho claim forces constancy, actual network is nonconstant.','Exact attained least global Lipschitz constant; independent patterns maximum1 and attained least valid diagonal SDP value1.']},
 {'scope':'whole node1301','conclusions':['Exact actual increment difference form and point evaluation -3<0.','Separate direct primary SectionII-C source read validates the book citation fact that the paper prints -2 for the same stated points; Lean does not certify PDF text.']},
 {'scope':'whole node1302','conclusions':['Actual full Fin1⊕Fin2 matrix equality, products, eigenbasis inverse/diagonalisation and characteristic-polynomial multiplicities.','Full actual multiplier PSD and every positive-rho negative-semidefinite certificate; false arbitrary bound implies constancy and is contradicted.']},
 {'scope':'whole node1303','conclusions':['Actual composition, actual first derivative/sech identity/oddness; global profile reduction on entire real line and complete[0,1] slope interval, unique critical root/attainment and genuine least true global Lipschitz bound.','Rigorous .93349<L<.933495 and input1.0605<x<1.0615 roundings; direct actual .061/2.061 sech-squared roundings.','Actual source weights pattern gain d0-d1, attained all-patterns maximum1, every diagonal certificate rho>=1 and identity feasible, actual bound1 valid, relative looseness strictly .07..075.']},
 {'scope':'whole node1304','conclusions':['Genuine scalar derivatives and second derivative, all global derivative-magnitude maximizers solve actual printed fsecond=0 via Fermat sign cases.','Magnitude even and tends to zero when absolute input tends to infinity.','Actual grid6001 points[0,6] and Newton on actual printed fsecond, exact source helper/native/result; runtime distinct from kernel global proof.']}]
d={'status':'prepared_actual_passed_coupled_tanh62_full_literal_scope_for_independent_review_only','source':copy(S),'source_sha256':sha(S),'theorem_count':61,'private_theorem_count':1,'definition_count':19,'public_declaration_count':80,'public_theorem_names':[namespace+'.'+x for x in pubtheorems],'public_definition_names':[namespace+'.'+x for x in defs],'private_full_body_names':private,'exercise_key':E['inventory_key'],'material_unit_keys':keys,'entire_current_context':contextref,'source_page_original_byte_alias':page_alias,'original_owner29_candidate':{'file':candidate.relative_to(R).as_posix(),'sha256':sha(candidate)},'current_inventory':{'file':'book/coverage/inventory-after-correction65.json','sha256':sha(R/'book/coverage/inventory-after-correction65.json')},'full_scope_review_requests':full_scopes,'real_lean_native_history':history,'actual_runtime_support':runtime_refs,'primary_citation':{'primary_url':'https://arxiv.org/abs/2005.02929','version':'v2','full_original_text':paper,'required_full_passage_lines':[135,218],'citation_fact_scope':'Same stated points, printed -2; actual evaluation -3. No Section5 cosinefit.0843, product2, bibliographic history or unrelated whole unit promotion inferred.'},'selected_complete_dependency_sources':selected,'primary_used_api_full_sources':primary_api,'precompiler_actual_tool_observations':tool_observations,'original_closed_byte_aliases':aliases,'required_evidence_artifacts_sha256':{r['file']:r['sha256'] for r in aliases.values()},'whole_promotion_performed':False,'independent_full_semantic_review_pending':True,'canonical_pairs_executed':False,'coverage_complete':False,'supplementary_after_frozen29_manifest':True}
for r in [contextref,d['original_owner29_candidate'],d['current_inventory']]:d['required_evidence_artifacts_sha256'][r['file']]=r['sha256']
out=B/'modules-coupled-tanh62-full-scope-independent-review-request30-v1.json';assert not out.exists();out.write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'status':d['status'],'request':out.relative_to(R).as_posix(),'sha256':sha(out),'bytes':out.stat().st_size,'original_alias_count':len(aliases),'warning_counts':[x['actual_warning_count'] for x in history]}))
