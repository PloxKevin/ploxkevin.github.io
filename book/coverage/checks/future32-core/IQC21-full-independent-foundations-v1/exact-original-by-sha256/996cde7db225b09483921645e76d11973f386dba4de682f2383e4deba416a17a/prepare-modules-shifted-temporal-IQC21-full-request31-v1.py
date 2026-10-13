from pathlib import Path
import hashlib,json,re,sys
R=Path('/home/oxrexkevin/SafetyBased');B=Path('/tmp/modules-shifted-temporal-IQC21-full-Exercise14_6-review31-v1');assert not B.exists();B.mkdir()
C=Path('/tmp/root_tmp_lean_current81_historical_owner30_context_v1.json');assert hashlib.sha256(C.read_bytes()).hexdigest()=='f9490760c85e8be1392f271bdf65e193e5a5e4cfc2ba29b5f7e4d32c682a7af9';context=json.loads(C.read_bytes());guards={**context['pins_sha256'],**context['held_current_source_sha256'],**context['owners_sha256']}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):
 p=Path(p);return {'file':str(p),'sha256':sha(p),'bytes':p.stat().st_size}
aliases={};originals={}
def copied(p):
 p=Path(p);h=sha(p);q=B/'physical-originals'/h/p.name;q.parent.mkdir(parents=True,exist_ok=True)
 if not q.exists():
  with q.open('xb')as f:f.write(p.read_bytes())
 assert sha(q)==h;aliases[str(p)]=ref(q);originals[str(p)]=h;return ref(q)
def guard():
 for n,h in guards.items():
  p=R/n;assert p.is_file()and not p.is_symlink()and p.resolve().is_relative_to(R)and sha(p)==h,n
guard();sys.dont_write_bytecode=True;sys.path.insert(0,str(R/'book/coverage'));import lean_names
S=Path('/tmp/CompleteModulesShiftedTemporalIQC31-draft-v14.lean');text=S.read_text();ds=lean_names.declarations(text);tn=[x['name']for x in ds if x['kind']in ['theorem','lemma']];assert len(tn)==21
assert S.read_bytes().startswith(Path('/tmp/CompleteModulesShiftedTemporalIQC31-draft-v13.lean').read_bytes())
assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by|run_elab|ofReduceBool|sorryAx)\b',lean_names.without_comments(text))
invpath=R/'book/coverage/inventory-after-correction81.json';inv=json.loads(invpath.read_bytes());assert sha(invpath)=='b1e914086b3b3ab104bbfff6a647ad5488f6797b2a6f3e4f6aa7ffcb5aa74ef5'
ex=next(x for x in inv['exercises']if x['key']=='nn-in-the-loop.html::exercise-20');keys=['nn-in-the-loop.html::node-'+n for n in ['1254','1258','1260','1262']];units={x['key']:x for x in inv['material_source_units']if x['key']in keys};assert len(units)==4
ownerpath=R/'book/coverage/checks/modules-future30/current79-three-fragments-final-v1/modules30-current79-real30-three-fragments-candidate-v1.json';assert sha(ownerpath)=='6f347b3d512a5ce36222e72e8236eb350f3218ace430c3a9dabd8776a03fbc34';owner=json.loads(ownerpath.read_bytes());oe=next(x for x in owner['exercises']if x['inventory_key']==ex['key']);assert oe['status']=='partial'
oldrows=[x for x in owner['material_claims']if set(x['source_unit_keys'])&set(keys)]
page=R/'SafeLearning/nn-in-the-loop.html';assert sha(page)==ex['source_sha256'];lines=page.read_text().splitlines(keepends=True)
selectednames=['CompleteModulesNNTanhOffset24','CompleteModulesNNTanhOffsetConsequences24','CompleteModulesNNTanhSectorClass24','CompleteModulesNNDoublyHyperdominant25','CompleteModulesNNTemporalDiagonal25','CompleteModulesNNTwoLayerLFT23','CompleteModulesLipSDP','CompleteModulesTanhChords','CompleteModulesTanhNumerics']
selected=[copied(R/'verification/lean/SafeLearning'/f'{n}.lean')for n in selectednames]
primarynames=['Algebra/Order/Rearrangement.lean','Analysis/Convex/Birkhoff.lean','Order/Monotone/Monovary.lean','Data/Matrix/Mul.lean','Data/Matrix/Block.lean','Algebra/BigOperators/Group/Finset/Defs.lean','Algebra/BigOperators/Ring/Finset.lean','Data/Fin/Basic.lean','Analysis/SpecialFunctions/Trigonometric/DerivHyp.lean','Analysis/Complex/Trigonometric.lean','Algebra/GroupWithZero/Basic.lean','Data/Int/Interval.lean']
primary=[copied(R/'verification/lean/.lake/packages/mathlib/Mathlib'/n)for n in primarynames]
previous=[]
for key in ['independent_source_review','canonical_source_binding_peer']:
 for row in oe['claims']:
  x=row.get(key)
  if x:
   p=Path(x['file']);p=p if p.is_absolute()else R/p;assert sha(p)==x['sha256'];rr=copied(p)
   if rr not in previous:previous.append(rr)
hist=[];codes=[1,0,1,0,1,0,1,1,1,0,1,1,0,0]
for j in range(1,15):
 stem=f'modules-shifted-temporal-IQC31-owner30-trial{j}'if j<=7 else f'modules-shifted-temporal-IQC31-source81-historical-owner30-trial{j}'
 npath=Path('/tmp')/(stem+'.json');n=json.loads(npath.read_bytes());raw=Path(n['raw_log']);s=Path(n['source']);snap=Path(n['source_snapshot'])
 assert n['actual_exit_code']==n['actual_runner_exit_code']==codes[j-1]and n['protection_errors']==[]and n['source_unchanged']is True
 assert sha(s)==n['source_sha256_before']==n['source_sha256_after']==sha(snap)==n['source_snapshot_sha256']and sha(raw)==n['raw_log_sha256']
 assert n['actual_command']==['lake','env','lean',str(s)]and n['actual_workdir']==str(R/'verification/lean')
 contextkey='actual_source79_final_css_owner30_context'if j<=7 else'actual_source81_historical_source79_owner30_context'
 historical_context=Path(n[contextkey]['file']);assert sha(historical_context)==n[contextkey]['sha256']
 runner=Path(n['original_actual_runner']['file']);assert sha(runner)==n['original_actual_runner']['sha256']
 hist.append({'trial':j,'native':copied(npath),'source':copied(s),'snapshot':copied(snap),'raw_log':copied(raw),'actual_exit_code':n['actual_exit_code'],'emitted_diagnostic_warning_headers':len(re.findall(rb'^.*?:\d+:\d+: warning:',raw.read_bytes(),re.M)),'actual_original_context':copied(historical_context),'actual_original_runner':copied(runner),'original_body_times':{k:n[k]for k in ['started_at_utc','finished_at_utc','elapsed_seconds']}})
assert hist[-1]['source']['sha256']==sha(S)and hist[-1]['actual_exit_code']==0
retr=Path('/tmp/modules-shifted-temporal-IQC-primary31-v1/actual-primary-retrieval-v1.json');rp=json.loads(retr.read_bytes());assert rp['actual_HTTP_status']==200 and rp['actual_pdftotext_exit_code']==0
for key in ['original_pdf','full_extracted_text']:assert sha(rp[key]['file'])==rp[key]['sha256']
decisions=[{'key':keys[0],'requested_current_whole':True,'reason':'Entire(a)/(b)/(c) mathematical requirements are supplied by full selected24/25 bodies plus21 actual causal FIR/loop-transform proofs, without a conclusion hypothesis.'},{'key':keys[1],'requested_current_whole':True,'reason':'Full actual shiftedfunctions, inherited[0,1]slopes and exact origin values supplied in selected24; preserve prior component bodies.'},{'key':keys[2],'requested_current_whole':True,'reason':'Actual matrix identity, exact negative value and four rounded-number enclosures retained from selected24; new21 directly refutes the uniform premise, without inferring instability.'},{'key':keys[3],'requested_current_whole':True,'reason':'All-depth zero bias-free tanh, equal-offset/common-bound grouping, true diagonal and fullblock sector choices, actual zero-state delay-window hard IQC for independent shifted channels, and exact nonzero-shift oddness failure. The common local-bound restriction is supported by the explicit -1/8 shared-activation countermodel. Final diagonal-T use is bounded source correspondence, not a new general LMI theorem.'}]
q={'status':'prepared_actual_source81_shifted_temporal_IQC21_entire_Exercise14_6_four_literals_full_review_request','source':copied(S),'public_theorem_names':tn,'public_theorem_count':21,'all_public_declarations':ds,'entire_current_exercise':ex,'entire_four_current_material_literals':units,'entire_original_partial_exercise_and_all_component_rows':oe,'entire_original_material_rows':oldrows,'current_inventory':ref(invpath),'immutable_original_installed_owner30':ref(ownerpath),'current_source':copied(page),'exact_keepends_exercise_context_lines1028_1046':''.join(lines[1027:1046]),'entire_Section3_context_lines240_393':''.join(lines[239:393]),'equilibrium_shift_context_lines90_113':''.join(lines[89:113]),'full_selected_proof_sources':selected,'complete_used_primary_Mathlib_sources':primary,'entire_prior_component_peers':previous,'genuine_original_compiler_histories':hist,'uncompiled_source_versions':[],'individual_full_literal_review_requests':decisions,'full_exercise_whole_requested':True,'current_full_exercise_whole_approved_by_author':False,'finite_FIR_realization_scope':'Actual zero-initial shift register, exact retained lags, exact printed tildeP firstrow/column and middleblock, and exact finite-horizon sum equals the banded Toeplitz form. No spectral-factor or desired hard-IQC assumption. The printed L gives(-b,-a); an explicit transpose handles nonsymmetric M before the two sign changes. No coefficient-symmetry assumption. Independent diagonal channels retain their own scalar coefficient conditions and slope bounds.','odd_class_scope':'New actual shifted-tanh odd iff center0 proves why generic nonzero shifted channels cannot use the enlarged odd class. No general enlarged odd-multiplier theorem is asserted.','primary_paper_bounded_attribution':'The CDC2021 primary explicitly distinguishes shifted nonidentical channels from repeated nonlinearities, gives the fullblock sector-gain interpretation, specifies the FIR firstrow/column/middle matrix and zero prehistory, and states diagonal coefficients suffice for nonrepeated channels. Its scalar-to-slope transformation uses the same printed signs. The finite hard-IQC proof expands the Toeplitz form; our proof derives the causal-filter equality and handles the transformed nonsymmetric orientation explicitly. The enlarged odd case separately needs oddness.','offline_primary_PDF_and_fulltext_only':{key:rp[key]for key in ['original_pdf','full_extracted_text']},'actual_primary_retrieval':copied(retr),'full_remote_PDF_or_text_publication_authorized':False,'primary_full_sections_actually_read':['II-A equilibrium shift and Remark1','II-C fullblock sector choices','II-D and Theorem1 FIR coefficients/filter/loop transformation','AppendicesA/B finite Toeplitz proof and diagonal/nonrepeated scope'],'all_original_byte_aliases':aliases,'all_physical_original_inputs_sha256':originals,'guard_current_sha256':guards,'current_partial_and_all_old_proved_body_times_remain_unchanged':True,'compiler_or_parser_owner_source_canonical_publication_mutation':False,'canonical31_selection_contains_this_future_source':False,'coverage_complete':False,'scope':'Independent full reading of all21 bodies, full selected proof bodies and every requested clause is required. These current whole decisions are requests only; the original old partial/wholeFalse and component bodies/times remain untouched.'}
for p in sorted(Path('/tmp').glob('modules-shifted-temporal-*-append31-v1.txt')):q.setdefault('original_append_inputs',[]).append(copied(p))
guard()
out=B/'modules-shifted-temporal-IQC21-entire-current-Exercise14_6-four-literals-full-review-request31-v1.json'
with out.open('x')as f:json.dump(q,f,indent=2);f.write('\n')
print(json.dumps({'request':ref(out),'actual_histories':codes,'actual_final_warnings':hist[-1]['emitted_diagnostic_warning_headers'],'whole_approved':False}))
