from pathlib import Path
import hashlib,json,re
R=Path('/home/oxrexkevin/SafetyBased')
B=R/'book/coverage/checks/modules-future30/physical-gp34-full-scope-v1'
assert not B.exists()
B.mkdir(parents=True)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
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
S=Path('/tmp/CompleteModulesPhysicalGPWhole30-draft-v4.lean')
assert sha(S)=='3c6841d74305c42310ad96ef21ef0a464114286f5c033c593904328d5af1bc65'
t=S.read_text();ns='SafeLearning.CompleteModulesPhysicalGPWhole30'
theorems=re.findall(r'^theorem\s+(\w+)',t,re.M);defs=re.findall(r'^def\s+(\w+)',t,re.M)
assert (len(theorems),len(defs))==(34,21)
I=json.loads((R/'book/coverage/inventory-after-correction65.json').read_bytes())
ownerpath=R/'book/coverage/checks/modules-future29/current65-pair-bound-v7/modules29-current65-two-source-pair-bound-candidate-v1.json'
assert sha(ownerpath)==sha(R/'book/coverage/modules.json')=='13a1955d1920b9eafec20b5b38d7e10800354db71188c154f0967a93bccbc22d'
M=json.loads(ownerpath.read_bytes())
exkeys=['toolkit-gp.html#book-m3-b1','toolkit-gp.html#book-m3-b2']
exercises=[next(r for r in M['exercises'] if r['inventory_key']==k) for k in exkeys]
assert [e['status'] for e in exercises]==['partial','partial']
assert [len(e['claims']) for e in exercises]==[4,5]
keys=['toolkit-gp.html::node-'+str(i) for i in [940,944,948,955,959]]
rows=[next(r for r in I['material_source_units'] if r['key']==k) for k in keys]
affected=[r for r in M['material_claims'] if set(r.get('source_unit_keys',[]))&set(keys)]
assert len(affected)==6
page=R/'SafeLearning/toolkit-gp.html';assert sha(page)==exercises[0]['source_sha256']==exercises[1]['source_sha256']
lines=page.read_text().splitlines(keepends=True)
proposalpath=Path('/tmp/modules-gp-discrepancy-unnumbered-proposal30-v1/modules-gp-discrepancy-unnumbered-full29-proposal30-v1.json')
proposal=json.loads(proposalpath.read_bytes())
assert proposal['fresh_changed_literal_keys']=={'exercises':[exkeys[1]],'material_source_units':[keys[4]]}
for v in proposal.values():
 if isinstance(v,dict) and {'file','sha256'}<=v.keys():
  p=Path(v['file']);p=p if p.is_absolute() else R/p
  assert sha(p)==v['sha256'];copy(p)
proposalref=copy(proposalpath)
proposalnative=Path('/tmp/modules-gp-discrepancy-unnumbered-proposal30-preparation-actual-v1.json')
pn=json.loads(proposalnative.read_bytes());assert pn['actual_exit_code']==0 and pn['protection_errors']==[]
for p in [proposalnative,pn['raw_log'],'/tmp/prepare-modules-gp-discrepancy-unnumbered-proposal30-v1.py','/tmp/run-modules-gp-discrepancy-unnumbered-proposal30-preparation-v1.py']:copy(p)
context={'entire_current_GP_context_and_both_exercises_lines875_914':''.join(lines[874:914]),
 'two_entire_current_exercise_inventory_rows':[next(r for r in I['exercises'] if r['key']==k) for k in exkeys],
 'two_entire_current_partial_exercise_owner_rows':exercises,
 'five_entire_current_material_inventory_rows':rows,'six_entire_old_affected_material_claim_rows':affected,
 'entire_prospective_corrected_B2_literal':proposal['entire_current_and_proposed_literal_records'][exkeys[1]]['entire_proposed'],
 'entire_prospective_corrected_node959_literal':proposal['entire_current_and_proposed_literal_records'][keys[4]]['entire_proposed']}
C=B/'modules-physical-gp34-full-current-and-prospective-context-v1.json';C.write_text(json.dumps(context,indent=2,ensure_ascii=False)+'\n')
history=[]
for j in range(1,5):
 p=Path('/tmp/modules-physical-gp-whole30-current65-owner29-trial'+str(j)+'.json');n=json.loads(p.read_bytes())
 assert n['actual_exit_code']==[1,1,1,0][j-1] and n['protection_errors']==[] and n['source_unchanged']
 assert n['actual_command']==['lake','env','lean',n['source']] and n['actual_workdir']==str(R/'verification/lean')
 assert sha(n['source'])==n['source_sha256_before']==n['source_sha256_after']==n['source_snapshot_sha256']==sha(n['source_snapshot'])
 assert sha(n['raw_log'])==n['raw_log_sha256'];raw=Path(n['raw_log']).read_text()
 history.append({'actual_native':copy(p),'actual_source':copy(n['source']),
  'actual_source_snapshot':copy(n['source_snapshot']),'actual_raw_log':copy(n['raw_log']),
  'actual_exit_code':n['actual_exit_code'],'actual_warning_count':len(re.findall(r'^.*?:\d+:\d+: warning:',raw,re.M)),
  'original_body_and_times_untouched':True})
assert Path('/tmp/modules-physical-gp-whole30-current65-owner29-trial4.log').read_bytes()==b''
selected=[copy(R/'verification/lean/SafeLearning'/(name+'.lean')) for name in ['CompleteModulesMatrixGP','CompleteModulesBook']]
primary=[]
for name in ['Data/Matrix/Mul.lean','LinearAlgebra/Matrix/NonsingularInverse.lean',
 'Analysis/SpecificLimits/Basic.lean','Order/Filter/AtTopBot/Archimedean.lean','Analysis/Real/Sqrt.lean']:
 p=R/'verification/lean/.lake/packages/mathlib/Mathlib'/name
 primary.append({'original_external_package_path_historical_metadata':str(p),'exact_physical_byte_alias':copy(p)})
for p in ['/tmp/root_tmp_lean_current65_owner29_context_v1.json','/tmp/root_tmp_lean_current65_owner29_runner_v1.py',__file__,'/tmp/run-modules-physical-gp34-full-request30-preparation-v1.py']:copy(p)
d={'status':'prepared_actual_passed_physical_GP34_full_source_and_literals_for_independent_semantic_review_only',
 'source':copy(S),'source_sha256':sha(S),'public_theorem_count':34,'public_definition_count':21,'public_declaration_count':55,
 'public_theorem_names':[ns+'.'+n for n in theorems],'public_definition_names':[ns+'.'+n for n in defs],
 'exercise_keys':exkeys,'material_unit_keys':keys,'entire_current_and_prospective_context':copy(C),
 'current_page_original_byte_alias':copy(page),
 'original_owner29_candidate':{'file':ownerpath.relative_to(R).as_posix(),'sha256':sha(ownerpath)},
 'current_inventory':{'file':'book/coverage/inventory-after-correction65.json','sha256':sha(R/'book/coverage/inventory-after-correction65.json')},
 'genuine_lean_native_history':history,'selected_complete_dependency_sources':selected,'primary_used_API_full_sources':primary,
 'unnumbered_narrow_wording_proposal':proposalref,'actual_narrow_wording_author_parser':copy(proposalnative),
 'full_scope_review_requests':[
  {'scope':'current entire Exercise3.B1 and current nodes940/944',
   'conclusions':['Actual arbitrary repeated-data kernel matrix with every entry4, regularizer1, inverse, inverse action, and uniqueness of the all-ones linear-system solution.',
    'Actual selected matrix posterior formulas yield mean8n/(1+4n) and latent variance4/(1+4n), including n=0.',
    'Latent variance strictly decreases; actual posterior mean tends to2, not0; actual variance and standard deviation tend to0.',
    'For three identical observations2, exact mean24/13 and variance4/13, rigorous nearest-six-decimal displays1.846154/2.955554/59.955554, conditional heating acceptance at nominal57.',
    'The repeated dataset and midpoint dataset have different actual Gram entries and labels; no claim they can be pooled without a fresh joint posterior.']},
  {'scope':'current node948 and current node955 under their explicitly supplied envelope/discrepancy hypotheses',
   'conclusions':['Actual midpoint kernel/regularizer inverse and posterior mean6/7 and variance10/7.',
    'Both unknown terms are bounded separately under the displayed absolute-value hypotheses; a positive deterministic target discrepancy is allowed, so zero-mean independent noise is not inferred.']},
  {'scope':'current entire Exercise3.B2 and current node959','whole_scope_expected_pending':True,
   'remaining_gap':'The current literal treats rounded3.247600+0.4 as an exact physical upper bound. The exact modeled upper bound is strictly larger than3.247600; the exact radical complement is required for the maximal safe nominal.'},
  {'scope':'prospective corrected entire Exercise3.B2 and corrected node959 conditional on actual later source application',
   'conclusions':['Actual matrix posterior correspondence, not an assumed scalar answer.',
    'Exact physical residual maximum6/7+2sqrt(10/7)+2/5 is genuinely attained by admissible modeled residual and discrepancy.',
    'Safety for every admissible pair iff nominal≤60 minus that exact maximum; the largest nominal is safe and equality is attained.',
    'Nominal56.5 fails for a genuine admissible attaining residual; all unchanged six-decimal targets have strict half-unit rounding enclosures.',
    'A fixed two-location physical countermodel gives exactly the same repeated measurements2 at the observed location, satisfies the explicitly assumed modeled envelope at both locations for all n, and retains target discrepancy2/5 while actual posterior variance tends to0.',
    'No posterior-confidence probability, all-time plant guarantee, zero-mean discrepancy, or independence of the unmodeled term is inferred.']},
  {'scope':'old partial component gap associations only; no original statements, declarations, hypotheses, correspondence or times modified',
   'associations':[{'claim_id':exercises[0]['claims'][2]['id'],'old_gap':exercises[0]['claims'][2]['remaining_gaps'],
      'proposed_actual_support':['repeated_ridge_actual_inverse','repeated_inverse_constant_action','repeated_actual_posterior','repeated_regularized_solution_unique'],
      'mathematical_discharge_requested':True},
     {'claim_id':exercises[1]['claims'][4]['id'],'old_gap':exercises[1]['claims'][4]['remaining_gaps'],
      'proposed_actual_support':['all_admissible_residuals_safe_iff','physical_residual_greatest','repeated_true_function_in_assumed_envelope'],
      'mathematical_discharge_requested':False,
      'scope_note_remains_true':'The confidence event is explicitly supplied as a hypothesis in the complete source. The requested whole decision is conditional. No probabilistic coverage theorem is proved or claimed; independent reviewer must distinguish this inherited scope note from an unresolved source conclusion.'}]}],
 'original_closed_byte_aliases':aliases,'required_evidence_artifacts_sha256':{r['file']:r['sha256'] for r in aliases.values()},
 'source_number_reserved':False,'source_applied':False,'canonical_pairs_executed':False,'whole_promotion_performed':False,
 'independent_full_semantic_review_pending':True,'coverage_complete':False,'supplementary_after_frozen29_manifest':True}
for r in [d['original_owner29_candidate'],d['current_inventory']]:d['required_evidence_artifacts_sha256'][r['file']]=r['sha256']
O=B/'modules-physical-gp34-full-source-literal-independent-review-request30-v1.json'
O.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'request':O.relative_to(R).as_posix(),'sha256':sha(O),'bytes':O.stat().st_size,
 'closed_refs':len(d['required_evidence_artifacts_sha256']),'aliases':len(aliases),
 'warning_counts':[x['actual_warning_count'] for x in history]}))
