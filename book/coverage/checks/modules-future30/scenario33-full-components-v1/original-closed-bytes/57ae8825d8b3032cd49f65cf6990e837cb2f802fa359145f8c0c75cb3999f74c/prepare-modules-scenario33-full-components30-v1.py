from pathlib import Path
import hashlib,json,importlib.util,re,sys
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased')
B=R/'book/coverage/checks/modules-future30/scenario33-full-components-v1'
assert not B.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):
 p=Path(p);return {'file':p.relative_to(R).as_posix() if p.is_relative_to(R) else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
aliases={}
def copy(p):
 p=Path(p);q=B/'original-closed-bytes'/sha(p)/p.name;q.parent.mkdir(parents=True,exist_ok=True)
 if not q.exists():q.write_bytes(p.read_bytes())
 assert sha(q)==sha(p)
 z=ref(q);aliases[str(p)]=z;return z
S=Path('/tmp/CompleteModulesScenarioSamplesExact30-draft-v5.lean')
N=[Path('/tmp/modules-scenario-samples-exact30-owner29-trial'+str(i)+'.json') for i in range(1,4)]
final=json.loads(N[-1].read_bytes())
assert final['actual_exit_code']==final['actual_runner_exit_code']==0 and not final['protection_errors']
assert sha(S)==final['source_sha256_before']==final['source_sha256_after']=='a2d8517db80696b443b571018c89881a83f51507b47b480e73fa401e390b2826'
I=R/'book/coverage/inventory-after-correction65.json'
O=R/'book/coverage/checks/modules-future29/current65-pair-bound-v7/modules29-current65-two-source-pair-bound-candidate-v1.json'
P=R/'SafeLearning/verification.html'
assert sha(I)=='5f68ee3c68c1da1275a0a2667fe43b42263b8fc31800a834371de5bfbed01b68'
assert sha(O)==sha(R/'book/coverage/modules.json')=='13a1955d1920b9eafec20b5b38d7e10800354db71188c154f0967a93bccbc22d'
assert sha(P)=='2b60f48b0b374ab75902df099a19d28289b1e107ba2e23187c2b1e348f7d52cb'
inv=json.loads(I.read_bytes());owner=json.loads(O.read_bytes())
exercise=next(e for e in inv['exercises'] if e['key']=='verification.html::exercise-19')
oldexercise=next(e for e in owner['exercises'] if e['inventory_key']==exercise['key'])
units=[u for u in inv['material_source_units'] if u['source']=='SafeLearning/verification.html' and 863<=u['line']<=878]
keys={u['key'] for u in units}
oldrows=[r for r in owner['material_claims'] if keys.intersection(r.get('source_unit_keys',[])) or r.get('source_unit_key') in keys or r.get('inventory_key') in keys]
B.mkdir(parents=True)
sp=importlib.util.spec_from_file_location('scenario33_names',R/'book/coverage/lean_names.py');m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m)
declarations=m.declarations(S.read_text());names=[x['name'] for x in declarations if x['kind'] in ['theorem','lemma']]
assert len(names)==33 and len(declarations)==39
hist=[]
for p in N:
 j=json.loads(p.read_bytes())
 assert j['source_unchanged'] and not j['protection_errors']
 assert j['actual_command']==['lake','env','lean',j['source']]
 assert j['actual_workdir']==str(R/'verification/lean')
 assert sha(j['source'])==sha(j['source_snapshot'])==j['source_sha256_before']==j['source_sha256_after']==j['source_snapshot_sha256']
 assert sha(j['raw_log'])==j['raw_log_sha256']
 hist.append({'actual_native':copy(p),'source':copy(j['source']),'source_snapshot':copy(j['source_snapshot']),'raw_log':copy(j['raw_log']),'actual_exit_code':j['actual_exit_code'],'actual_warning_headers':len(re.findall(r'^.*?:\d+:\d+: warning:',Path(j['raw_log']).read_text(),re.M)),'original_actual_times':{k:j[k] for k in ['started_at_utc','finished_at_utc','elapsed_seconds']}})
uncompiled=[{'source':copy('/tmp/CompleteModulesScenarioSamplesExact30-draft-v'+str(i)+'.lean'),'compiled':False,'historical_scope':'Unused offline local repairs; v2 included a statically caught indentation defect, corrected before v4 actual trial.'} for i in [2,3]]
selected=[]
for name in ['CompleteLyapunovScenarioNumbers23.lean','CompleteModulesGPNumerics.lean','CompleteAppliedDiscountedHorizons.lean','CompleteFoundationsExponentialNumerics.lean','CompleteAppliedBinomialModel.lean','CompleteAppliedValidation.lean']:
 p=R/'verification/lean/SafeLearning'/name
 selected.append({'source':ref(p),'entire_source':copy(p),'scope':'Existing selected source, full byte-exact file supplied for independent used-body/dependency reading. No new assertion about unrelated clauses.'})
primary=[]
for name in ['Data/Nat/Choose/Basic.lean','Data/Nat/Choose/Cast.lean','Algebra/Order/Ring/Abs.lean','Analysis/SpecialFunctions/Log/Basic.lean','Analysis/SpecialFunctions/Exp.lean','MeasureTheory/Measure/OpenPos.lean','MeasureTheory/Measure/Prod.lean','Data/Set/Prod.lean']:
 p=R/'verification/lean/.lake/packages/mathlib/Mathlib'/name
 primary.append({'original_package_path_historical_metadata':str(p),'entire_physical_API_source':copy(p)})
for p in [__file__,'/tmp/run-modules-scenario33-full-components30-preparation-v1.py','/tmp/root_tmp_lean_current65_owner29_context_v1.json','/tmp/root_tmp_lean_current65_owner29_runner_v1.py',R/'book/coverage/lean_names.py']:
 copy(p)
lines=P.read_text().splitlines(keepends=True)
request={'status':'prepared_scenario33_full_source_and_exact_current_literals_component_review_request',
 'source':copy(S),'public_theorem_count':len(names),'public_theorem_names':names,'public_declaration_count':len(declarations),'other_public_declarations':[d for d in declarations if d['kind'] not in ['theorem','lemma']],
 'genuine_original_native_history':hist,'genuine_native_codes':[h['actual_exit_code'] for h in hist],'genuine_warning_headers':[h['actual_warning_headers'] for h in hist],'uncompiled_historical_sources':uncompiled,
 'entire_current_exercise':exercise,'entire_original_owned_exercise_row':oldexercise,'entire_current_material_literals':units,'entire_original_material_rows':oldrows,
 'entire_current_page_original_byte_alias':copy(P),'entire_used_scenario_section_context':{'original_page':copy(P),'start_line_inclusive':457,'end_line_exclusive':520,'keepends_exact_full_html':''.join(lines[456:519])},
 'entire_exercise_context':{'original_page':copy(P),'start_line_inclusive':860,'end_line_exclusive':882,'keepends_exact_full_html':''.join(lines[859:881])},
 'current_inventory':ref(I),'immutable_original_owner29':ref(O),'complete_selected_sources':selected,'entire_physical_primary_API_sources':primary,
 'exact_components_requested':[
  {'scope':'Actual finite binomial tails and genuine least sample sizes','proof_scope':'Exact adjacent crossings642/643 atd10,beta10^-6 and1137/1138 atd36,beta10^-3, with generic tail successor/nonincrease, zeroth mass and all-n minimum proof. Existing lowerTail/actual independent count mass correspondence is supplied by selected ScenarioNumbers23.'},
  {'scope':'Actual 2006 support-union expression and its least design size','proof_scope':'Exact1395/1396 crossing and actual all-n minimum on natural sample-design domain n>=d=10. Below d the algebraic choose expression is0 and is not asserted to be a valid support-size design bound.'},
  {'scope':'Actual explicit logarithmic cutoffs and roundings','proof_scope':'True log enclosure derives ceilings953/1717, approximate display accuracy, and falsity of printed exact logarithm equalities. Original source precision remains unchanged and wholecurrent1202/1205/Ex19 is not requested.'},
  {'scope':'Actual Chernoff parameter domain and quadratic slack','proof_scope':'For d>=0,mu>0, t=1-d/mu belongs to[0,1] iff d<=mu; exact exponent identity retains d^2/(2mu), and positive-epsilon explicit rule puts the parameter in its domain. This does not assert a new general Bernoulli Chernoff probability theorem.'},
  {'scope':'Actual common-Lyapunov parameter count and sample comparison','proof_scope':'2*4^2+4=36 and exact ordering643<953<1396,1138<1717, roughly50% explicit overhead.'},
  {'scope':'Actual scalar adaptive-design infeasibility mechanism','proof_scope':'For B>0 actual stability iff printed open gain interval. Nonempty OPEN plant neighborhoods around(3,1) and(-3,1) require opposite signs, hence no common gain and no positive common scalar Lyapunov certificate. Full-support independent pair law has strictly positive probability of infeasibility; full support is stated precisely as IsOpenPosMeasure, not inferred for an unspecified posterior.'},
  {'scope':'Actual scalar fixed-gain distinction and unbounded-support countermodel','proof_scope':'Every fixed scalar gain has a nonempty open unstable region with positive full-support mass; A=0,K=0 stabilizes all B. Thus fixed-gain instability and unbounded B support do not imply adaptive sampled design infeasibility.'}],
 'whole_current_exercise_requested':False,'whole_current_exercise_expected_pending':True,
 'explicit_remaining_whole_associations':['Rounded logarithms/decimal computation equality signs require separate literal correction.','The paper matrix-normal posterior full-support identification is not derived by these scalar theorems.','A robust incompatible MATRIX sample family and its precise actual initial LMI feasibility association are not yet supplied.','Full generic Campi-Garatti tightness and old-union-bound distribution-free theorem domains are separate existing/primary-source associations, not inferred from numerical tail evaluation.','Paper truncation reason/unstabilizable truncated support/improvement-vs-scenario and final Hoeffding factual attribution require full primary used-scope review.'],
 'primary_paper_URLs_for_following_attribution_scope':['https://proceedings.mlr.press/v144/rohr21a/rohr21a.pdf','https://marco-campi.unibs.it/pdf-pszip/Campi-Garatti-exact.pdf'],
 'source_ordinal_reserved':False,'source_applied':False,'whole_promotion_performed':False,'canonical_pairs_executed':False,'independent_full_semantic_review_pending':True,'compiler_or_parser_started_by_preparation':False,'coverage_complete':False,'supplementary_after_frozen29_manifest':True,
 'original_closed_byte_aliases':aliases,'required_evidence_artifacts_sha256':{v['file']:v['sha256'] for v in aliases.values()}}
for p in [I,O]:request['required_evidence_artifacts_sha256'][ref(p)['file']]=sha(p)
p=B/'modules-scenario33-full-source-current-literals-component-independent-review-request30-v1.json'
p.write_text(json.dumps(request,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'request':ref(p),'public_theorems':len(names),'public_declarations':len(declarations),'native_codes':request['genuine_native_codes'],'warnings':request['genuine_warning_headers'],'closed_refs':len(request['required_evidence_artifacts_sha256'])}))
