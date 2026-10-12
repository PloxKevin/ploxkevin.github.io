from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,importlib.util,re,copy
R=Path('/home/oxrexkevin/SafetyBased')
REQ=R/'book/coverage/checks/modules-future29/scalar-lipsdp42-and-source65-v1/modules-scalar-lipsdp42-full-scope-independent-review-request29-current64-v3.json'
OUT=Path('/tmp/scalar-lipsdp42-independent-applied-findings29-v2.json')
def H(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def J(p):return json.loads(Path(p).read_bytes())
def P(n):return Path(n) if Path(n).is_absolute() else R/n
def ref(p):return {'file':str(p.relative_to(R))if p.is_relative_to(R)else str(p),'sha256':H(p)}
assert H(REQ)=='bd4713b7af70e431b54e9de65cbd377aed5d3d88eb35ea4b409c44adb6fac52d'
d=J(REQ);ctxpath=Path('/tmp/root_tmp_lean_current64_owner28_context_v1.json')
assert H(ctxpath)=='442590b45444a97af4b12a37b9ee3f6166b6118a85516e339c6d55bb0c33c6e0'
ctx=J(ctxpath);held={}
for m in (ctx['pins_sha256'],ctx['held_current_source_sha256'],ctx['owners_sha256']):
 for n,h in m.items():assert n not in held or held[n]==h;held[n]=h
def guard():
 for n,h in held.items():assert H(P(n))==h,n
guard()
for n,h in d['required_evidence_artifacts_sha256'].items():
 p=P(n);assert p.resolve().is_relative_to(R),n
 assert H(p)==h,n
for n,a in d['original_closed_byte_aliases'].items():assert H(P(a['file']))==a['sha256'],n
s=P(d['proof_source']['file']);assert H(s)==d['proof_source']['sha256']=='614b44c904a7401dd285fa542a2c5ff16a48c3f2baa13b22b5b08e5ddbfc7608'
text=s.read_text();assert text==d['entire42_public_bodies_and_definitions']
spec=importlib.util.spec_from_file_location('lean_names',R/'book/coverage/lean_names.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
names=m.declarations(text);theorems=[x['name']for x in names if x['kind']in ('theorem','lemma')]
assert theorems==d['public_theorem_names'] and len(theorems)==d['public_theorem_count']==42
assert len(names)==52 and len({x['name']for x in names})==52
assert not re.search(r'\b(sorry|axiom|admit)\b',m.without_comments(text))
alltrials=d['seven_genuine_native_trials_all_bodies_times_preserved']+[d['eighth_genuine_current64_trial_same42_source']]
history=[]
for i,row in enumerate(alltrials):
 a=J(P(row['actual_native']['file']));raw=P(row['raw_log']['file']);snapshot=P(row['source_snapshot']['file'])
 for r in (row['actual_native'],row['raw_log'],row['source_snapshot']):assert H(P(r['file']))==r['sha256']
 for k in ('actual_exit_code','actual_runner_exit_code'):
  assert type(a[k])is int and a[k]==row[k]
 assert a['actual_exit_code']==[1,1,1,1,0,1,0,0][i] and a['protection_errors']==[]
 assert a['source_sha256_before']==a['source_sha256_after']==a['source_snapshot_sha256']==H(snapshot)
 assert a['actual_command']==['lake','env','lean',a['source']]
 assert a['actual_workdir']==str(R/'verification/lean')
 assert H(raw)==a['raw_log_sha256'] and a['source_unchanged']is True
 warnings=len(re.findall(r'^.*?:[0-9]+:[0-9]+: warning:',raw.read_text(),re.M))
 assert warnings==row['actual_emitted_warning_count']==[0,6,4,6,5,5,6,6][i]
 for k in ('started_at_utc','finished_at_utc','elapsed_seconds'):assert a[k]==row[k]
 history.append({'original_native':row['actual_native'],'raw_log':row['raw_log'],'source_snapshot':row['source_snapshot'],'actual_exit_code':a['actual_exit_code'],'actual_warning_headers':warnings,'original_started_at_utc':a['started_at_utc'],'original_finished_at_utc':a['finished_at_utc']})
assert alltrials[-1]['source_snapshot']['sha256']==H(s)
old25=P(d['original_closed_byte_aliases']['/tmp/CompleteModulesScalarLipSDPOptimum29-draft-v5.lean']['file']).read_bytes()
closing=b'end SafeLearning.CompleteModulesScalarLipSDPOptimum29\n'
assert old25.endswith(closing) and s.read_bytes().startswith(old25[:-len(closing)])
inv=J(P(d['actual_current64_inventory']['file']));ex=next(r for r in inv['exercises']if r['key']=='lipsdp.html::exercise-19')
assert ex==d['entire_current_exercise']
keys=['lipsdp.html::node-'+str(n)for n in [1320,1324,1326,1327,1328,1329]]
current={r['key']:r for r in d['entire_current_six_material_literals']}
assert list(current)==keys
for k,r in current.items():
 assert r==next(x for x in inv['material_source_units']if x['key']==k)
 assert hashlib.sha256(r['source_text'].encode()).hexdigest()==r['text_sha256']
owner=J(R/'book/coverage/modules.json')
assert d['entire_current_owned_exercise_row']==next(x for x in owner['exercises']if x['inventory_key']==ex['key'])
for row in d['entire_current_owned_six_unit_claim_rows']:
 assert row==next(x for x in owner['material_claims']if x['id']==row['id'])
page=P(d['actual_current64_source_snapshot']['file']);assert H(page)==H(R/'SafeLearning/lipsdp.html')
assert ''.join(page.read_text().splitlines(keepends=True)[1006:1026])==d['full_current_context1007_1026']
proposal=J(P(d['actual_current64_source65_narrow_proposal']['file']))
proposed=J(P(proposal['proposed_full29_inventory']['file']))
newex=next(x for x in proposed['exercises']if x['key']==ex['key'])
assert newex==d['entire_prospective_corrected_exercise']
newunits={x['key']:x for x in proposed['material_source_units']if x['key']in keys}
for row in d['entire_prospective_corrected_d_e_units']:assert row==newunits[row['key']]
for k in keys[:4]:assert newunits[k]['source_text']==current[k]['source_text'] and newunits[k]['text_sha256']==current[k]['text_sha256']
assert 'there is no finite multiplicative ratio' in newunits[keys[4]]['source_text']
assert 'eigenvalues $-1.3181$ and $0$' in newunits[keys[5]]['source_text']
runtime=J(P(d['actual_exact_rational_grid_and_matrix_runtime']['file']));assert type(runtime['actual_exit_code'])is int and runtime['actual_exit_code']==0
assert runtime['status']=='passed' and runtime['protection_errors']==[]
result=J(P(d['actual_exact_grid_result']['file']))
assert result['actual_valid_grid_count']==3755 and result['unique_argmin_k']==[490]
assert result['actual_optimal_t']=='49/100' and result['actual_optimal_rho']=='8281/10000'
assert result['exact_eigenvalues']==['0','-13181/10000'] and result['actual_three_decimal_rounding']=='-1.318'
assert H(P(d['complete_selected_Modules_source']['file']))==d['complete_selected_Modules_source']['sha256']
for api in d['primary_API_full_used_definitions_and_proof_bodies_to_read']:assert H(P(api['file']))==api['sha256']
guard()
groups=[
 {'part':'a','approved':True,'scope':'Real symmetric sourceMatrix quadratic expansion and negative-semidefinite convention (-M).PosSemidef; all real entries and nonzero weights are the printed scalar model.','declarations':theorems[:1]},
 {'part':'b','approved':True,'scope':'For t>w1²/2, exact Schur completion iff rho>=w0²g(t); genuine IsLeast fixed-t feasible rho. Every feasible t lies in this strict domain under 0<=alpha<beta and both nonzero weights.','declarations':theorems[1:5]},
 {'part':'c','approved':True,'scope':'Actual first and iterated second derivative, positive g second derivative and StrictConvexOn; actual stationary equation/root and square gap give unique attained global optimum t*=beta*w1²/(beta-alpha), rho*=beta²w0²w1².','declarations':theorems[5:13]+theorems[16:20]},
 {'part':'d','approved':True,'scope':'Genuine global slope restriction derives monotonicity and Lipschitz/absolute continuity, derivative integral identity proves derivative supremum is least activation constant without differentiability everywhere. Nonzero affine input is onto and nonzero output scale give exact network least constant. Interval all-pattern maximum and product bound equal beta|w0w1|; derivative supremum approach property and true ReLU/tanh/sigmoid witnesses yield1/1/1/4. Positive ratio and constant-zero exception support corrected65 only.','declarations':theorems[13:16]+theorems[20:35]},
 {'part':'e','approved':True,'scope':'Actual ReLU sharp constant yields .49/.8281/.91; exact source matrix, characteristic polynomial and two nonzero eigenvectors prove eigenvalues0/-1.3181 with three-decimal enclosure -1.318. Exact rational finite grid3755 valid k contains unique global optimizer k490; genuine Lean IsLeast plus closed exact Fraction runtime. Exact eigenvalue clause requires corrected65.','declarations':theorems[35:]}
]
decisions=[]
for k in keys:
 ok=k not in keys[4:]
 decisions.append({'key':k,'entire_current_literal':copy.deepcopy(current[k]),'whole_material_unit_approved':ok,
  'missing_source_claims':[]if ok else (['Multiplicative looseness ratio needs positive derivative supremum; constant activation has true constant0.']if k==keys[4]else['Exact eigenvalue is -1.3181; -1.318 is three-decimal rounding.']),
  'entire_prospective_corrected65_literal':copy.deepcopy(newunits[k]),'prospective_corrected65_whole_material_unit_approved':True,'prospective_missing_source_claims':[]})
out={'status':'passed_independent_full_scalar_lipsdp42_current_and_prospective65_semantic_review','errors':[],
 'reviewer':'/root/applied_next','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'request':ref(REQ),'proof_source':copy.deepcopy(d['proof_source']),
 'all42_complete_bodies_and10_definitions_independently_read':True,'full_selected_Modules_source_read':True,
 'primary_used_API_definitions_and_complete_proof_bodies_read':copy.deepcopy(d['primary_API_full_used_definitions_and_proof_bodies_to_read']),
 'primary_paper_scope':{'url':'https://arxiv.org/pdf/2005.02929','scope':'v2 SectionII.B slope restriction/QC/LipSDP matrix and least global Lipschitz definition; SectionIII.A Schur training formulation. Scalar exercise is proved from its actual mathematical model; no all-network tightness claim.'},
 'component_groups':groups,'exercise':{'key':ex['key'],'entire_current_literal':ex,'whole_exercise_approved':False,'missing_source_claims':['Unqualified finite ratio at zero true activation constant.','Exact negative eigenvalue printed only as rounded -1.318.'],
 'entire_prospective_corrected65_literal':newex,'prospective_corrected65_whole_exercise_approved':True,'prospective_missing_source_claims':[]},
 'material_units':decisions,'original_native_history':history,'exact_old25_prior_body_preserved_excluding_moved_namespace_end':True,
 'genuine_read_tool_schema_observation':{'exit_code':1,'scope':'An earlier read-only tool extraction accessed runtime helper as typed dict; original runtime helper field is a string. It stopped with TypeError before reading that helper; the corrected extraction fully read it. No Lean or checker failure, artifact write, altered native body or fabricated execution time.'},
 'no_compiler_or_parser_started_by_this_reader':True,'canonical_pair_approval_claimed':False,'current65_applied':False,'coverage_complete':False,
 'required_evidence_artifacts_sha256':copy.deepcopy(d['required_evidence_artifacts_sha256'])}
with OUT.open('x')as f:f.write(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'status':out['status'],'findings':ref(OUT),'all_theorems':42,'prospective_whole_exercise':True,'current_whole_units':4,'prospective_whole_units':6,'protected_sources':1186,'protection_errors':[]}))
