import json,hashlib,pathlib,re,datetime
R=pathlib.Path('/home/oxrexkevin/SafetyBased'); OUT=pathlib.Path('/tmp/root-mpc-local-bootstrap27-independent-modules-full-component-review-v1.json')
assert not OUT.exists()
def path(n): return pathlib.Path(n) if n.startswith('/') else R/n
def sha(n): return hashlib.sha256(path(n).read_bytes()).hexdigest()
def ref(n): return {'file':n,'sha256':sha(n)}
def read(n):return json.loads(path(n).read_text())
SOURCE='/tmp/CompleteCoreMPCLocalBootstrap27-draft-v4.lean'; TEXT=path(SOURCE).read_text(); EXPECT='39f7fbe849ab0e4ade3d2fb77941cc597ba8c93ba2beb0c351436392167a90cd'
assert sha(SOURCE)==EXPECT
NAMES=re.findall(r'^theorem ([A-Za-z0-9_]+)',TEXT,re.M); assert len(NAMES)==3
assert 'sorry' not in TEXT and 'axiom ' not in TEXT
TRIAL='/tmp/root-mpc-local-bootstrap27-trial2.json'; T=read(TRIAL)
assert type(T['actual_exit_code']) is int and T['actual_exit_code']==0
assert T['actual_command']==['lake','env','lean',SOURCE] and T['protection_errors']==[]
for k in ['source_sha256_before','source_sha256_after','source_snapshot_sha256']:assert T[k]==EXPECT
assert sha(T['source_snapshot'])==EXPECT and sha(T['raw_log'])==T['raw_log_sha256']
assert path(T['raw_log']).read_text().count('warning:')==3
FIRST='/tmp/root-mpc-local-bootstrap27-trial1.json'; F=read(FIRST)
assert type(F['actual_exit_code']) is int and F['actual_exit_code']==1 and F['protection_errors']==[]
assert sha(F['source_snapshot'])==F['source_snapshot_sha256']==F['source_sha256_before']==F['source_sha256_after']
assert sha(F['raw_log'])==F['raw_log_sha256']; assert 'Unknown identifier `le_norm_self`' in path(F['raw_log']).read_text()
INV='book/coverage/inventory.json'; I=read(INV); assert sha(INV)=='4b1e657eb61234a6d2e2a3a3ea6a0b11986c01d7d1c7cb5ba2dd5452d1fe29be'
UNITS=[r for r in I['material_source_units'] if r['key'] in ['lyapunov-mpc.html::node-737','lyapunov-mpc.html::node-739']]; assert len(UNITS)==2
for u in UNITS:assert sha(u['source'])==u['source_sha256'] and hashlib.sha256(u['source_text'].encode()).hexdigest()==u['text_sha256']
assert all('continuous' not in u['source_text'].lower() for u in UNITS)
PRIMARY='sources/text/hertneck.txt'; assert sha(PRIMARY)=='f0d8687a0368e2c4eec9ea3a6bad70ea5456793c5a275b9c0f1b4a8942746c97'
PL=path(PRIMARY).read_text().splitlines(); REGION='\n'.join(PL[165:234]); assert 'continuous in the first argument' in REGION
SEL='reports/full-coverage/checkpoint-26-selection.json'; S=read(SEL); assert sha(SEL)==T['actual_installed26_selection']['sha256']; assert len(S['proof_files'])==1167
BROWSER='reports/full-coverage/browser-corrections-26-inputs.json'; B=read(BROWSER); assert len(B['source_sha256'])==31
GUARDS={**{n:r['sha256'] for n,r in S['proof_files'].items()},**B['source_sha256'],**T['installed26_owner_sha256']}
for n,h in GUARDS.items():assert sha(n)==h,(n,h,sha(n))
EVIDENCE={n:sha(n) for n in [SOURCE,TRIAL,T['source_snapshot'],T['raw_log'],FIRST,F['source'],F['source_snapshot'],F['raw_log'],INV,PRIMARY,SEL,BROWSER,'/tmp/root_tmp_lean27_runner_v2.py','/tmp/CompleteCoreMPCLocalBootstrap27-draft-v1.lean','/tmp/CompleteCoreMPCLocalBootstrap27-draft-v2.lean','/tmp/root-mpc-local-bootstrap27-independent-applied-semantic-review-v1.json']}
PREFIX='SafeLearning.CompleteCoreMPCLocalBootstrap27.'
GROUPS=[
 {'id':'continuous_local_first_crossing_bootstrap','declarations':[PREFIX+NAMES[0]],'status':'approved_precise_component','missing_clauses':[],'hypotheses':['V continuous on [0,1], V(0)=0','delta>0, 0<=c<=delta','For each t in [0,1], only when V(t)<=delta, V(t)<=c*t^2'], 'reason':'The proof does not assume the endpoint lies in the local sublevel. If V(1)>delta, the intermediate value theorem gives 0<t<1 with V(t)=delta. The conditional local estimate and c<=delta then give delta<=c*t^2<=delta*t^2<delta, contradiction. At the endpoint the local estimate yields V(1)<=c. Positivity of delta supplies the strict inequality even at c=delta.'},
 {'id':'actual_convex_state_path_bootstrap','declarations':[PREFIX+NAMES[1]],'status':'approved_precise_component','missing_clauses':[],'hypotheses':['Real normed state space, convex X; both z and x belong to X','V continuous on X, V(z)=0','delta>0,cU>=0,cU*norm(x-z)^2<=delta','Conditional upper quadratic bound for every y in X with V(y)<=delta'], 'reason':'The actual path z+t*(x-z) lies in X by convexity. Composition gives continuous V along that path; its endpoints are z and x. Norm homogeneity for 0<=t<=1 transforms the local estimate into c*t^2 with c=cU*norm(x-z)^2. The first-crossing theorem therefore proves the small-error endpoint estimate without assuming V(x)<=delta.'},
 {'id':'actual_linear_constraint_margin_under_bounded_state_error','declarations':[PREFIX+NAMES[2]],'status':'approved_precise_component','missing_clauses':[],'hypotheses':['Rows are real continuous linear functionals on the chosen normed state space','H>=0 and every row operator norm<=H','Every nominal row value<=1-margin','norm(x-z)<=radius and H*radius<=margin'], 'reason':'Actual linearity writes row(x)=row(z)+row(x-z). The continuous-linear-map operator bound controls the latter term by H*norm(x-z)<=H*radius. Nominal tightening plus the margin inequality then proves every actual row(x)<=1. The generic theorem does not silently substitute a coordinate sup norm for the chosen state norm.'}
]
GAPS=[
 {'id':'missing_primary_continuity_in_current_site','status':'prerequisite_and_source_correction_needed','reason':'The primary Assumption 1 expressly says V_delta is continuous in its first argument. Current complete node737/739 does not state that condition. Both bootstrap theorems require it; this review does not infer continuity from the displayed conditional quadratic bounds. A later reviewed source correction must explicitly retain it.'},
 {'id':'state_domain_and_norm_identification','status':'explicit_application_bridge_pending','reason':'The state-path theorem requires both endpoints in convex X. For the paper, X is a polytopic state set and V(y)=V_delta(y,z,v) for fixed nominal z and v. The margin lemma can establish endpoint membership only after the actual matrix rows and their bounds are instantiated. None of these three declarations exports Euclidean row-operator norm<=the printed matrix infinity row-sum bound, or the actual input-infinity disturbance through Assumption 2 to the Euclidean state radius lambda*eta.'},
 {'id':'complete_robust_MPC_certificate','status':'pending_outside_three_components','reason':'These declarations do not prove the complete incremental-feedback contraction/input tightening pipeline, predicted shifted-plan feasibility, online optimizer existence, all-horizon robust MPC recursion or the full Theorem5/certificate. No whole Exercise18, material1387 or assumption-definition approval follows.'}
]
REVIEW={'status':'passed_independent_full_source_precise_component_review','errors':[],'reviewer':'modules','reviewed_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source':ref(SOURCE),'entire_source':TEXT,'all_public_theorem_names':[PREFIX+n for n in NAMES],'all_three_complete_proof_bodies_read':True,'components':GROUPS,'whole_exercise_approved':False,'whole_material_unit_approved':False,'source_literal_bindings':UNITS,'current_source_context':{'file':'SafeLearning/lyapunov-mpc.html','sha256':sha('SafeLearning/lyapunov-mpc.html'),'complete_lines504_514':'\n'.join(path('SafeLearning/lyapunov-mpc.html').read_text().splitlines()[503:514])},'primary_source':ref(PRIMARY),'primary_complete_lines166_234':REGION,'primary_additional_domain_and_notation_context_lines78_149':'\n'.join(PL[77:149]),'norm_convention':'State norm instantiated as Euclidean as in primary; additive input disturbance uses infinity norm. Generic theorem3 continuous-linear-row operator norms belong to the chosen state norm. No automatic identification with printed matrix infinity norm is claimed.','remaining_gaps':GAPS,'actual_standalone_execution':{'record':ref(TRIAL),'entire_original_record':T,'raw_log':ref(T['raw_log'])},'original_failed_trial_preserved':{'record':ref(FIRST),'entire_original_record':F,'raw_log':ref(F['raw_log'])},'original_prior_applied_semantic_review':{'record':ref('/tmp/root-mpc-local-bootstrap27-independent-applied-semantic-review-v1.json'),'entire_original_body':read('/tmp/root-mpc-local-bootstrap27-independent-applied-semantic-review-v1.json'),'scope':'Original earlier two-component review retained without retiming; the present independent three-component read has its own time.'},'evidence_sha256':EVIDENCE,'protected_counts':{'selected_proof_sources':1167,'current_book_assets':31,'installed_owner_files':5},'limits':['Read-only independent source correspondence and actual evidence check; no new Lean compile.','TMP only, no canonical source/named build, live owner mutation or aggregate verification.','Three complete conditional components only; explicit continuity omission and norm/application bridges retained.']}
for n,h in GUARDS.items():assert sha(n)==h
OUT.write_text(json.dumps(REVIEW,ensure_ascii=False,indent=2)+'\n');print(json.dumps({'output':str(OUT),'sha256':sha(str(OUT)),'components':3,'remaining_gaps':3,'status':REVIEW['status']}))
