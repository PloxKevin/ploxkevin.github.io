from pathlib import Path
from fractions import Fraction as F
import hashlib,json,re,sys
R=Path('/home/oxrexkevin/SafetyBased');Q=Path('/tmp/foundations-explorer7-two-captions-review31-v1/foundations-explorer7-full-source-current1437-1452-two-captions-independent-review-request31-v1.json');B=Path('/tmp/foundations-explorer7-independent-modules31-v1')
assert not B.exists();B.mkdir()
sys.dont_write_bytecode=True;sys.path.insert(0,str(R/'book/coverage'));import lean_names
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def path(r):
 p=Path(r['file']);return p if p.is_absolute()else R/p
def ref(p):
 p=Path(p);return {'file':str(p),'sha256':sha(p),'bytes':p.stat().st_size}
assert sha(Q)=='ca5166fe3a570b79b1b8351917ab12ca02c005a0ef0b80a50711a3599bfb385a';q=json.loads(Q.read_bytes())
for p,h in q['all_physical_original_inputs_sha256'].items():assert sha(p)==h
for old,r in q['all_original_byte_aliases'].items():assert sha(path(r))==r['sha256']
t=path(q['final_actual_passed_source']).read_text();names=[d['name'].removeprefix('SafeLearning.CompleteFoundationsExplorerCaptionModels31.')for d in lean_names.declarations(t)if d['kind']in ['theorem','lemma']]
assert names==q['public_theorem_names']and len(names)==q['public_theorem_count']==7
assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by|run_elab|ofReduceBool|sorryAx)\b',lean_names.without_comments(t))
inv=json.loads(path(q['current_inventory']).read_bytes());units={r['key']:r for r in inv['material_source_units']}
for k,u in q['entire_current_literals'].items():assert u==units[k]
owner=json.loads(path(q['current_installed30_foundations_owner']).read_bytes());rows={r['id']:r for r in owner['material_claims']}
for r in q['entire_current_pending_rows']:assert r==rows[r['id']]and r['status']=='pending'and r['lean_declarations']==[]
page=path(q['current_source']).read_text();js=q['full_explorer_JS_lines1781_1964'];html=q['full_explorer_context_lines1460_1497']
assert html==''.join(page.splitlines(keepends=True)[1459:1497]);assert js==''.join(page.splitlines(keepends=True)[1780:1964])
for s in ['id="p0-g" min="0" max="0.995" step="0.005"','id="p0-T" min="1" max="300"']:assert s in html
assert "Math.pow(R.L, i - R.k0) * R.d / (1 - R.L)"in js
assert "R.d = Math.abs(xs[R.k0 + 1] - xs[R.k0])"in js
assert "R.k0 = 2"in js and "xs[k] >= Math.cos(1)"in js
for s in ["pl(pts, '#1565c0'","sy(hi), '#9e9e9e'","stroke=\"#e67e22\"","stroke=\"#2e7d32\"","stroke-dasharray=\"5,4\"","fill=\"#1565c0\"","pl(a, '#1565c0'","pl(b, '#00838f'","'#7b1fa2'","(off the plot)"]:
 assert s in js,s
hist=[]
for i,h in enumerate(q['genuine_original_compiler_histories']):
 n=json.loads(path(h['native']).read_bytes());raw=path(h['raw_log']).read_bytes()
 assert n['actual_exit_code']==n['actual_runner_exit_code']==h['actual_exit_code']==[1,0][i]and n['protection_errors']==[]and n['source_unchanged']
 for key,nkey in [('source','source_sha256_before'),('snapshot','source_snapshot_sha256'),('raw_log','raw_log_sha256')]:assert sha(path(h[key]))==h[key]['sha256']==n[nkey]
 assert n['source_sha256_before']==n['source_sha256_after']==n['source_snapshot_sha256']
 assert n['actual_command']==['lake','env','lean',n['source']]and n['actual_workdir']==str(R/'verification/lean')
 assert len(re.findall(rb'^.*?:\d+:\d+: warning:',raw,re.M))==h['emitted_diagnostic_warning_headers']==0
 for k in ['started_at_utc','finished_at_utc','elapsed_seconds']:assert h[k]==n[k]
 hist.append(h)
assert path(hist[-1]['raw_log']).read_bytes()==b''
a=json.loads(path(q['actual_all200_admitted_slider_horizons_exact_arithmetic_validation']).read_bytes());v=json.loads(path(q['actual_all200_validation_native']).read_bytes())
assert a['actual_exit_code']==v['actual_exit_code']==0 and v['protection_errors']==[]
assert a['actual_source_expression']in js and len(a['individual_checks'])==200
for i,c in enumerate(a['individual_checks']):
 assert c['numerator']==i and c['denominator']==200 and c['actual_admitted_value']==i/200
 g=F(i,200);T=c['actual_horizon'];assert T>=1 and g**T<=F(1,100)and g**(T-1)>F(1,100)
for r in [a['raw_stdout'],a['raw_stderr']]:assert sha(path(r))==r['sha256']
for p,h in v['helper_sha256_before'].items():assert sha(p)==h==v['helper_sha256_after'][p]
assert sha(v['log'])==v['log_sha256']
prep=Path('/tmp/foundations-explorer7-two-captions-review31-preparation-actual-v1.json');pn=json.loads(prep.read_bytes());assert pn['actual_exit_code']==0 and pn['protection_errors']==[]
for p,h in pn['helper_sha256_before'].items():assert sha(p)==h==pn['helper_sha256_after'][p]
assert sha(pn['log'])==pn['log_sha256']
decision1437={'inventory_key':'primer-basics.html::node-1437','entire_current_literal':units['primer-basics.html::node-1437'],'current_whole_literal_approved':True,'remaining_gaps':[],'exact_support':names[5:],'correspondence':'The actual closed nonempty invariant-domain Banach proof derives the fixed point and iteration error, then exact iterate composition shifts the start to k0 without assuming convergence. The bound is conditional on a valid contraction factor on that complete invariant domain and applies for k>=k0. Actual widget code uses the same difference, exponent and denominator; affine/cosine/eligible logistic branches set L, with the cosine orbit entering its invariant interval by k0<=2. The cobweb code emits the blue map curve, grey diagonal, orange vertical/horizontal iterate staircase and green fixed-point marker, while dots and dashed curve carry the displayed quantities. These are plotted mathematical roles; floating-point cosine equality and neighboring empirical map claims are not asserted.'}
decision1452={'inventory_key':'primer-basics.html::node-1452','entire_current_literal':units['primer-basics.html::node-1452'],'current_whole_literal_approved':True,'remaining_gaps':[],'exact_support':names[:5],'correspondence':'Actual generic geometric prefix, tail and positive total give exactly the two fractions for every natural horizon and every0<=gamma<1, including gamma0. The true minimum index is derived, not assumed; positive gamma has the logarithmic cutoff and gamma0 has exact minimum1. The actual source-extracted Node horizon output has the exact minimum at each of the200 admitted slider values, verified independently with Fraction powers at both adjacent indices. Actual code assigns blue collected, teal remaining, orange chosen horizon and purple first1percent horizon; if the latter exceeds the displayed300 cap, its purple off-plot label retains the exact index.'}
d={'status':'passed_independent_explorer7_full_source_current1437_1452_individual_whole_literal_review','errors':[],'reviewer':'/root/modules_finish28','request':ref(Q),'source':q['final_actual_passed_source'],'all7_entire_public_bodies_all3_definitions_both_entire_selected_sources_read':True,'individual_decisions':[decision1437,decision1452],'entire_original_pending_rows':q['entire_current_pending_rows'],'full_explorer_HTML_context':html,'full_actual_explorer_JS':js,'selected_sources':q['entire_complete_selected_dependencies'],'complete_primary_files':q['complete_used_primary_files'],'used_primary_full_proof_bodies_read':['Actual geometric finite sum from telescoping product, positive geometric HasSum and geometric decay','Banach Cauchy sequence construction, completeness/fixedpoint uniqueness and actual a-priori iterate error','Lipschitz iterate contraction and successor error bound','Function iterate addition/successor identities','Exact log inequality and multiplication by a negative logarithm in the full selected geometric model'],'actual_all200_submitted_implementation_validation':q['actual_all200_admitted_slider_horizons_exact_arithmetic_validation'],'actual_all200_native':q['actual_all200_validation_native'],'independent_all200_exact_Fraction_adjacent_thresholds_verified':True,'original_validation_exact_helpers':[ref(p)for p in v['helper_sha256_before']],'original_validation_exact_raw_log':ref(v['log']),'author_preparation':ref(prep),'author_preparation_helpers':[ref(p)for p in pn['helper_sha256_before']],'author_preparation_log':ref(pn['log']),'author_preparation_wrapper':ref('/tmp/run-foundations-explorer7-two-captions-review31-preparation-v1.py'),'genuine_original_compiler_histories':hist,'visual_and_float_scope':'Entire source formulas, literal color assignments and plotting paths were read. Generic mathematics is supplied by Lean; the discrete200-value JS threshold check is supplementary. No browser session, exact floating-point cosine root, generic JS rounding theorem, or every plotted pixel is claimed.','original_owner_rows_and_all_true_history_body_times_preserved':True,'parent1430_or_neighbor1453_or_empirical_cycles_chaos_promotion':False,'source_applied':False,'compiler_or_owner_source_canonical_publication_mutation':False,'coverage_complete':False}
O=B/'foundations-explorer7-full-two-current-captions-independent-modules31-peer-v1.json';O.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'peer':ref(O),'whole':['1437','1452']}))
