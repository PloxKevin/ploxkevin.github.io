from pathlib import Path
from datetime import datetime, timezone
import json, hashlib, re
ROOT=Path('/home/oxrexkevin/SafetyBased')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
R=lambda p:json.loads(Path(p).read_text())
OUT=Path('/tmp/modules-nn-tanh-seven-bridges24-independent-foundations-component-review-v1.json')
assert not OUT.exists()
def ref(p):return {'file':str(p),'sha256':H(p)}
def bind(r):
 p=Path(r['file']);assert H(p)==r['sha256'],str(p);return p
req3=Path('/tmp/modules-nn-tanh-offset24-three-bridges-review-request-v1.json')
req4=Path('/tmp/modules-nn-tanh-sector-class24-four-bridges-review-request-v1.json')
assert H(req3)=='f6464468f6f216efcfc77ca076877892850a6d29a3afa49399943e6bf68c2805'
assert H(req4)=='dfce6203dcd40359bbbfac08bdd23c6e96ced4e7e009de59cc5471e4c9698ee1'
a=R(req3);b=R(req4)
oldpeerp=bind(a['original_nine_body_peer']);assert b['original_nine_body_peer']==a['original_nine_body_peer']
oldpeer=R(oldpeerp);assert oldpeer['errors']==[] and 'passed' in oldpeer['status']
oldrequest=bind(a['original_nine_body_request']);assert b['original_full_literal_request']==a['original_nine_body_request']
assert a['entire_exercise_record']==b['entire_exercise_record'] and a['entire_material_records']==b['entire_material_records']
invp=ROOT/'book/coverage/inventory-after-correction51.json'
assert H(invp)=='d746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41'==H(ROOT/'book/coverage/inventory.json')
inv=R(invp);units={r['key']:r for r in inv['material_source_units']};exercises={r['key']:r for r in inv['exercises']}
assert exercises[a['entire_exercise_record']['key']]==a['entire_exercise_record']
page=ROOT/'SafeLearning/nn-in-the-loop.html'
for u in a['entire_material_records']:
 assert units[u['key']]==u and H(page)==u['source_sha256']
 assert hashlib.sha256(u['source_text'].encode()).hexdigest()==u['text_sha256']
s12=bind(a['new_actual_twelve_body_source']);s4=bind(b['actual_four_body_source'])
t12=s12.read_text();t4=s4.read_text();t9=oldpeer['entire_new_source_and_all_nine_bodies']
def blocks(t):
 matches=list(re.finditer(r'^theorem\s+(\w+)',t,re.M));return {m.group(1):t[m.start():(matches[i+1].start() if i+1<len(matches) else t.index('\nend SafeLearning.',m.start()))].strip() for i,m in enumerate(matches)}
o9=blocks(t9);o12=blocks(t12);o4=blocks(t4)
assert len(o9)==9 and len(o12)==12 and len(o4)==4
assert all(o12[n]==v for n,v in o9.items())
assert not re.search(r'\b(sorry|admit|axiom)\b',t12+t4)
new3=[n for n in o12 if n not in o9];assert len(new3)==3
prefix3='SafeLearning.CompleteModulesNNTanhOffset24.';prefix4='SafeLearning.CompleteModulesNNTanhSectorClass24.'
assert [prefix3+n for n in new3]==a['exact_new_declarations']
hist=[]
for stem,trials in [('modules-tanh-offset24',[1,2,3,4,5]),('modules-tanh-sector24',[1,2])]:
 for i in trials:
  p=Path(f'/tmp/{stem}-trial{i}.json');r=R(p);snapshot=Path(r['source']);log=Path(r['raw_log']);runner=Path(r['actual_runner'])
  assert r['actual_command']==['lake','env','lean',str(snapshot)] and r['actual_workdir']==str(ROOT/'verification/lean')
  expected=0 if (stem=='modules-tanh-offset24' and i in [3,5]) or (stem=='modules-tanh-sector24' and i==2) else 1
  assert r['actual_exit_code']==expected
  assert r['source_sha256_before']==r['source_sha256_after']==H(snapshot)
  assert r['raw_log_sha256']==H(log) and r['actual_runner_sha256']==H(runner)
  assert r['started_at_utc']<r['finished_at_utc'] and r['elapsed_seconds']>0
  assert 'subprocess.run' in runner.read_text() and 'returncode' in runner.read_text()
  if expected==0:assert log.read_bytes()==b''
  else:assert 'error:' in log.read_text()
  hist.append({'record':ref(p),'entire_original_actual_record_and_time':r,'unique_source_snapshot':ref(snapshot),'raw_log':ref(log),'actual_runner':ref(runner)})
assert ref(Path('/tmp/modules-tanh-offset24-trial5.json'))==a['actual_standalone_record']
assert ref(Path('/tmp/modules-tanh-sector24-trial2.json'))==b['actual_standalone_record']
selectionp=ROOT/'reports/full-coverage/checkpoint-23-selection.json';selection=R(selectionp)
assert len(selection['proof_files'])==1131
for n,r in selection['proof_files'].items():
 assert H(ROOT/n)==r['sha256'] and H(ROOT/'reports/full-coverage/checkpoint-23'/n)==r['sha256'],n
owners=['core','foundations','applied','modules','applied-promotions']
expectedowners=['1358c11b912820b5fd07d8742ebe04e9b3c371b1e4c80d462641876f00c0d39a','6008c0225111ce8a8db195475036d85af95567f620e57929ea485d39e9d42279','cf35fa4605bd21c1d6b638ab2fecfdd871beea8e7a3b850456b8053832ae9131','448b83324829b136ef9745977e10f397086b6872f6d3141854d96504dfd53367','64d40e98a0cb98cbb0e4355c38709a6a89b7d2822e982e34fc340dbc402fcdce']
ownerrefs={f'book/coverage/{n}.json':h for n,h in zip(owners,expectedowners)}
for n,h in ownerrefs.items():assert H(ROOT/n)==h
manifest=R(ROOT/'reports/full-coverage/checkpoint-23-manifest.json')
assets={n:h for n,h in manifest['working_inputs_sha256'].items() if n.startswith('SafeLearning/')}
assert len(assets)==31
for n,h in assets.items():assert H(ROOT/n)==h==H(ROOT/'reports/full-coverage/checkpoint-23'/n)
lip=ROOT/'verification/lean/SafeLearning/CompleteModulesLipSDP.lean';assert H(lip)==selection['proof_files'][lip.relative_to(ROOT).as_posix()]['sha256']
psd=ROOT/'verification/lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/PosDef.lean'
psdexcerpt=''.join(psd.read_text().splitlines(keepends=True)[275:322]);assert 'dotProduct_mulVec_nonneg' in psdexcerpt
def group(cid,names,hyp,reason):return {'component_id':cid,'lean_declarations':names,'hypotheses':hyp,'per_component_reason':reason,'missing_clauses':[],'remaining_gaps':[]}
groups=[
 group('literal_diagonal_products_true_roundings_and_non_equalities',[prefix3+new3[0]],['Actual tanh channels centered0/2 and exact source inputs−1/−1.5; real exp enclosures.'],'Both actual products are nonnegative, within half a last printed unit of0.762/0.753, and strictly unequal to those printed rationals. This approves true numerical qualifications, while the literal exact equalities remain false.'),
 group('pointwise_full_block_gain_box_actual_offset_graph',[prefix3+new3[1]],['Arbitrary finite actual tanh channels/independent centers, fixed input v and matrix Q; at that v Q is nonnegative for every independent diagonal gain d_i∈[0,1].'],'The scalar chord property and zero-centered graph derive each gain internally. This theorem is pointwise in v; the new distinct robust matrix theorems below derive its printed all-input premise.'),
 group('actual_two_layer_bias_free_zero_network',[prefix3+new3[2]],['Actual source two-layer matrices with arbitrary natural dimensions, zero biases and zero input; actual tanh.'],'All two-layer preactivations, activations and controller output are exactly0 under the source forward equations. No stability or arbitrary-initial-state conclusion follows.'),
 group('actual_stacked_identity_diagonal_action',[prefix4+list(o4)[0]],['Any finite index type n with decidable equality, real input v and diagonal gain d.'],'The actual Matrix.fromRows identity/diagonal gain equals the printed stacked action [v;Dv] coordinate by coordinate.'),
 group('robust_all_diagonal_matrix_psd_implies_all_input_gain_qc',[prefix4+list(o4)[1]],['For every independent diagonal d_i∈[0,1], the actual pullback [I;D]ᵀQ[I;D] is PosSemidef; arbitrary v.'],'The true PSD quadratic nonnegativity and explicit matrix action give the pointwise QC for every v and every gain in the box. Q is not assumed diagonal or repeated-structure-dependent; the robust condition is imposed on each actual pullback.'),
 group('robust_psd_independent_actual_scalar_channels',[prefix4+list(o4)[2]],['The same robust all-D PSD condition; each independent actual scalar function has every chord slope in[0,1] and f_i(0)=0.'],'Taking each actual chord from v_i to0 constructs its sector gain; robust all-input nonnegativity therefore holds on the genuine independent nonlinear graph. Applying the previously approved arbitrary-center tanh slope/zero theorem specializes this exact generic statement to all shifted tanh channels without repeated-function assumptions.'),
 group('arbitrary_depth_actual_bias_free_tanh_zero_preactivations',[prefix4+list(o4)[3]],['Arbitrary natural width sequence and weights at every depth, zero input layer0 and actual layer(k+1)=tanh(W_k layer(k)) equations.'],'Induction from layer0=0 and tanh0=0 proves every layer output and every actual matrix preactivation0, even with changing widths/any finite chosen depth. This directly matches the every-layer bias-free-at-origin clause; it assumes the actual feedforward equations and does not assert uniqueness of arbitrary other closed-loop equilibria.'),
]
gaps=['Six printed decimal equalities remain false as exact equalities; the original four coupled and new two diagonal products have correct rigorous approximation/non-equality proofs but source precision must be qualified before whole answer approval.',
 'Admissible diagonal temporal Zames–Falb finite-horizon/channel-invariance proof remains pending; the seven new bodies prove static pointwise sector facts only.',
 'The generic doubly hyperdominant repeated-function theorem and exact common-local-interval/common-bound correspondence require their own named proofs; the existing two-input monotonicity component does not silently close them.',
 'Offset-free/incremental method-selection sentences are explanatory scope and imply no new general certificate or stability theorem.',
 'The counterexample invalidates the QC as a generally valid premise, without proving every particular stability conclusion from an invalid premise false.']
report={'status':'passed_independent_seven_precise_static_tanh_bridge_components_whole_exercise_pending_future24_tmp_only','reviewer':'/root/config21_next','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'checker':ref(Path(__file__)),
 'original_nine_body_peer':ref(oldpeerp),'entire_original_nine_body_semantics_and_time_unchanged':oldpeer,
 'requests':[{'reference':ref(req3),'entire_original_request_body':a},{'reference':ref(req4),'entire_original_request_body':b}],
 'new_sources':[{'reference':ref(s12),'entire_source_and_all_twelve_bodies':t12,'original_nine_bodies_exact':True,'three_new_public_names':[prefix3+n for n in new3]},{'reference':ref(s4),'entire_source_and_all_four_bodies':t4,'four_new_public_names':[prefix4+n for n in o4]}],
 'approved_components':groups,'precise_new_component_count':7,'whole_new_units_approved':0,
 'material_units':[{'source_unit_key':u['key'],'entire_inventory_record':u,'whole_unit_approved':False,'material_status':'pending','reviewed_components':groups if u['key'].endswith('1262') else [],'missing_clauses':gaps} for u in a['entire_material_records'] if u['key'].endswith(('1254','1262'))],
 'original_whole_answer_a_approval_retained_without_new_decision':oldpeer['material_units'][1],
 'exercise':{'entire_inventory_record':a['entire_exercise_record'],'whole_exercise_approved':False,'status':'partial','reviewed_components':groups,'remaining_gaps':gaps},
 'full_literal_contexts_read':[{'source':ref(page),'lines_start':a0,'lines_end':b0,'exact_lines':''.join(page.read_text().splitlines(keepends=True)[a0-1:b0])}for a0,b0 in [(1029,1047),(104,111),(249,265),(275,309)]],
 'selected_actual_LipSDP_definitions_and_bodies_read':{'source':ref(lip),'entire_source':lip.read_text()},
 'primary_PSD_API_read':{'source':ref(psd),'lines_start':276,'lines_end':322,'exact_lines':psdexcerpt},
 'all_original_passed_and_failed_trial_commands_records_snapshots_runners_logs_and_times':hist,
 'current_inventory51':ref(invp),'current23_selection':ref(selectionp),'all1131_selected_sources_and_frozen_snapshots_exact':True,'all31_current51_assets_and_frozen_snapshots_exact':True,'five_live23_owner_files_exact':ownerrefs,
 'scope':['TMP-only fresh semantic supplement. All original nine-body source/peer/time and original three-body/four-body requests retained exact.','Only actual unique standalone commands inferred from original records; no canonical or named execution, whole Exercise14.6, temporal IQC or current23 amendment.'],
 'errors':[],'coverage_complete':False}
with OUT.open('x')as f:f.write(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'report':ref(OUT),'new_components':7,'whole_new_units':0}))
