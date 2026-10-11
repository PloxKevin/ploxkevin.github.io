import sys,json,hashlib
from pathlib import Path
from datetime import datetime,timezone
ROOT=Path('/home/oxrexkevin/SafetyBased')
sys.path.insert(0,str(ROOT/'book/coverage'))
from lean_names import declarations
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
ref=lambda p:{'file':str(p),'sha256':sha(p)}
source=Path('/tmp/root-monitoring-face-classification23-trial2.lean')
actual_path=source.with_suffix('.json');actual=json.loads(actual_path.read_text())
assert sha(source)==actual['source_sha256']=='c57ab035c84951e5ee114d2810ae5d75627508234a753160f7a0286e0a5e20e2'
assert actual['exit_code']==0 and actual['command']==['lake','env','lean',str(source)]
assert sha(source.with_suffix('.log'))==actual['log_sha256']=='e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855'
runner=Path('/tmp/root-monitoring-face-classification23-trial2-run.py')
assert "cwd='/home/oxrexkevin/SafetyBased/verification/lean'" in runner.read_text()
failed=Path('/tmp/root-monitoring-face-classification23-trial1.lean')
failed_record=json.loads(failed.with_suffix('.json').read_text())
assert failed_record['exit_code']==1 and sha(failed)==failed_record['source_sha256']
assert sha(failed.with_suffix('.log'))==failed_record['log_sha256']
decl=[d for d in declarations(source.read_text()) if d['kind'] in ('theorem','lemma')]
assert len(decl)==8
proposal=Path('/tmp/applied-monitoring-modes-source49-qualification-proposal23-v2.json')
assert sha(proposal)=='125ae48247af82a507ff66309aa51291936efeef72c4f24af4add5461d10f85e'
proposed=json.loads(proposal.read_text());replacement=next(x for x in proposed['replacements'] if x['source_unit_key']=='cmdp.html::node-1138')
invpath=ROOT/'book/coverage/inventory-after-correction48.json';assert sha(invpath)=='2daa285ff1cbc2ad0db045e00e1271b6cb58ce809f5a8328120286748250c108'
inv=json.loads(invpath.read_text());unit=next(x for x in inv['material_source_units'] if x['key']=='cmdp.html::node-1138');exercise=next(x for x in inv['exercises'] if x['key']=='cmdp.html::exercise-21')
assert sha(ROOT/unit['source'])==unit['source_sha256']
assert replacement['before'] in (ROOT/unit['source']).read_text()
selection_path=ROOT/'reports/full-coverage/checkpoint-22-selection.json';selection=json.loads(selection_path.read_text())
assert len(selection['proof_files'])==1113
for name,row in selection['proof_files'].items():assert sha(ROOT/name)==row['sha256']
deps=[]
for name in ('CompleteMonitoringGeometry21','CompleteMonitoringFaces22'):
 p='verification/lean/SafeLearning/'+name+'.lean';row=selection['proof_files'][p]
 for f,digest in row['evidence_sha256'].items():assert sha(ROOT/f)==digest
 deps.append({'source':p,'sha256':sha(ROOT/p),'retained_selected22_row':row,'entire_source_read':True})
ns='SafeLearning.CompleteMonitoringFaceClassification23.'
names=lambda xs:[ns+x for x in xs]
groups=[
 {'component_id':'first_price_strict_unique_fraction_vertex','lean_declarations':names(['actual_first_strictly_largest_above_one_unique','actual_first_strictly_largest_below_one_unique']),'hypotheses':['lambda2<lambda1; lambda1>1 or lambda1<1, respectively. Fractions use the actual source polytope and source Lagrangian.'],'per_component_reason':'Every maximizer, not merely an exhibited fixture, is proved equal to v1 above1 and v3 below1. Comparing the actual vertex value and source simplex equation forces the unique fraction coordinates.','review_status':'approved_complete_component','missing_clauses':[]},
 {'component_id':'second_price_strict_unique_fraction_vertex','lean_declarations':names(['actual_second_strictly_largest_above_one_unique','actual_second_strictly_largest_below_one_unique']),'hypotheses':['lambda1<lambda2; lambda2>1 or lambda2<1, respectively.'],'per_component_reason':'The symmetric source cases derive the unique vertices v2 and v4 from actual maximizer inequalities and nonnegative simplex coordinates.','review_status':'approved_complete_component','missing_clauses':[]},
 {'component_id':'threshold_one_entire_maximizing_edges','lean_declarations':names(['actual_first_threshold_one_has_full_tied_edge','actual_second_threshold_one_has_full_tied_edge']),'hypotheses':['One strictly larger multiplier equals1; the other is strictly below1. The candidate fraction lies in the source achievable polytope.'],'per_component_reason':'At lambda1=1>lambda2, maximizing is equivalent to V2=0; at lambda2=1>lambda1 it is equivalent to V1=0. Both necessary and sufficient directions are derived, retaining the full face at equality.','review_status':'approved_complete_component','missing_clauses':[]},
 {'component_id':'threshold_edges_actual_segment_parametrization','lean_declarations':names(['actual_zero_second_region_is_exact_first_edge','actual_zero_first_region_is_exact_second_edge']),'hypotheses':['Arbitrary real fraction structure; t ranges over the closed unit interval.'],'per_component_reason':'The entire first edge is exactly(t/2,1-t/2,0) for0≤t≤1, and the second exactly(t/2,0,1-t/2). Source endpoints are the actual staying and alternating vertices. Both membership and converse witnesses are proved.','review_status':'approved_complete_component','missing_clauses':[]}
]
assert set(d['name'] for d in decl)==set(n for g in groups for n in g['lean_declarations'])
out=Path('/tmp/monitoring-face-classification23-independent-applied-components-review-v1.json');assert not out.exists()
report={'status':'passed_independent_full_eight_body_monitoring_face_classification_components_review_future23','reviewer':'/root/applied_next','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'inventory':ref(invpath),'exercise_key':exercise['key'],'exercise_text_sha256':exercise['text_sha256'],'material_units':[{'source_unit_key':unit['key'],'entire_inventory_record':unit,'whole_unit_approved':False,'review_status':'approved_precise_components_only','components':groups,'missing_clauses':['This supplement alone does not prove all actual-policy/path realization statements, stationary/history distinctions or universal immediate action statements in the current original paragraph.','No complete current(b)/(c), conditional-unbiasedness A3 or generic epoch-update theorem is approved here.']}],'proposed_source_reference':ref(proposal),'proposed_exact_paragraph':replacement['after'],'proposed_source_scope':'The new eight theorems directly match V2 strict-price unique vertices and equality-at1 full tied edge. The current48 wording lists maximizing vertices on overlapping weak inequalities; this supplement makes the entire equality face explicit. Fraction maximization imposes no universal transient-action selector. The earlier V2 proposal peer and scope remain unchanged.','full_all_eight_public_bodies_read':True,'public_declarations':decl,'proof_source':ref(source),'actual_standalone_record':ref(actual_path),'entire_original_actual_record':actual,'raw_log':ref(source.with_suffix('.log')),'raw_log_description':'Genuinely empty standalone exit0 log.','actual_runner':ref(runner),'historical_failed_trial':{'source':ref(failed),'record':ref(failed.with_suffix('.json')),'entire_original_record':failed_record,'raw_log':ref(failed.with_suffix('.log')),'runner':ref(Path('/tmp/root-monitoring-face-classification23-trial1-run.py'))},'retained_dependencies':deps,'protected_selected22_sources':{'selection':ref(selection_path),'count':1113,'all_source_sha256_exact':True},'scope':'Only new future23 TMP component correspondence and read-only checker execution. No Lean rerun, canonical source selection, current22 ledger/body/time mutation, source49 application or whole exercise promotion.','actual_checker':str(Path(__file__)),'actual_checker_sha256':sha(Path(__file__)),'errors':[],'coverage_complete':False}
with out.open('x') as f:f.write(json.dumps(report,indent=2)+'\n')
print(json.dumps({'status':'passed','file':str(out),'sha256':sha(out),'public_theorems':8,'source_sha256':sha(source)}))
