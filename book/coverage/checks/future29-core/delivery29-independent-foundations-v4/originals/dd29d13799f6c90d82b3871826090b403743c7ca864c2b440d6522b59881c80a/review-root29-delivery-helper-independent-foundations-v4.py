from pathlib import Path
import ast,hashlib,json
ROOT=Path('/home/oxrexkevin/SafetyBased')
def sha(n):return hashlib.sha256((ROOT/n).read_bytes()).hexdigest()
def read(n):return json.loads((ROOT/n).read_bytes())
helper='book/coverage/checks/root_close_publication29_delivery_v4.py'
old='book/coverage/checks/root_close_publication28_delivery_v2.py'
src=(ROOT/helper).read_text();oldsrc=(ROOT/old).read_text()
assert sha(helper)=='fa78133c16e5cd24da450a31d45896993cebc47f8eeed8f1ae550796256974de'
for text in [src,oldsrc]:ast.parse(text)
assert "publication29-staged-byte-check-v3.json" in src and "root-explicit-audited29-publication-stage-plan-v3.json" in src
assert "'status':'passed_actual_checkpoint29_content_and_metadata_delivery'" in src
assert "all(j['status']=='completed' and j['conclusion']=='success'" in src
assert "len(w['jobs'])==3" in src and "remote['output'].split()==[commit,'refs/heads/main']" in src
assert "if stem=='content':\n  failed=" not in src
assert "len(read('book/coverage/material-corrections.json')['corrections'])==65" in src
assert "cmd=(['git','-C',str(PUB),'-c','http.version=HTTP/1.1','-c','http.postBuffer=268435456','push','origin','main']" in src
closed=read('book/coverage/checks/future28-core/completed28-content-and-metadata-delivery-closure-v1.json')
assert closed['status']=='passed_actual_checkpoint28_content_and_metadata_delivery'
for n,h in closed['exact_native_evidence_sha256'].items():assert sha(n)==h
live=read('reports/full-coverage/live-checkpoint-28-attempt2.json')
assert live['status']=='passed_all31_asset_sha256' and len(live['assets'])==31
pages=read('reports/full-coverage/pages-checkpoint-28-attempt2.json')
assert pages['status']=='passed' and pages['command']==['gh','api','repos/PloxKevin/ploxkevin.github.io/pages/builds/latest']
assert sha(pages['log'])==pages['log_sha256']
build=read(pages['log']);assert build['status']=='built' and build['commit']==pages['commit']
workflow=read('reports/full-coverage/publication28-metadata-pages-view-execution-v1.json')
w=read(workflow['log']);assert w['headSha']==live['commit'] and len(w['jobs'])==3 and all(j['status']=='completed' and j['conclusion']=='success' for j in w['jobs'])
coverage=read('reports/full-coverage/root-source65-final-owner-integration29-v1.json')
assert coverage['integrity_status']=='passed' and coverage['errors']==[] and coverage['mathematical_coverage_complete'] is False
assert coverage['counts']['material_review_statuses']=={'reviewed':4663,'pending':8111}
assert [coverage['counts']['statuses'][k] for k in ['exercise:complete_math','exercise:partial','exercise:pending']]==[526,11,19]
prior_helper='book/coverage/checks/root_close_publication29_delivery_v3.py'
assert sha(prior_helper)=='ea68d00cab36712d3b171a193fc163007e980e824fb8cb37b2794636df4527ed'
expected=(ROOT/prior_helper).read_text().replace('root_close_publication29_delivery_v3.py','root_close_publication29_delivery_v4.py').replace('root-explicit-audited29-publication-stage-plan-v2.json','root-explicit-audited29-publication-stage-plan-v3.json').replace('pages29-config-preparation-v1.json','pages29-config-preparation-v2.json').replace('root_stage_publication29_v2.py','root_stage_publication29_v3.py').replace('publication29-staged-byte-check-v2.json','publication29-staged-byte-check-v3.json')
line=" review=plan['independent_delivery_helper_review'];assert set(review)=={'file','sha256'} and sha(review['file'])==review['sha256']\n peer=read(review['file']);assert peer['status'].startswith('passed_') and peer['errors']==[] and peer['helper']==ref(SELF)\n"
expected=expected.replace(" m=read(plan['manifest']['file']);",line+" m=read(plan['manifest']['file']);",1)
expected=expected.replace("'helper':ref(SELF),'content_commit':d['content_commit']","'helper':ref(SELF),'independent_delivery_helper_review':read(PLAN)['independent_delivery_helper_review'],'content_commit':d['content_commit']",1)
assert expected==src
planhelper='book/coverage/checks/root_prepare_publication29_stage_plan_v3.py'
assert sha(planhelper)=='06d4e26fa23163c7e27c36f00f73742e14a923cc0956c4e00a32084740662abc'
ps=(ROOT/planhelper).read_text();ast.parse(ps)
assert "['staging', 'pages', 'audit', 'delivery']" in ps and "assert peers['delivery']['helper'] == docs.ref(DELIVERY_HELPER)" in ps
assert "'independent_delivery_helper_review': docs.ref(args.delivery_peer)" in ps and "DELIVERY_HELPER = 'book/coverage/checks/root_close_publication29_delivery_v4.py'" in ps
prior_peer='book/coverage/checks/future29-core/delivery29-independent-foundations-v3/checkpoint29-delivery-helper3-full-independent-foundations-closed-peer-v1.json'
assert sha(prior_peer)=='2fd23674c52681f29e20bb07553fb3a873edf69695290c5099a529601e9a1987'
p=read(prior_peer);assert p['errors']==[] and p['helper']['file']==prior_helper
for n,h in p['closed_evidence_sha256'].items():assert sha(n)==h

findings=[]
assert "r=actual(n,['python3',SELF,mode])" in src
assert "for n,h in d['evidence_sha256'].items():assert sha(n)==h" in src
assert "d['status']=='passed_actual_checkpoint29_content_delivery_document_update' and d['helper']==ref(SELF) and d['coverage_complete'] is False" in src
for ver in [1,2,3]:
 prior=json.loads(Path(f'/tmp/root29-delivery-helper-independent-foundations-actual-v{ver}.json').read_bytes())
 assert prior['status']=='passed' and type(prior['actual_exit_code']) is int and prior['actual_exit_code']==0 and prior['protection_errors']==[]
 assert hashlib.sha256(Path(prior['log']).read_bytes()).hexdigest()==prior['log_sha256']
observations={'status':'passed_full_independent_delivery29_code_and_authentic28_schema_read_conditional_future_delivery','helper':{'file':helper,'sha256':sha(helper)},'original_producer':{'file':old,'sha256':sha(old)},'all_functions_and_output_bodies_read':True,'authentic28_native_schema_read':True,'current1197_source_union_checked_by_outer_guard':True,'current65_and_installed29_global_counts':[526,11,19,4663,8111],'all_current_source_owner_guards_claimed_only_as_readonly_integrity':True,'future29_delivery_or_audit_success_claimed':False,'producer_import_or_execution':False,'compiler_or_Git_PUB_mutation':False,'findings':findings,'expected_delivery28_body_time_retained':True,'original_v1_repair_findings_retained':True,'v2_original_three_findings_repaired':True,'v3_two_final_close_findings_repaired':True,'v4_delta_exact':True,'v4_fourth_precontent_plan_delivery_peer_gate':True,'v4_strict_review_ref_and_helper_binding':True,'v4_closure_retains_original_delivery_peer_ref':True,'errors':[],'fixture_count':0,'future_prerequisites':{'selection29':'not_claimed_successful_by_this_reader','frozen29_audit':'already_actual_audit_context_exists_but_no_producer_run_by_this_reader','content_pages_and_live':'not_yet_available','metadata_pages_and_live':'not_yet_available'},'coverage_complete':False}
Path('/tmp/root29-delivery-helper-independent-foundations-findings-v4.json').write_text(json.dumps(observations,indent=2)+'\n')
print(json.dumps({'status':observations['status'],'errors':[],'producer_executed':False}))
