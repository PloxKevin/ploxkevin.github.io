from pathlib import Path
import ast,hashlib,json
ROOT=Path('/home/oxrexkevin/SafetyBased')
def sha(n):return hashlib.sha256((ROOT/n).read_bytes()).hexdigest()
def read(n):return json.loads((ROOT/n).read_bytes())
helper='book/coverage/checks/root_close_publication29_delivery_v2.py'
old='book/coverage/checks/root_close_publication28_delivery_v2.py'
src=(ROOT/helper).read_text();oldsrc=(ROOT/old).read_text()
assert sha(helper)=='6386534c97f57842493b80241c3ec33d6bd3eea4f97614a0afd117efab8f1577'
for text in [src,oldsrc]:ast.parse(text)
assert "publication29-staged-byte-check-v2.json" in src and "root-explicit-audited29-publication-stage-plan-v2.json" in src
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
findings=[
 {'id':'close_bypasses_strict_native_command_and_helper_chain','location':'close execution records','decision':'repair_required','description':'The final close reads the update/stage records directly and checks only primary actual_exit_code/status/log. It bypasses actual() command/cwd/helper and present-alias consistency gates.'},
 {'id':'inherited_content_evidence_not_rechecked_at_close','location':'close delivery report','decision':'repair_required','description':'The final close inherits content evidence_sha256 without validating each original current byte digest, and does not assert the report helper/status/coverage before attributing the content commit.'}]
observations={'status':'completed_full_independent_delivery29_code_and_authentic28_schema_read_requires_repairs','helper':{'file':helper,'sha256':sha(helper)},'original_producer':{'file':old,'sha256':sha(old)},'all_functions_and_output_bodies_read':True,'authentic28_native_schema_read':True,'current1197_source_union_checked_by_outer_guard':True,'current65_and_installed29_global_counts':[526,11,19,4663,8111],'all_current_source_owner_guards_claimed_only_as_readonly_integrity':True,'future29_delivery_or_audit_success_claimed':False,'producer_import_or_execution':False,'compiler_or_Git_PUB_mutation':False,'findings':findings,'expected_delivery28_body_time_retained':True,'original_v1_repair_findings_retained':True,'v2_original_three_findings_repaired':True,'coverage_complete':False}
Path('/tmp/root29-delivery-helper-independent-foundations-findings-v2.json').write_text(json.dumps(observations,indent=2)+'\n')
print(json.dumps({'status':observations['status'],'repair_count':2,'optional_count':0}))
