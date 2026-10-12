from pathlib import Path
import ast,hashlib,json
ROOT=Path('/home/oxrexkevin/SafetyBased')
def sha(n):return hashlib.sha256((ROOT/n).read_bytes()).hexdigest()
def read(n):return json.loads((ROOT/n).read_bytes())
helper='book/coverage/checks/root_close_publication29_delivery_v1.py'
old='book/coverage/checks/root_close_publication28_delivery_v2.py'
src=(ROOT/helper).read_text();oldsrc=(ROOT/old).read_text()
assert sha(helper)=='b2bc189e7a291dd8a95b705d7de7a3f6e0b04569b0e3165cff6a2e811d8f86c4'
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
 {'id':'native_present_alias_conflicts_ignored','location':'actual','decision':'repair_required','description':'Primary actual_* and log fields are checked, but present exit_code/command/cwd/raw_log aliases are not checked for consistency.'},
 {'id':'source_inventory_and_correction_publication_hash_guards_missing','location':'immutable','decision':'repair_required','description':'Inventory has only a Root comparison, while correction guard only counts65 entries. Require exact Root working and PUB frozen hashes for both files.'},
 {'id':'metadata_prewrite_gates_after_mutation','location':'stage','decision':'repair_required','description':'Unexpected Git dirty paths and current website budget are checked after metadata copying, stage-report creation and index changes. Prepare expected payloads and reject these before copying.'},
 {'id':'literal_git_pathspec_optional','location':'stage git add','decision':'small_hardening','description':'Current expected paths are ordinary; global --literal-pathspecs prevents a leading-colon path from being interpreted as magic.'}]
observations={'status':'completed_full_independent_delivery29_code_and_authentic28_schema_read_requires_repairs','helper':{'file':helper,'sha256':sha(helper)},'original_producer':{'file':old,'sha256':sha(old)},'all_functions_and_output_bodies_read':True,'authentic28_native_schema_read':True,'current1197_source_union_checked_by_outer_guard':True,'current65_and_installed29_global_counts':[526,11,19,4663,8111],'all_current_source_owner_guards_claimed_only_as_readonly_integrity':True,'future29_delivery_or_audit_success_claimed':False,'producer_import_or_execution':False,'compiler_or_Git_PUB_mutation':False,'findings':findings,'expected_delivery28_body_time_retained':True,'coverage_complete':False}
Path('/tmp/root29-delivery-helper-independent-foundations-findings-v1.json').write_text(json.dumps(observations,indent=2)+'\n')
print(json.dumps({'status':observations['status'],'repair_count':3,'optional_count':1}))
