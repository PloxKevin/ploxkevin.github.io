"""Independent config-v3 full read and isolated gates, with no producer writes."""
from pathlib import Path
from datetime import datetime,timezone
import ast,copy,hashlib,json,subprocess
R=Path('/home/oxrexkevin/SafetyBased');PUB=R/'reports/book/publication-repo'
NAME='book/coverage/checks/root_prepare_pages25_config_v3.py';EXPECTED='6a05cb9a1ab25be9b2450778f264a424613dcea4c895452aec2545bbf7cabc70'
OUT=Path('/tmp/pages25-config-helper-independent-modules-review-v3.json')
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(n):return {'file':n,'sha256':h(R/n)}
assert not OUT.exists() and h(R/NAME)==EXPECTED
text=(R/NAME).read_text();tree=ast.parse(text)
# Run the entire actual read-only prefix, stopping BEFORE the first exclusive backup write.
first_write=next(i for i,node in enumerate(tree.body) if isinstance(node,ast.With))
assert all(not(isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute) and n.func.attr in {'write_bytes','write_text','mkdir','unlink','rename','replace'}) for node in tree.body[:first_write] for n in ast.walk(node))
ns={'__file__':str(R/NAME)};before=h(PUB/'_config.yml')
exec(compile(ast.Module(body=tree.body[:first_write],type_ignores=[]),NAME,'exec'),ns)
assert h(PUB/'_config.yml')==before=='f687b33a73defabc3e95085addaa796961f088df8de06f7fc98093a9dc0af523'
assert all(not (R/ns[k]).exists() for k in ['REPORT','BACKUP','BACKUP_RECORD'])
assert ns['RETIRED_FILES']=={'reports/full-coverage/checkpoint-19-manifest.json':'b6ec94fc308b266f2a8a16be156dbbdea8fae7915146ec66fab6375fa2501575','reports/full-coverage/checkpoint-19-selection.json':'9fcf2c8d8785e1b1e98fa482d47a4a4dda2fb5f19ae9d8375e860f32767e4672'}
assert sum((R/n).stat().st_size for n in ns['RETIRED_FILES'])==9240153
prev=json.loads((R/ns['PREVIOUS_NATIVE']).read_text());assert ns['previous_native']==prev and ns['report']['entire_original_configuration_preparation_body_and_time']==prev
assert ns['report']['retained_original_native_files_sha256']==ns['retained_original_native_files']
old=set(prev['exclusions']);new=ns['exclusions'];assert len(old)==99 and new-old==set(ns['RETIRED_FILES']) and not old-new and len(new)==101
assert ns['report']['new_literal_exclusions']==sorted(new-old)
# All actual write guards and future outcomes are still independent: prefix runs no producer.
assert first_write>next(i for i,node in enumerate(tree.body) if isinstance(node,ast.Assert) and ast.unparse(node.test)=='prospective < 850000000')
assert "all(type(c['exit_code']) is int and c['exit_code'] == 0" in text
assert "removed == baseline_removed and len(removed) == (3 if owner == 'applied' else 0)" in text
assert "normalized == json.loads((PUB / name).read_text())" in text
assert "sum(c.get('evidence_mode') == 'fresh_kernel_replay' for c in audit['checks']) == 12" in text
# The complete common audit/source/owner guard and output-writing suffix remain identical to v2.
v2=(R/ns['PREVIOUS_HELPER']).read_text()
common_start="assert sha(ROOT / 'reports/full-coverage/checkpoint-24-manifest.json') == BASELINE_MANIFEST"
common_end='added = set(RETIRED_FILES)'
assert text[text.index(common_start):text.index(common_end)]==v2[v2.index(common_start):v2.index(common_end)]
suffix_start="with (ROOT / BACKUP).open('xb') as out: out.write(old)"
new_suffix=text[text.index(suffix_start):].replace("'excluded_count': 101","'excluded_count': 99")
assert new_suffix==v2[v2.index(suffix_start):]
fixtures=[]
for case,d,ok in [('actual0',{'actual_exit_code':0},True),('exit0',{'exit_code':0},True),('both0',{'actual_exit_code':0,'exit_code':0},True),('boolFalse',{'actual_exit_code':False},False),('float0',{'exit_code':0.0},False),('string0',{'exit_code':'0'},False),('conflict',{'actual_exit_code':0,'exit_code':1},False),('missing',{},False),('negative',{'exit_code':-15},False)]:
 try:ns['zero'](d);got=True
 except AssertionError:got=False
 assert got==ok;fixtures.append({'case':case,'accepted':got,'synthetic':True})
for n in ns['required']:
 assert ns['kept'](n);fixtures.append({'case':'required_included:'+n,'accepted':True,'path_eligibility_only':True})
for n in ns['RETIRED_FILES']:
 assert not ns['kept'](n);assert ns['kept'](n+'0');fixtures.extend([{'case':'exact_retired:'+n,'accepted':False,'path_eligibility_only':True},{'case':'prefix_neighbour:'+n+'0','accepted':True,'path_eligibility_only':True}])
# Native retained archives, previous producer successes/failures and no stage copies are rewritten.
retained={**ns['retained_original_native_files'],ns['PREVIOUS_HELPER']:ns['PREVIOUS_HELPER_SHA'],ns['PREVIOUS_CODE_PEER']:ns['PREVIOUS_CODE_PEER_SHA'],ns['ORIGINAL_HELPER']:ns['ORIGINAL_HELPER_SHA'],ns['ORIGINAL_CODE_PEER']:ns['ORIGINAL_CODE_PEER_SHA'],**ns['original_failed_evidence'],ns['previous_execution_name']:h(R/ns['previous_execution_name']),ns['previous_execution']['log']:ns['previous_execution']['log_sha256']}
for n,d in retained.items():assert h(R/n)==d
for n in ['reports/full-coverage/stage-checkpoint25-content-execution-v1.json','reports/full-coverage/stage-checkpoint25-content-execution-v2.json']:
 if (R/n).exists():
  d=json.loads((R/n).read_text());vals=[d[k] for k in ['actual_exit_code','exit_code'] if k in d];assert vals and all(type(v)is int and v==1 for v in vals);retained[n]=h(R/n)
report={'status':'passed_independent_pages25_config_v3_full_code_native_archive_and_budget_review','errors':[],'checked_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'/root/modules_resume','helper':ref(NAME),'helper_sha256':EXPECTED,'fixture_count':len(fixtures),'isolated_fixtures':fixtures,'previous_successful_native':ref(ns['PREVIOUS_NATIVE']),'entire_previous_successful_native_body_and_time':prev,'previous_successful_code_peer':ref(ns['PREVIOUS_CODE_PEER']),'entire_previous_successful_code_peer_body_and_time':json.loads((R/ns['PREVIOUS_CODE_PEER']).read_text()),'exact_delta':'Only the two direct checkpoint19 manifest/selection website exclusions beyond the passed99 config; new output paths and full previous native/helper/peer/success provenance. All original archives and audit/source/owner guards remain exact.','old_excluded_count':99,'excluded_count':101,'exact_two_additions':ns['RETIRED_FILES'],'retired_two_direct_files_bytes':9240153,'current_native_prewrite_prospective_bytes':ns['prospective'],'prewrite_budget_bytes':850000000,'protected_required_publication_files_sha256':ns['required'],'retained_original_evidence_sha256':retained,'native_prefix_execution_scope':'Executed the entire helper read-only prefix in isolated namespace, stopping before its first backup write. It validates actual archive/gate/website budget data and creates no output/config/backup; this is not producer execution.','source31_unchanged':True,'original_three_unreferenced_applied_metadata_removals_exact':True,'coverage_complete':False,'scope':'Independent code/schema/read-only native inputs and focused isolated fixtures. Actual config successor execution and output review remain required; no Pages or live outcome claimed.'}
OUT.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'peer':str(OUT),'sha256':h(OUT),'fixture_count':len(fixtures),'prospective':ns['prospective']}))
