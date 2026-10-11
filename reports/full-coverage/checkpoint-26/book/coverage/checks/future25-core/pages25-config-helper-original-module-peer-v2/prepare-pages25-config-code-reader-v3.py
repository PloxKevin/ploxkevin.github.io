from pathlib import Path
p=Path('/tmp/pages25-config-helper-independent-modules-checker-v2.py');s=p.read_text();s=s.replace("root_prepare_pages25_config_v1.py'","root_prepare_pages25_config_v2.py'").replace("OUT=Path('/tmp/pages25-config-helper-independent-modules-review-v1.json')","OUT=Path('/tmp/pages25-config-helper-independent-modules-review-v2.json')").replace("EXPECTED='04207875a69824919c74a78d0fc95b415369cbceaab24989815b7b96dafaccad'","EXPECTED='fb5086deddeb83fbca5e1523e6764ee9391f8dc2e8d1c6e0196b4678084402ce'")
s=s.replace('assert len(retired)==6','assert len(retired)==8').replace('assert len(added)==9','assert len(added)==11').replace('assert len(new)==97','assert len(new)==99').replace("'new_literal_exclusion_count':97","'new_literal_exclusion_count':99").replace("'exact_nine_additions'","'exact_eleven_additions'").replace("'six_old_manifest_selection_archives_root_pub_tracked_head_exact'","'eight_old_manifest_selection_archives_root_pub_tracked_head_exact'")
anchor='fixtures=[]\n';extra='''oldhelper=(R/'book/coverage/checks/root_prepare_pages25_config_v1.py').read_text()
reverse=text
for line in ["    'reports/full-coverage/checkpoint-20-manifest.json': 'fa9561d3266e9661b785ddcffc582d0b223bd56c2f56680b4e0353c4e934b6a6',\\n","    'reports/full-coverage/checkpoint-20-selection.json': '66cb09b08a0729794bc0f77e8e9778659e4437479ae4e10f686b4012901256b6',\\n"]:
 assert line in reverse;reverse=reverse.replace(line,'',1)
start=reverse.index('# The original helper and both genuine prewrite failures remain unchanged.')
end=reverse.index('assert sha(CFG) == BEFORE',start)
reverse=reverse[:start]+reverse[end:]
reverse=reverse.replace('assert len(exclusions) == 99','assert len(exclusions) == 97').replace("'excluded_count': 99","'excluded_count': 97")
start=reverse.index("    'original_prewrite_failed_execution_evidence_sha256': original_failed_evidence,")
end=reverse.index("    'coverage_complete': False",start)
reverse=reverse[:start]+reverse[end:]
reverse=reverse.replace('Only the exact older checkpoint20 pair is additionally retired in this version. ','')
assert reverse==oldhelper
assert digest(R/'book/coverage/checks/root_prepare_pages25_config_v1.py')==ns['ORIGINAL_HELPER_SHA']
assert digest(R/ns['ORIGINAL_CODE_PEER'])==ns['ORIGINAL_CODE_PEER_SHA']
for name,h in ns['ORIGINAL_FAILURES'].items():
 assert digest(R/name)==h
 d=json.loads((R/name).read_text());vv=[d[k] for k in ['actual_exit_code','exit_code'] if k in d]
 assert vv and all(type(x)is int and x==1 for x in vv)
 assert d['actual_command']==['python3',ns['ORIGINAL_HELPER']]
 assert d['helper_sha256_before']==d['helper_sha256_after']=={ns['ORIGINAL_HELPER']:ns['ORIGINAL_HELPER_SHA']}
 assert digest(R/d['log'])==d['log_sha256']
assert '862125851' in (R/'reports/full-coverage/pages25-config-execution-v2.log').read_text()
'''
s=s.replace(anchor,extra+anchor)
s=s.replace("'status':'passed_independent_pages25_config_helper_code_and_current_archive_review'","'original_helper':ref('book/coverage/checks/root_prepare_pages25_config_v1.py'),'original_code_peer':ref(ns['ORIGINAL_CODE_PEER']),'original_genuine_prewrite_failures':ns['ORIGINAL_FAILURES'],'exact_delta':'Only older checkpoint20 pair literal exclusions plus exact original failure/code provenance; reverse recovers original helper bytes.','status':'passed_independent_pages25_config_helper_v2_code_native_archives_and_delta_review'")
s=s.replace('OUT.write_text',"assert current<850000000,current\nassert sum((R/n).stat().st_size for n in retired if 'checkpoint-20-' in n)==22938018\nOUT.write_text")
t=Path('/tmp/pages25-config-helper-independent-modules-checker-v3.py');assert not t.exists();t.write_text(s)
