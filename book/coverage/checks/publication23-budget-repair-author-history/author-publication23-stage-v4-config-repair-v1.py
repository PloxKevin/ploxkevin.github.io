from pathlib import Path
import ast,hashlib
R=Path('/home/oxrexkevin/SafetyBased'); old=R/'book/coverage/checks/root_prepare_and_stage_publication23_v3.py';new=R/'book/coverage/checks/root_prepare_and_stage_publication23_v4.py'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(old)=='9a584d7155f6696a9fd225277005341dc8f908f4a74fdb911498eb7de0a078bb' and not new.exists()
s=old.read_text().replace('the config-v2 output and its independent review, which exclude','the config-v3 output and its independent review, which exclude').replace('older lean-checkpoint-21 website content while retaining those exact files in Git.', 'older lean-checkpoint-21 and eight literal old report inventory archives from\nwebsite content while retaining those exact files in Git. The genuine config-v2\nbudget failure and unexecuted staging-v3/code peer remain unchanged.')
s=s.replace("CONFIG_PEER = 'book/coverage/checks/pages23-config-independent-modules-review-v2.json'", "CONFIG_PEER = 'book/coverage/checks/pages23-config-independent-modules-review-v3.json'")
s=s.replace("STAGE_PEER = 'book/coverage/checks/publication23-helper-independent-foundations-review-v2.json'", "STAGE_PEER = 'book/coverage/checks/publication23-helper-independent-foundations-review-v3.json'")
insert='''ORIGINAL_STAGE_V3 = 'book/coverage/checks/root_prepare_and_stage_publication23_v3.py'
ORIGINAL_STAGE_V3_SHA = '9a584d7155f6696a9fd225277005341dc8f908f4a74fdb911498eb7de0a078bb'
ORIGINAL_STAGE_V3_PEER = 'book/coverage/checks/publication23-helper-independent-foundations-review-v2.json'
ORIGINAL_STAGE_V3_PEER_SHA = '7bc0529392700da2a23e1d03b6b55d3b8a7a4fecf8c832c70e8a955995fc6d5d'
CONFIG_V3_HELPER = 'book/coverage/checks/root_prepare_pages23_config_v3.py'
CONFIG_V3_HELPER_SHA = 'efb1d71313f940a531c98af69900482ba71713dd4d7cca35a01a1dcca0f0c1c4'
CONFIG_V3_CODE_PEER = 'book/coverage/checks/pages23-config-v3-helper-independent-foundations-review-v1.json'
ORIGINAL_CONFIG_V2 = 'book/coverage/checks/root_prepare_pages23_config_v2.py'
ORIGINAL_CONFIG_V2_SHA = '7256ceed8c875961e8ecc097caf070c9727be2b9099a1c07e112d0e90af97331'
FAILED_CONFIG_V2 = 'reports/full-coverage/pages23-config-execution-v2.json'
FAILED_CONFIG_V2_SHA = '''+repr(sha(R/'reports/full-coverage/pages23-config-execution-v2.json'))+'''
FAILED_CONFIG_V2_LOG_SHA = '746c7b7122bd91aaa8d7427ac6f82ab321857a84d817d42aeba22cd2e684d069'
'''
s=s.replace("ALIAS_PLAN = ",insert+"ALIAS_PLAN = ",1)
insert='''assert sha(source_file(ORIGINAL_STAGE_V3)) == ORIGINAL_STAGE_V3_SHA
assert sha(source_file(ORIGINAL_STAGE_V3_PEER)) == ORIGINAL_STAGE_V3_PEER_SHA
assert sha(source_file(CONFIG_V3_HELPER)) == CONFIG_V3_HELPER_SHA
assert sha(source_file(ORIGINAL_CONFIG_V2)) == ORIGINAL_CONFIG_V2_SHA
assert sha(source_file(FAILED_CONFIG_V2)) == FAILED_CONFIG_V2_SHA
failed_config_v2 = read(source_file(FAILED_CONFIG_V2))
assert failed_config_v2['status'] == 'failed' and failed_config_v2['actual_exit_code'] == 1
assert failed_config_v2['actual_command'] == ['python3', ORIGINAL_CONFIG_V2]
assert failed_config_v2['helper_sha256_before'] == failed_config_v2['helper_sha256_after'] == {ORIGINAL_CONFIG_V2: ORIGINAL_CONFIG_V2_SHA}
assert sha(source_file(failed_config_v2['log'])) == failed_config_v2['log_sha256'] == FAILED_CONFIG_V2_LOG_SHA
assert not any((REPORTS / name).exists() for name in (
    'pages23-config-preparation-v2.json', 'pages23-config-previous-original-v2.yml', 'pages23-config-previous-original-v2.json'))
config_code_peer = read(source_file(CONFIG_V3_CODE_PEER))
assert 'passed' in config_code_peer['status'] and config_code_peer['errors'] == []
assert config_code_peer['helper_sha256'] == CONFIG_V3_HELPER_SHA
'''
s=s.replace("for name, digest in REPAIR_HELPERS_SHA.items():",insert+"for name, digest in REPAIR_HELPERS_SHA.items():",1)
s=s.replace("actual_zero('reports/full-coverage/pages23-config-execution-v2.json')", "config_execution_v3 = actual_zero('reports/full-coverage/pages23-config-execution-v3.json')\nassert config_execution_v3['actual_command'] == ['python3', CONFIG_V3_HELPER]")
s=s.replace("'book/coverage/checks/root_prepare_and_stage_publication23_v3.py', STAGE_PEER, CONFIG_PEER,", "'book/coverage/checks/root_prepare_and_stage_publication23_v4.py', STAGE_PEER, CONFIG_PEER,")
s=s.replace("'book/coverage/checks/root_prepare_pages23_config_v2.py', PRODUCTION_PEER,", "CONFIG_V3_HELPER, CONFIG_V3_CODE_PEER, PRODUCTION_PEER,\n    ORIGINAL_STAGE_V3, ORIGINAL_STAGE_V3_PEER, ORIGINAL_CONFIG_V2, FAILED_CONFIG_V2, failed_config_v2['log'],")
s=s.replace("'pages23-config-preparation-v2.json', 'pages23-config-previous-original-v2.yml',\n    'pages23-config-previous-original-v2.json', 'pages23-config-execution-v2.json',\n    'pages23-config-execution-v2.log',", "'pages23-config-preparation-v3.json', 'pages23-config-previous-original-v3.yml',\n    'pages23-config-previous-original-v3.json', 'pages23-config-execution-v3.json',\n    'pages23-config-execution-v3.log',")
s=s.replace("extra_hashes =", "extras.update(str(path.relative_to(ROOT)) for path in (ROOT / 'book/coverage/checks').glob('pages23-config-v3-helper-independent-foundations-*') if path.is_file())\nextra_hashes =",1)
s=s.replace("    preserved_failed_selector_v1_execution=", "    original_unexecuted23_stage_v3=ORIGINAL_STAGE_V3, original_unexecuted23_stage_v3_sha256=ORIGINAL_STAGE_V3_SHA,\n    original_stage_v3_code_peer=ORIGINAL_STAGE_V3_PEER, original_stage_v3_code_peer_sha256=ORIGINAL_STAGE_V3_PEER_SHA,\n    actual_failed_config_v2=FAILED_CONFIG_V2, actual_failed_config_v2_sha256=FAILED_CONFIG_V2_SHA, actual_failed_config_v2_exit_code=1,\n    current_config_v3_helper=CONFIG_V3_HELPER, current_config_v3_helper_sha256=CONFIG_V3_HELPER_SHA,\n    preserved_failed_selector_v1_execution=",1)
ast.parse(s);new.write_text(s);print(new.relative_to(R),sha(new))
