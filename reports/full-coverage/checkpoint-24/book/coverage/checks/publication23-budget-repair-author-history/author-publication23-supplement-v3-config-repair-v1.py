from pathlib import Path
import hashlib,ast
R=Path('/home/oxrexkevin/SafetyBased');old=R/'book/coverage/checks/root_stage_checkpoint23_additional_execution_evidence_v2.py';new=R/'book/coverage/checks/root_stage_checkpoint23_additional_execution_evidence_v3.py'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(old)=='9c9ddd68df0e351fcaae628f6740bf6db0eb45148372b4d9b751dc53c24f16f4' and not new.exists()
s=old.read_text().replace("SELF_NAME = 'book/coverage/checks/root_stage_checkpoint23_additional_execution_evidence_v2.py'", "SELF_NAME = 'book/coverage/checks/root_stage_checkpoint23_additional_execution_evidence_v3.py'")
s=s.replace("PEER_NAME = 'book/coverage/checks/publication23-additional-evidence-helper-independent-foundations-review-v1.json'", "PEER_NAME = 'book/coverage/checks/publication23-additional-evidence-helper-independent-foundations-review-v2.json'")
s=s.replace("PRIMARY_HELPER = 'book/coverage/checks/root_prepare_and_stage_publication23_v3.py'", "PRIMARY_HELPER = 'book/coverage/checks/root_prepare_and_stage_publication23_v4.py'")
s=s.replace("PRIMARY_HELPER_SHA = '9a584d7155f6696a9fd225277005341dc8f908f4a74fdb911498eb7de0a078bb'", "PRIMARY_HELPER_SHA = 'a7c07a5560b480e183b8eefba95c087eb406d474e47f80ec007137e286bdcf87'")
s=s.replace(" 'pages23-config-execution-v2', 'export-checkpoint23-output-integrity-execution-v1',", " 'pages23-config-execution-v3', 'export-checkpoint23-output-integrity-execution-v1',")
old_extra=[old,R/'book/coverage/checks/publication23-additional-evidence-helper-independent-foundations-review-v1.json',R/'book/coverage/checks/publication23-additional-evidence-helper-independent-foundations-check-v1.py',R/'book/coverage/checks/publication23-additional-evidence-helper-independent-foundations-actual-v1.json',R/'book/coverage/checks/publication23-additional-evidence-helper-independent-foundations-actual-v1.log',R/'book/coverage/checks/run-publication23-additional-evidence-helper-independent-foundations-review-v1.py',R/'book/coverage/checks/publication23-additional-evidence-original-TMP-byte-aliases-v1.json',R/'book/coverage/checks/root_prepare_pages23_config_v2.py',R/'reports/full-coverage/pages23-config-execution-v2.json',R/'reports/full-coverage/pages23-config-execution-v2.log']
extra={p.relative_to(R).as_posix():sha(p) for p in old_extra}
s=s.replace('ORIGINAL_EXECUTION_CODES = ', 'PINNED_CLOSED_EVIDENCE.update('+repr(extra)+')\nORIGINAL_EXECUTION_CODES = ',1)
s=s.replace('SUCCESSFUL_LATER_EXECUTIONS = (', "ORIGINAL_EXECUTION_CODES['pages23-config-execution-v2'] = 1\nSUCCESSFUL_LATER_EXECUTIONS = (",1)
s=s.replace('selector/binding executions remain failures;', 'selector/binding/config-v2 executions remain failures;')
s=s.replace('All23 mathematical owner/source inputs are read-only.', 'All23 mathematical owner/source inputs are read-only. Version3 requires the\nnew primary stage-v4/config-v3 and preserves the reviewed unexecuted\nsupplemental-v2 and its complete actual independent-code-review history.')
ast.parse(s);new.write_text(s);print(new.relative_to(R),sha(new))
