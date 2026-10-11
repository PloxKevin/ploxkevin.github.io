from pathlib import Path
import hashlib,ast,json
R=Path('/home/oxrexkevin/SafetyBased'); P=R/'reports/book/publication-repo'
old=R/'book/coverage/checks/root_prepare_pages23_config_v2.py'
new=R/'book/coverage/checks/root_prepare_pages23_config_v3.py'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(old)=='7256ceed8c875961e8ecc097caf070c9727be2b9099a1c07e112d0e90af97331'
assert not new.exists()
s=old.read_text().replace('Version2 adds only the older21 audit archive as a literal website exclusion.','Version3 retains the reviewed version2 exclusions and adds only eight exact old\nreports/full-coverage inventory archives as literal website exclusions.\nThe genuine version2 budget failure and all original bytes remain preserved.')
s=s.replace('pages23-config-previous-original-v2','pages23-config-previous-original-v3').replace('pages23-config-preparation-v2','pages23-config-preparation-v3')
paths=sorted((P/'reports/full-coverage').glob('inventory*.json'))
archive_sha={p.relative_to(P).as_posix():sha(p) for p in paths}
assert len(archive_sha)==8
block='''ORIGINAL_CONFIG_V2 = "book/coverage/checks/root_prepare_pages23_config_v2.py"
ORIGINAL_CONFIG_V2_SHA = "7256ceed8c875961e8ecc097caf070c9727be2b9099a1c07e112d0e90af97331"
FAILED_CONFIG_V2 = "reports/full-coverage/pages23-config-execution-v2.json"
FAILED_CONFIG_V2_SHA = "'''+sha(R/'reports/full-coverage/pages23-config-execution-v2.json')+'''"
FAILED_CONFIG_V2_LOG_SHA = "746c7b7122bd91aaa8d7427ac6f82ab321857a84d817d42aeba22cd2e684d069"
OLD_REPORT_INVENTORY_ARCHIVES_SHA256 = '''+repr(archive_sha)+'''\n'''
s=s.replace('OWNERS = ["core", "foundations", "applied", "modules"]\n', 'OWNERS = ["core", "foundations", "applied", "modules"]\n'+block)
block='''assert sha(ROOT / ORIGINAL_CONFIG_V2) == ORIGINAL_CONFIG_V2_SHA
assert sha(ROOT / FAILED_CONFIG_V2) == FAILED_CONFIG_V2_SHA
failed_config_v2 = read(ROOT / FAILED_CONFIG_V2)
assert failed_config_v2["status"] == "failed" and failed_config_v2["actual_exit_code"] == 1
assert failed_config_v2["actual_command"] == ["python3", ORIGINAL_CONFIG_V2]
assert failed_config_v2["actual_workdir"] == str(ROOT)
assert failed_config_v2["helper_sha256_before"] == failed_config_v2["helper_sha256_after"] == {ORIGINAL_CONFIG_V2: ORIGINAL_CONFIG_V2_SHA}
assert failed_config_v2["log"] == "reports/full-coverage/pages23-config-execution-v2.log"
assert sha(ROOT / failed_config_v2["log"]) == failed_config_v2["log_sha256"] == FAILED_CONFIG_V2_LOG_SHA
assert not any((REPORTS / name).exists() for name in (
    "pages23-config-previous-original-v2.yml", "pages23-config-previous-original-v2.json", "pages23-config-preparation-v2.json"))
'''
s=s.replace('assert sha(CONFIG) == PREVIOUS22_SHA\n','assert sha(CONFIG) == PREVIOUS22_SHA\n'+block,1)
block='''# Only these eight immediate old report inventories are newly excluded. Their
# original ROOT/PUB bytes and tracked HEAD versions must match before any write.
assert {path.relative_to(PUB).as_posix() for path in (PUB / "reports/full-coverage").glob("inventory*.json")} == set(OLD_REPORT_INVENTORY_ARCHIVES_SHA256)
for name, digest in OLD_REPORT_INVENTORY_ARCHIVES_SHA256.items():
    assert sha(ROOT / name) == sha(PUB / name) == digest, name
tracked_old_inventories = subprocess.run(["git", "ls-files", "-z", "--", *sorted(OLD_REPORT_INVENTORY_ARCHIVES_SHA256)], cwd=PUB, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True)
assert {name for name in tracked_old_inventories.stdout.decode().split("\\0") if name} == set(OLD_REPORT_INVENTORY_ARCHIVES_SHA256)
subprocess.run(["git", "diff", "--quiet", "HEAD", "--", *sorted(OLD_REPORT_INVENTORY_ARCHIVES_SHA256)], cwd=PUB, check=True)
excluded.update(OLD_REPORT_INVENTORY_ARCHIVES_SHA256)
'''
s=s.replace('assert "book/coverage/inventory-after-correction51.json" in excluded\n','assert "book/coverage/inventory-after-correction51.json" in excluded\n'+block)
s=s.replace('assert all(not kept(name) for name in older_audit_sha256)\n','assert all(not kept(name) for name in older_audit_sha256)\nassert all(not kept(name) for name in OLD_REPORT_INVENTORY_ARCHIVES_SHA256)\n')
s=s.replace('assert sum(path.stat().st_size for path in PUB.rglob', 'for name, digest in OLD_REPORT_INVENTORY_ARCHIVES_SHA256.items():\n    assert sha(ROOT / name) == sha(PUB / name) == digest, name\nassert sha(ROOT / ORIGINAL_CONFIG_V2) == ORIGINAL_CONFIG_V2_SHA and sha(ROOT / FAILED_CONFIG_V2) == FAILED_CONFIG_V2_SHA\nassert sum(path.stat().st_size for path in PUB.rglob',1)
s=s.replace('        "coverage_complete": False,','''        "original_config_v2": ORIGINAL_CONFIG_V2, "original_config_v2_sha256": ORIGINAL_CONFIG_V2_SHA,
        "actual_failed_config_v2": FAILED_CONFIG_V2, "actual_failed_config_v2_sha256": FAILED_CONFIG_V2_SHA,
        "actual_failed_config_v2_exit_code": 1, "actual_failed_config_v2_raw_log_sha256": FAILED_CONFIG_V2_LOG_SHA,
        "old_report_inventory_archives_sha256_retained_exact_in_git": OLD_REPORT_INVENTORY_ARCHIVES_SHA256,
        "old_report_inventory_archive_bytes": sum((PUB / name).stat().st_size for name in OLD_REPORT_INVENTORY_ARCHIVES_SHA256),
        "coverage_complete": False,''')
s=s.replace('Actual Pages workflow and live hashes require separate execution.', 'The eight explicitly pinned old report inventory archives also remain byte-exact in Git and are excluded only from website content. The original config-v2 budget failure remains actual1; all its original/preparation outputs are absent before this version executes. Actual Pages workflow and live hashes require separate execution.')
ast.parse(s);new.write_text(s);print(new.relative_to(R),sha(new))
