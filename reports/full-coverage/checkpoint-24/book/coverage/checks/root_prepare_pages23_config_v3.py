"""Prepare literal Pages23 exclusions after the actual23 audit and export.

Version3 retains the reviewed version2 exclusions and adds only eight exact old
reports/full-coverage inventory archives as literal website exclusions.
The genuine version2 budget failure and all original bytes remain preserved.
Creating or reading this draft does not run it. Its future execution changes
only the publication configuration and creates new, separate provenance files.
An actual Pages build and live checks remain separate requirements.
"""
from datetime import datetime, timezone
import hashlib
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
PUB = ROOT / "reports/book/publication-repo"
REPORTS = ROOT / "reports/full-coverage"
CONFIG = PUB / "_config.yml"
PREVIOUS = REPORTS / "pages23-config-previous-original-v3.yml"
PREVIOUS_RECORD = REPORTS / "pages23-config-previous-original-v3.json"
REPORT = REPORTS / "pages23-config-preparation-v3.json"
PREVIOUS22_SHA = "443a2c117d1caf7d3d0236235b15af1cafc48cfd60ab8f9b60ef5a9c7909e41a"
INVENTORY_SHA = "d746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41"
MANIFEST22_SHA = "c8e4ce87ceceed0092e0593d4b6d5fed1340bc151af9aa2aaeb6e07f220413bb"
SOURCE51_REVISIONS = {
    "SafeLearning/cmdp.html": "76c03226e17b8c058fa05085e55dbe9374272541fd1c347d7a0dc98542b3795a",
    "SafeLearning/lyapunov-mpc.html": "228e4e22eaa32ad287069001abe9507706ec0112ec2ed9e1d3cfb2d569c4be7c",
}
OWNERS = ["core", "foundations", "applied", "modules"]
ORIGINAL_CONFIG_V2 = "book/coverage/checks/root_prepare_pages23_config_v2.py"
ORIGINAL_CONFIG_V2_SHA = "7256ceed8c875961e8ecc097caf070c9727be2b9099a1c07e112d0e90af97331"
FAILED_CONFIG_V2 = "reports/full-coverage/pages23-config-execution-v2.json"
FAILED_CONFIG_V2_SHA = "29ba55b594f8fc16240a2228c3911290d6bc402efc6cab0211b8a31b7b3b542d"
FAILED_CONFIG_V2_LOG_SHA = "746c7b7122bd91aaa8d7427ac6f82ab321857a84d817d42aeba22cd2e684d069"
OLD_REPORT_INVENTORY_ARCHIVES_SHA256 = {'reports/full-coverage/inventory-after-correction16.json': '34d7f404c5d838e11115bcb7bc07bb90ca77ca2816a7f834adaab1260c22abb3', 'reports/full-coverage/inventory-after-correction18.json': '05ed4925d229f3d61fa10a1df6eea881bb7f0d5ec8ecadc1bab64c91373d7731', 'reports/full-coverage/inventory-before-correction10.json': 'e2f15b65c554a75eee7895a5821dc34167d9e3c11967e964614c6088328e98ca', 'reports/full-coverage/inventory-before-correction11.json': '371bb2a0f6b93f8e63ea1e2a512e0bc35fede092b69a1afa911138726562b179', 'reports/full-coverage/inventory-before-correction13.json': 'd3deb7d3e8bd67a43938d5279ff559aa25822197a9a521a5a8751d7570e025ec', 'reports/full-coverage/inventory-before-correction16.json': '6100fe5ce71510cdd04ccba12f6150bd1a2045d6f3802b2358174172af4c9249', 'reports/full-coverage/inventory-before-correction18.json': '9d30dd5c926e8f29203555ed613400a05e08b097f3c168b463ebbe3ae680c1f4', 'reports/full-coverage/inventory-before-surrounding-expansion.json': 'bd751b1e6bfb50dfd428f5f2546d65949e0ce0b9cbcab7256c7e4ea8aa4925bd'}
APPLIED_UNSELECTED_METADATA = [
    "verification/lean/SafeLearning/CompleteAppliedBinaryTemperaturePrecision.lean",
    "verification/lean/SafeLearning/CompleteAppliedBinaryVariationalPrecision.lean",
    "verification/lean/SafeLearning/CompleteAppliedConformalCalibrationOnly.lean",
]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_text())


def rel(path):
    return path.relative_to(ROOT).as_posix()


assert not any(path.exists() for path in [PREVIOUS, PREVIOUS_RECORD, REPORT])
assert sha(CONFIG) == PREVIOUS22_SHA
assert sha(ROOT / ORIGINAL_CONFIG_V2) == ORIGINAL_CONFIG_V2_SHA
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
old_preparation = REPORTS / "pages22-config-preparation-v2.json"
old_independent = ROOT / "book/coverage/checks/pages22-config-independent-modules-review-v1.json"
assert sha(old_preparation) == "b32835ce52a9d4c6286842485a866c838b9d7b170bc16c5141b106afffc2b61e"
assert sha(old_independent) == "82c2d80e2e361142d7a842cdf438633822ec5f3c0f2b684237a092dba07d63d4"
old_prepared = read(old_preparation)
assert old_prepared["config_sha256"] == PREVIOUS22_SHA and old_prepared["excluded_count"] == 52
assert "passed" in read(old_independent)["status"] and read(old_independent)["config_sha256"] == PREVIOUS22_SHA
old_manifest_path = REPORTS / "checkpoint-22-manifest.json"
assert sha(old_manifest_path) == MANIFEST22_SHA
old_manifest = read(old_manifest_path)
manifest_path = REPORTS / "checkpoint-23-manifest.json"
selection_path = REPORTS / "checkpoint-23-selection.json"
manifest = read(manifest_path)
selection = read(selection_path)
assert manifest["status"] == "formal_verification_passed_partial_coverage"
assert sha(selection_path) == manifest["selection_sha256"]
assert len(manifest["proof_files"]) == selection["proof_file_count"] == 1131
assert len(old_manifest["proof_files"]) == 1113
assert set(old_manifest["proof_files"]) <= set(manifest["proof_files"])
assert len(set(manifest["proof_files"]) - set(old_manifest["proof_files"])) == 18
audit_path = REPORTS / "lean-checkpoint-23/verification-original.json"
audit = read(audit_path)
assert audit["status"] == "passed" and audit["proof_file_count"] == 1131 and audit["theorem_count"] == 9193
assert len(audit["declarations"]) == 9193 and all(check["exit_code"] == 0 for check in audit["checks"])
old_audit = read(REPORTS / "lean-checkpoint-22/verification-original.json")
assert old_audit["status"] == "passed" and old_audit["proof_file_count"] == 1113 and old_audit["theorem_count"] == 9002
assert all(audit["proof_sha256"][name] == old_audit["proof_sha256"][name] for name in old_manifest["proof_files"])

assets = {name: digest for name, digest in manifest["frozen_inputs_sha256"].items() if name.startswith("SafeLearning/")}
old_assets = {name: digest for name, digest in old_manifest["frozen_inputs_sha256"].items() if name.startswith("SafeLearning/")}
expected_assets = dict(old_assets)
expected_assets.update(SOURCE51_REVISIONS)
assert len(assets) == len(old_assets) == 31 and assets == expected_assets
assert {name for name in assets if assets[name] != old_assets[name]} == set(SOURCE51_REVISIONS)
required_sha256 = dict(assets)
for name, digest in assets.items():
    assert sha(ROOT / name) == sha(PUB / name) == sha(ROOT / "reports/full-coverage/checkpoint-23" / name) == digest, name
for name, digest in old_assets.items():
    assert sha(ROOT / "reports/full-coverage/checkpoint-22" / name) == digest, name
inventory = "book/coverage/inventory.json"
assert sha(ROOT / inventory) == sha(PUB / inventory) == sha(ROOT / "book/coverage/inventory-after-correction51.json") == INVENTORY_SHA
required_sha256[inventory] = INVENTORY_SHA
for owner in OWNERS:
    name = "book/coverage/" + owner + ".json"
    working_digest = manifest["working_inputs_sha256"][name]
    frozen_digest = manifest["frozen_inputs_sha256"][name]
    assert sha(ROOT / name) == working_digest, name
    assert sha(PUB / name) == sha(ROOT / "reports/full-coverage/checkpoint-23" / name) == frozen_digest, name
    working_ledger = read(ROOT / name)
    frozen_ledger = read(PUB / name)
    excluded = manifest["excluded_unreferenced_ledger_metadata"][owner]
    assert excluded == (APPLIED_UNSELECTED_METADATA if owner == "applied" else []), (owner, excluded)
    assert set(working_ledger["proof_files"]) - set(manifest["proof_files"]) == set(excluded)
    listed = working_ledger["proof_files"]
    working_ledger["proof_files"] = ([n for n in listed if n in manifest["proof_files"]] if isinstance(listed, list) else {n: v for n, v in listed.items() if n in manifest["proof_files"]})
    if "proof_sha256" in working_ledger:
        working_ledger["proof_sha256"] = {n: v for n, v in working_ledger["proof_sha256"].items() if n in manifest["proof_files"]}
    assert working_ledger == frozen_ledger, name
    required_sha256[name] = frozen_digest

required = set(required_sha256) | {
    "reports/full-coverage/README.md", "reports/full-coverage/integration-23.json", "reports/full-coverage/browser-checkpoint-23.json",
    "reports/full-coverage/checkpoint-23-manifest.json", "reports/full-coverage/checkpoint-23-selection.json",
    "reports/full-coverage/lean-checkpoint-23/verification-original.json", "reports/full-coverage/lean-checkpoint-23/verification.json",
    "reports/full-coverage/lean-checkpoint-23/ledger-audit.json", "reports/full-coverage/owner23-reviewed-candidate-integration-v1.json",
}
owner_paths = {"book/coverage/" + owner + ".json" for owner in OWNERS}
for name in required:
    assert (ROOT / name).is_file() and (PUB / name).is_file(), name
    if name != "reports/full-coverage/README.md" and name not in owner_paths:
        assert sha(ROOT / name) == sha(PUB / name), name
    required_sha256[name] = sha(PUB / name)

# These are the exact original32 archived trials at the21 freeze, not selected proofs.
manifest21 = read(REPORTS / "checkpoint-21-manifest.json")
archival32 = {name: digest for name, digest in manifest21["frozen_inputs_sha256"].items() if name.startswith("book/coverage/checks/future22-monitoring/")}
assert len(archival32) == 32
assert all(name not in manifest["proof_files"] for name in archival32)
for name, digest in archival32.items():
    assert sha(ROOT / name) == sha(PUB / name) == digest, name

before = CONFIG.read_bytes()
old_exclusions = {line[4:] for line in before.decode().splitlines() if line.startswith("  - ")}
assert len(old_exclusions) == 52 and old_exclusions == set(old_prepared["exclusions"])
assert before.decode() == "# Keep complete audit archives in Git while limiting the published website.\nexclude:\n" + "".join("  - " + name + "\n" for name in sorted(old_exclusions))
excluded = set(old_exclusions)
excluded.add("reports/full-coverage/checkpoint-23")
# This older audit is already preserved in Git. Only its website inclusion changes.
older_audit_archive = "reports/full-coverage/lean-checkpoint-21"
older_audit_root = ROOT / older_audit_archive
older_audit_pub = PUB / older_audit_archive
assert older_audit_root.is_dir() and older_audit_pub.is_dir()
older_audit_sha256 = {path.relative_to(ROOT).as_posix(): sha(path) for path in older_audit_root.rglob("*") if path.is_file()}
assert older_audit_sha256 and older_audit_archive + "/verification-original.json" in older_audit_sha256
assert {path.relative_to(PUB).as_posix(): sha(path) for path in older_audit_pub.rglob("*") if path.is_file()} == older_audit_sha256
tracked_result = subprocess.run(["git", "ls-files", "-z", "--", older_audit_archive], cwd=PUB, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True)
assert {name for name in tracked_result.stdout.decode().split("\0") if name} == set(older_audit_sha256)
subprocess.run(["git", "diff", "--quiet", "HEAD", "--", older_audit_archive], cwd=PUB, check=True)
excluded.add(older_audit_archive)
excluded.add("reports/full-coverage/owner22-originals-before-owner23-integration-v1")
inventory_archives = {path.relative_to(PUB).as_posix() for path in (PUB / "book/coverage").glob("inventory*.json") if path.name != "inventory.json"}
excluded.update(inventory_archives)
assert "book/coverage/inventory-after-correction51.json" in excluded
# Only these eight immediate old report inventories are newly excluded. Their
# original ROOT/PUB bytes and tracked HEAD versions must match before any write.
assert {path.relative_to(PUB).as_posix() for path in (PUB / "reports/full-coverage").glob("inventory*.json")} == set(OLD_REPORT_INVENTORY_ARCHIVES_SHA256)
for name, digest in OLD_REPORT_INVENTORY_ARCHIVES_SHA256.items():
    assert sha(ROOT / name) == sha(PUB / name) == digest, name
tracked_old_inventories = subprocess.run(["git", "ls-files", "-z", "--", *sorted(OLD_REPORT_INVENTORY_ARCHIVES_SHA256)], cwd=PUB, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True)
assert {name for name in tracked_old_inventories.stdout.decode().split("\0") if name} == set(OLD_REPORT_INVENTORY_ARCHIVES_SHA256)
subprocess.run(["git", "diff", "--quiet", "HEAD", "--", *sorted(OLD_REPORT_INVENTORY_ARCHIVES_SHA256)], cwd=PUB, check=True)
excluded.update(OLD_REPORT_INVENTORY_ARCHIVES_SHA256)
assert all(name and not name.startswith("/") and ".." not in Path(name).parts and not any(character in name for character in "*?[{") for name in excluded)


def kept(name):
    return not any(name == excluded_name or name.startswith(excluded_name + "/") for excluded_name in excluded)


for name in required:
    assert kept(name), name
assert all(not kept(name) for name in archival32)
assert all(not kept(name) for name in older_audit_sha256)
assert all(not kept(name) for name in OLD_REPORT_INVENTORY_ARCHIVES_SHA256)
assert kept("reports/full-coverage/lean-checkpoint-22/verification-original.json")
new_config = "# Keep complete audit archives in Git while limiting the published website.\nexclude:\n" + "".join("  - " + name + "\n" for name in sorted(excluded))
included_bytes = sum(path.stat().st_size for path in PUB.rglob("*") if path.is_file() and ".git" not in path.relative_to(PUB).parts and kept(path.relative_to(PUB).as_posix())) - len(before) + len(new_config.encode())
assert included_bytes < 900_000_000
with PREVIOUS.open("xb") as output:
    output.write(before)
assert sha(PREVIOUS) == PREVIOUS22_SHA
with PREVIOUS_RECORD.open("x") as output:
    output.write(json.dumps({
        "status": "exact_original_pages22_configuration_preserved_before_pages23_change",
        "preserved_at_utc": datetime.now(timezone.utc).isoformat(),
        "original_configuration": rel(PREVIOUS), "original_configuration_sha256": sha(PREVIOUS),
        "original_exclusions": sorted(old_exclusions), "original_excluded_count": 52,
        "original_pages22_preparation": rel(old_preparation), "original_pages22_preparation_sha256": sha(old_preparation),
        "original_pages22_independent_review": rel(old_independent), "original_pages22_independent_review_sha256": sha(old_independent),
        "scope": "Exact original22 bytes and original evidence are preserved. This record does not claim an actual23 Pages build."
    }, indent=2) + "\n")
CONFIG.write_text(new_config)
for name, digest in required_sha256.items():
    assert sha(PUB / name) == digest, name
for name, digest in older_audit_sha256.items():
    assert sha(PUB / name) == digest, name
for name, digest in OLD_REPORT_INVENTORY_ARCHIVES_SHA256.items():
    assert sha(ROOT / name) == sha(PUB / name) == digest, name
assert sha(ROOT / ORIGINAL_CONFIG_V2) == ORIGINAL_CONFIG_V2_SHA and sha(ROOT / FAILED_CONFIG_V2) == FAILED_CONFIG_V2_SHA
assert sum(path.stat().st_size for path in PUB.rglob("*") if path.is_file() and ".git" not in path.relative_to(PUB).parts and kept(path.relative_to(PUB).as_posix())) == included_bytes
with REPORT.open("x") as output:
    output.write(json.dumps({
        "status": "literal_pages23_exclusions_prepared_requires_independent_review_and_actual_pages_build",
        "prepared_at_utc": datetime.now(timezone.utc).isoformat(), "actual_helper": rel(Path(__file__)), "actual_helper_sha256": sha(Path(__file__)),
        "config_sha256": sha(CONFIG), "previous_config": rel(PREVIOUS), "previous_config_sha256": sha(PREVIOUS),
        "previous_config_record": rel(PREVIOUS_RECORD), "previous_config_record_sha256": sha(PREVIOUS_RECORD),
        "original_pages22_preparation": rel(old_preparation), "original_pages22_preparation_sha256": sha(old_preparation),
        "original_pages22_independent_review": rel(old_independent), "original_pages22_independent_review_sha256": sha(old_independent),
        "exclusions": sorted(excluded), "excluded_count": len(excluded), "included_file_bytes": included_bytes,
        "exact_current51_assets": assets, "deliberate_source51_asset_revisions_from22": SOURCE51_REVISIONS,
        "required_published_paths": sorted(required), "required_published_sha256": required_sha256,
        "actual23_manifest": rel(manifest_path), "actual23_manifest_sha256": sha(manifest_path),
        "actual23_original_audit": rel(audit_path), "actual23_original_audit_sha256": sha(audit_path),
        "actual23_proof_file_count": 1131, "actual23_public_theorem_count": 9193, "baseline22_proof_file_count": 1113, "new23_proof_file_count": 18,
        "excluded_unreferenced_ledger_metadata": manifest["excluded_unreferenced_ledger_metadata"],
        "working_owner_ledger_sha256": {"book/coverage/" + owner + ".json": manifest["working_inputs_sha256"]["book/coverage/" + owner + ".json"] for owner in OWNERS},
        "original32_archival_trial_sha256_retained_unselected": archival32,
        "older21_audit_archive_sha256_retained_exact_in_git": older_audit_sha256,
        "older21_audit_archive_bytes": sum((PUB / name).stat().st_size for name in older_audit_sha256),
        "original_config_v2": ORIGINAL_CONFIG_V2, "original_config_v2_sha256": ORIGINAL_CONFIG_V2_SHA,
        "actual_failed_config_v2": FAILED_CONFIG_V2, "actual_failed_config_v2_sha256": FAILED_CONFIG_V2_SHA,
        "actual_failed_config_v2_exit_code": 1, "actual_failed_config_v2_raw_log_sha256": FAILED_CONFIG_V2_LOG_SHA,
        "old_report_inventory_archives_sha256_retained_exact_in_git": OLD_REPORT_INVENTORY_ARCHIVES_SHA256,
        "old_report_inventory_archive_bytes": sum((PUB / name).stat().st_size for name in OLD_REPORT_INVENTORY_ARCHIVES_SHA256),
        "coverage_complete": False,
        "scope": "Only the mutable publication configuration for a new23 build changes. Exact22 configuration bytes are preserved separately. All31 source51 assets, current inventory, four frozen23 publication ledgers and actual23 reports remain included; working ledgers differ only by the exact3 manifest-declared unused Applied metadata removals. Archives remain in Git, including the exact older21 audit archive whose tracked HEAD bytes are checked before exclusion. The eight explicitly pinned old report inventory archives also remain byte-exact in Git and are excluded only from website content. The original config-v2 budget failure remains actual1; all its original/preparation outputs are absent before this version executes. Actual Pages workflow and live hashes require separate execution."
    }, indent=2) + "\n")
print(json.dumps({"status": "prepared", "config_sha256": sha(CONFIG), "included_file_bytes": included_bytes, "excluded_count": len(excluded), "previous22_config_sha256": sha(PREVIOUS)}))
