"""Prepare literal Pages23 exclusions after the actual23 audit and export.

Creating or reading this draft does not run it. Its future execution changes
only the publication configuration and creates new, separate provenance files.
An actual Pages build and live checks remain separate requirements.
"""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
PUB = ROOT / "reports/book/publication-repo"
REPORTS = ROOT / "reports/full-coverage"
CONFIG = PUB / "_config.yml"
PREVIOUS = REPORTS / "pages23-config-previous-original-v1.yml"
PREVIOUS_RECORD = REPORTS / "pages23-config-previous-original-v1.json"
REPORT = REPORTS / "pages23-config-preparation-v1.json"
PREVIOUS22_SHA = "443a2c117d1caf7d3d0236235b15af1cafc48cfd60ab8f9b60ef5a9c7909e41a"
INVENTORY_SHA = "d746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41"
MANIFEST22_SHA = "c8e4ce87ceceed0092e0593d4b6d5fed1340bc151af9aa2aaeb6e07f220413bb"
SOURCE51_REVISIONS = {
    "SafeLearning/cmdp.html": "76c03226e17b8c058fa05085e55dbe9374272541fd1c347d7a0dc98542b3795a",
    "SafeLearning/lyapunov-mpc.html": "228e4e22eaa32ad287069001abe9507706ec0112ec2ed9e1d3cfb2d569c4be7c",
}
OWNERS = ["core", "foundations", "applied", "modules"]
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
excluded.add("reports/full-coverage/owner22-originals-before-owner23-integration-v1")
inventory_archives = {path.relative_to(PUB).as_posix() for path in (PUB / "book/coverage").glob("inventory*.json") if path.name != "inventory.json"}
excluded.update(inventory_archives)
assert "book/coverage/inventory-after-correction51.json" in excluded
assert all(name and not name.startswith("/") and ".." not in Path(name).parts and not any(character in name for character in "*?[{") for name in excluded)


def kept(name):
    return not any(name == excluded_name or name.startswith(excluded_name + "/") for excluded_name in excluded)


for name in required:
    assert kept(name), name
assert all(not kept(name) for name in archival32)
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
        "original32_archival_trial_sha256_retained_unselected": archival32, "coverage_complete": False,
        "scope": "Only the mutable publication configuration for a new23 build changes. Exact22 configuration bytes are preserved separately. All31 source51 assets, current inventory, four frozen23 publication ledgers and actual23 reports remain included; working ledgers differ only by the exact3 manifest-declared unused Applied metadata removals. Archives remain in Git. Actual Pages workflow and live hashes require separate execution."
    }, indent=2) + "\n")
print(json.dumps({"status": "prepared", "config_sha256": sha(CONFIG), "included_file_bytes": included_bytes, "excluded_count": len(excluded), "previous22_config_sha256": sha(PREVIOUS)}))
