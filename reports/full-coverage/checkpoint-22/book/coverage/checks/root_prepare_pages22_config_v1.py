"""Prepare a NEW literal Pages22 configuration only after actual22 audit/export.

This is a draft helper. Writing it does not execute it or modify the current
passed Pages21 configuration, owner ledgers, source HTML or publication files.
"""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
PUB = ROOT / "reports/book/publication-repo"
REPORTS = ROOT / "reports/full-coverage"
CONFIG = PUB / "_config.yml"
PREVIOUS = REPORTS / "pages22-config-previous-original-v1.yml"
REPORT = REPORTS / "pages22-config-preparation-v1.json"
PREVIOUS21_SHA = "410746b5dbe55b9f760aeabd0939dfc791bfcf59a598b4e7f3d84e1381999bc2"
INVENTORY_SHA = "2daa285ff1cbc2ad0db045e00e1271b6cb58ce809f5a8328120286748250c108"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_text())


def rel(path):
    return path.relative_to(ROOT).as_posix()


assert not PREVIOUS.exists() and not REPORT.exists()
assert sha(CONFIG) == PREVIOUS21_SHA
old_preparation = REPORTS / "pages21-config-preparation-v1.json"
assert read(old_preparation)["config_sha256"] == PREVIOUS21_SHA
old_independent = ROOT / "book/coverage/checks/pages21-config-independent-foundations-review-v1.json"
assert "passed" in read(old_independent)["status"] and read(old_independent)["config_sha256"] == PREVIOUS21_SHA
old_manifest = read(REPORTS / "checkpoint-21-manifest.json")
manifest_path = REPORTS / "checkpoint-22-manifest.json"
selection_path = REPORTS / "checkpoint-22-selection.json"
manifest = read(manifest_path)
selection = read(selection_path)
assert manifest["status"] == "formal_verification_passed_partial_coverage"
assert sha(selection_path) == manifest["selection_sha256"]
assert len(manifest["proof_files"]) == selection["proof_file_count"] > 1089
audit_path = REPORTS / "lean-checkpoint-22/verification-original.json"
audit = read(audit_path)
assert audit["status"] == "passed" and audit["proof_file_count"] == selection["proof_file_count"]
assert all(check["exit_code"] == 0 for check in audit["checks"])
assets = {name: digest for name, digest in manifest["frozen_inputs_sha256"].items() if name.startswith("SafeLearning/")}
old_assets = {name: digest for name, digest in old_manifest["frozen_inputs_sha256"].items() if name.startswith("SafeLearning/")}
assert len(assets) == 31 and assets == old_assets
required_sha256 = dict(assets)
for name, digest in assets.items():
    assert sha(ROOT / name) == sha(PUB / name) == digest, name
inventory = "book/coverage/inventory.json"
assert sha(ROOT / inventory) == sha(PUB / inventory) == INVENTORY_SHA
required_sha256[inventory] = INVENTORY_SHA
for owner in ["core", "foundations", "applied", "modules"]:
    name = "book/coverage/" + owner + ".json"
    digest = manifest["working_inputs_sha256"][name]
    assert sha(ROOT / name) == sha(PUB / name) == digest, name
    required_sha256[name] = digest
required = set(required_sha256) | {
    "reports/full-coverage/README.md", "reports/full-coverage/integration-22.json", "reports/full-coverage/browser-checkpoint-22.json",
    "reports/full-coverage/checkpoint-22-manifest.json", "reports/full-coverage/checkpoint-22-selection.json",
    "reports/full-coverage/lean-checkpoint-22/verification-original.json", "reports/full-coverage/lean-checkpoint-22/verification.json",
    "reports/full-coverage/lean-checkpoint-22/ledger-audit.json", "reports/full-coverage/owner22-reviewed-candidate-integration-v1.json"
}
for name in required:
    assert (ROOT / name).is_file() and (PUB / name).is_file(), name
    if name != "reports/full-coverage/README.md":
        assert sha(ROOT / name) == sha(PUB / name), name
    required_sha256[name] = sha(PUB / name)
before = CONFIG.read_bytes()
excluded = {line[4:] for line in before.decode().splitlines() if line.startswith("  - ")}
assert len(excluded) == 50
excluded.add("reports/full-coverage/checkpoint-22")
excluded.add("reports/full-coverage/owner21-originals-before-owner22-integration-v1")
excluded.update(str(path.relative_to(PUB)) for path in (PUB / "book/coverage").glob("inventory*.json") if path.name != "inventory.json")
assert all(name and not name.startswith("/") and ".." not in Path(name).parts and not any(character in name for character in "*?[{") for name in excluded)


def kept(name):
    return not any(name == excluded_name or name.startswith(excluded_name + "/") for excluded_name in excluded)


for name in required:
    assert kept(name), name
new_config = "# Keep complete audit archives in Git while limiting the published website.\nexclude:\n" + "".join("  - " + name + "\n" for name in sorted(excluded))
included_bytes = sum(path.stat().st_size for path in PUB.rglob("*") if path.is_file() and ".git" not in path.relative_to(PUB).parts and kept(str(path.relative_to(PUB)))) - len(before) + len(new_config.encode())
assert included_bytes < 900_000_000
with PREVIOUS.open("xb") as output:
    output.write(before)
assert sha(PREVIOUS) == PREVIOUS21_SHA
CONFIG.write_text(new_config)
for name, digest in required_sha256.items():
    assert sha(PUB / name) == digest, name
assert sum(path.stat().st_size for path in PUB.rglob("*") if path.is_file() and ".git" not in path.relative_to(PUB).parts and kept(str(path.relative_to(PUB)))) == included_bytes
with REPORT.open("x") as output:
    output.write(json.dumps({
        "status": "literal_pages22_exclusions_prepared_requires_independent_review_and_actual_pages_build",
        "prepared_at_utc": datetime.now(timezone.utc).isoformat(), "actual_helper": rel(Path(__file__)), "actual_helper_sha256": sha(Path(__file__)),
        "config_sha256": sha(CONFIG), "previous_config": rel(PREVIOUS), "previous_config_sha256": sha(PREVIOUS),
        "original_pages21_preparation": rel(old_preparation), "original_pages21_preparation_sha256": sha(old_preparation),
        "original_pages21_independent_review": rel(old_independent), "original_pages21_independent_review_sha256": sha(old_independent),
        "exclusions": sorted(excluded), "excluded_count": len(excluded), "included_file_bytes": included_bytes,
        "exact_current48_assets": assets, "required_published_paths": sorted(required), "required_published_sha256": required_sha256,
        "actual22_manifest": rel(manifest_path), "actual22_manifest_sha256": sha(manifest_path), "actual22_original_audit": rel(audit_path), "actual22_original_audit_sha256": sha(audit_path),
        "actual22_proof_file_count": selection["proof_file_count"], "coverage_complete": False,
        "scope": "Only the mutable publication configuration for a new22 build changes. Exact21 configuration bytes are preserved separately, all31 unchanged current48 source assets/live inventory/four reviewed22 ledgers/actual22 reports remain included, and archive bytes remain in Git. Actual Pages workflow and live hashes require separate execution."
    }, indent=2) + "\n")
print(json.dumps({"status": "prepared", "config_sha256": sha(CONFIG), "included_file_bytes": included_bytes, "excluded_count": len(excluded), "previous21_config_sha256": sha(PREVIOUS)}))
