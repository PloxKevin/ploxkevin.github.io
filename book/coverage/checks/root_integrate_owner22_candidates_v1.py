"""Guard an explicit Root release of four independently reviewed owner candidates.

This helper changes no owner asset by default. Root must supply a complete final
binding manifest and --apply after the Core candidate has its final peer.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
REPORTS = ROOT / "reports/full-coverage"
OWNERS = {name: "book/coverage/" + name + ".json" for name in ["core", "foundations", "applied", "modules"]}
AUXILIARIES = {"book/coverage/applied-promotions.json"}
MUTABLE_DELIVERY_METADATA = {"book/coverage/progress.json", "book/coverage/README.md", "reports/full-coverage/README.md"}
BASE_MANIFEST = "reports/full-coverage/checkpoint-21-manifest.json"
BASE_SHA = "f5d27edc32eb5d952b1cfc92424f3ab6399dd37586885b59e15fee6028184010"
INVENTORY_SHA = "2daa285ff1cbc2ad0db045e00e1271b6cb58ce809f5a8328120286748250c108"


def safe_path(name):
    name = Path(name)
    assert not name.is_absolute() and ".." not in name.parts and str(name) not in {"", "."}
    target = ROOT / name
    assert target.resolve().is_relative_to(ROOT.resolve())
    return target


def sha(name):
    return hashlib.sha256(safe_path(name).read_bytes()).hexdigest()


def read(name):
    return json.loads(safe_path(name).read_text())


def reference(row):
    assert set(["file", "sha256"]) <= set(row)
    assert sha(row["file"]) == row["sha256"], row["file"]
    return read(row["file"])


def pointer(data, keys):
    assert isinstance(keys, list) and keys
    for key in keys:
        data = data[key]
    return data


def write_new(name, data):
    with safe_path(name).open("x") as output:
        output.write(json.dumps(data, ensure_ascii=False, indent=2) + "\n")


arguments = argparse.ArgumentParser()
arguments.add_argument("bindings", help="Complete final versioned JSON binding manifest, relative to Root")
arguments.add_argument("--apply", action="store_true", help="Root release: copy only exact reviewed candidate bytes after all preconditions pass")
args = arguments.parse_args()
binding = read(args.bindings)
assert binding["status"] == "all_four_reviewed_current48_owner_candidates_bound_ready_for_root_execution"
assert binding["helper"]["file"] == str(Path(__file__).relative_to(ROOT))
assert binding["helper"]["sha256"] == hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
helper_peer = reference(binding["independent_helper_review"])
assert "passed" in helper_peer["status"] and helper_peer.get("errors", []) == []
assert helper_peer["helper_sha256"] == binding["helper"]["sha256"]
assert set(binding["owners"]) == set(OWNERS)
assert binding["baseline21_manifest"] == {"file": BASE_MANIFEST, "sha256": BASE_SHA}
assert sha(BASE_MANIFEST) == BASE_SHA
manifest = read(BASE_MANIFEST)
assert manifest["status"] == "formal_verification_passed_partial_coverage"
assert len(manifest["proof_files"]) == 1089 and len(manifest["frozen_inputs_sha256"]) == 32040
assert sha(manifest["selection"]) == manifest["selection_sha256"]
selection = read(manifest["selection"])
assert selection["proof_file_count"] == 1089
assert sha("book/coverage/inventory.json") == sha("book/coverage/inventory-after-correction48.json") == binding["inventory_sha256"] == INVENTORY_SHA
snapshot = safe_path(manifest["snapshot"])
assets = {name: digest for name, digest in manifest["frozen_inputs_sha256"].items() if name.startswith("SafeLearning/")}
assert len(assets) == 31 and assets == binding["exact_current48_safelearning_assets_sha256"]


def verify_frozen_and_sources():
    for name, digest in manifest["frozen_inputs_sha256"].items():
        original = snapshot / name
        assert original.resolve().is_relative_to(snapshot.resolve())
        assert hashlib.sha256(original.read_bytes()).hexdigest() == digest, ("frozen21", name)
    for name, row in manifest["proof_files"].items():
        assert sha(name) == row["sha256"], ("selected21", name)
    for name, digest in assets.items():
        assert sha(name) == digest, ("current48", name)
    assert sha("book/coverage/inventory.json") == sha("book/coverage/inventory-after-correction48.json") == INVENTORY_SHA


verify_frozen_and_sources()
replacements = []
retained_reference_sha256 = {binding["independent_helper_review"]["file"]: binding["independent_helper_review"]["sha256"]}
seen_new_proofs = {}
for owner in sorted(OWNERS):
    row = binding["owners"][owner]
    assert row["ready"] is True and row["held21_ledger"] == OWNERS[owner]
    assert row["held21_ledger_sha256"] == manifest["working_inputs_sha256"][OWNERS[owner]]
    assert sha(row["held21_ledger"]) == row["held21_ledger_sha256"], owner
    candidate = row["candidate_ledger"]
    candidate_data = reference(candidate)
    offer = reference(row["reviewed_final_offer"])
    assert pointer(offer, row["offer_candidate_path_pointer"]) == candidate["file"]
    assert pointer(offer, row["offer_candidate_sha256_pointer"]) == candidate["sha256"]
    peer = reference(row["independent_candidate_mapping_peer"])
    assert "passed" in peer["status"] and peer.get("errors", []) == []
    assert pointer(peer, row["peer_candidate_path_pointer"]) == candidate["file"]
    assert pointer(peer, row["peer_candidate_sha256_pointer"]) == candidate["sha256"]
    assert row["original_full_source_semantic_reviews"]
    for ref in row["original_full_source_semantic_reviews"]:
        semantic = reference(ref)
        assert semantic["status"] == ref["original_review_status"], ref["file"]
        assert semantic.get("errors", []) == [], ref["file"]
        reviewed_time = semantic.get("reviewed_at_utc", semantic.get("checked_at_utc"))
        assert reviewed_time == ref["original_review_time"], ref["file"]
        retained_reference_sha256[ref["file"]] = ref["sha256"]
    actual_builder = reference(row["actual_candidate_builder"])
    assert actual_builder["actual_exit_code"] == 0
    for ref in row.get("additional_exact_provenance", []):
        assert sha(ref["file"]) == ref["sha256"]
        retained_reference_sha256[ref["file"]] = ref["sha256"]
    for name, digest in candidate_data["source_sha256"].items():
        assert digest == sha(name), (owner, name)
        if name.startswith("SafeLearning/"):
            assert assets[name] == digest, (owner, name)
        else:
            assert manifest["working_inputs_sha256"].get(name, manifest["frozen_inputs_sha256"].get(name)) == digest, (owner, name)
    assert set(row["new_immutable_proof_sources"]) == set(offer["proof_files"])
    for name, proof in row["new_immutable_proof_sources"].items():
        assert name not in manifest["proof_files"] and sha(name) == proof["sha256"]
        assert offer["proof_files"][name]["sha256"] == proof["sha256"]
        if name in seen_new_proofs:
            assert seen_new_proofs[name] == proof["sha256"]
        seen_new_proofs[name] = proof["sha256"]
        assert len(proof["actual_pair"]) == 2
        for ref in proof["actual_pair"]:
            execution = reference(ref)
            exits = [execution[field] for field in ["exit_code", "actual_exit_code"] if field in execution]
            assert exits and all(value == 0 for value in exits)
            assert execution["source"] == ref["actual_source"] == name
            assert execution["command"] == ref["actual_command"]
            assert execution["actual_workdir"] == ref["actual_workdir"] == str(ROOT / "verification/lean")
            assert execution["source_sha256_before"] == execution["source_sha256_after"] == proof["sha256"]
            log = ref["canonical_raw_log"]
            assert sha(log["file"]) == log["sha256"] == execution["log_sha256"]
            retained_reference_sha256[ref["file"]] = ref["sha256"]
            retained_reference_sha256[log["file"]] = log["sha256"]
    replacements.append({"destination": OWNERS[owner], "before_sha256": row["held21_ledger_sha256"], "candidate": candidate})
    assert len(row.get("companion_candidates", [])) == (1 if owner == "applied" else 0)
    for auxiliary in row.get("companion_candidates", []):
        destination = auxiliary["held21_asset"]
        assert owner == "applied" and destination in AUXILIARIES
        assert auxiliary["held21_asset_sha256"] == manifest["working_inputs_sha256"][destination] == sha(destination)
        reference(auxiliary["candidate"])
        assert offer["mapped_promotions"] == auxiliary["candidate"]["file"] and offer["mapped_promotions_sha256"] == auxiliary["candidate"]["sha256"]
        replacements.append({"destination": destination, "before_sha256": auxiliary["held21_asset_sha256"], "candidate": auxiliary["candidate"]})
    for ref in [row["reviewed_final_offer"], row["independent_candidate_mapping_peer"], row["actual_candidate_builder"]]:
        retained_reference_sha256[ref["file"]] = ref["sha256"]
assert len({row["destination"] for row in replacements}) == len(replacements)
allowed_destinations = set(OWNERS.values()) | AUXILIARIES
assert set(row["destination"] for row in replacements) <= allowed_destinations
untouched_working = {name: digest for name, digest in manifest["working_inputs_sha256"].items() if name not in allowed_destinations | MUTABLE_DELIVERY_METADATA}
for name, digest in untouched_working.items():
    assert sha(name) == digest, ("held21_working", name)
report_name = "reports/full-coverage/owner22-reviewed-candidate-integration-v1.json" if args.apply else "reports/full-coverage/owner22-integration-guard-dry-run-v1.json"
assert not safe_path(report_name).exists()
archive_name = "reports/full-coverage/owner21-originals-before-owner22-integration-v1"
if args.apply:
    archive = safe_path(archive_name)
    assert not archive.exists()
    archive.mkdir()
    for row in replacements:
        original = safe_path(row["destination"])
        preserved = archive / original.name
        with preserved.open("xb") as output:
            output.write(original.read_bytes())
        assert hashlib.sha256(preserved.read_bytes()).hexdigest() == row["before_sha256"]
        row["original21_byte_copy"] = str(preserved.relative_to(ROOT))
    for row in replacements:
        original = safe_path(row["destination"])
        assert sha(row["destination"]) == row["before_sha256"]
        assert sha(row["candidate"]["file"]) == row["candidate"]["sha256"]
        temporary = original.with_name(original.name + ".owner22-reviewed-copy-v1.tmp")
        assert not temporary.exists()
        with temporary.open("xb") as output:
            output.write(safe_path(row["candidate"]["file"]).read_bytes())
        assert hashlib.sha256(temporary.read_bytes()).hexdigest() == row["candidate"]["sha256"]
        os.replace(temporary, original)
        assert sha(row["destination"]) == row["candidate"]["sha256"]
    verify_frozen_and_sources()
    for name, digest in untouched_working.items():
        assert sha(name) == digest, ("held21_after_integration", name)
    for name, digest in retained_reference_sha256.items():
        assert sha(name) == digest, ("original_peer_after_integration", name)
write_new(report_name, {
    "status": "four_exact_reviewed_owner22_candidate_bytes_integrated_pending_fresh_global_integrity_and_aggregate22_audit" if args.apply else "passed_read_only_complete_four_owner22_integration_preconditions",
    "checked_at_utc": datetime.now(timezone.utc).isoformat(), "actual_helper": str(Path(__file__).relative_to(ROOT)),
    "actual_helper_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), "binding_manifest": args.bindings, "binding_manifest_sha256": sha(args.bindings),
    "applied": args.apply, "exact_replacements": replacements, "all32040_frozen21_inputs_exact": True, "all1089_selected21_root_source_hashes_exact": True,
    "all31_current48_safelearning_assets_exact": True, "inventory_sha256": INVENTORY_SHA,
    "other_held21_working_inputs_rechecked": len(untouched_working), "original_semantic_and_candidate_peer_reference_sha256": retained_reference_sha256,
    "new_immutable_proof_sources_sha256": seen_new_proofs, "coverage_complete": False,
    "scope": "Only the explicit reviewed candidate bytes and the required Applied promotion companion may be copied. Existing21 snapshot, selected proofs, source48 HTML/inventory, original helpers/offers/semantic reviews and execution histories remain exact. Aggregate22 and site22 status require separate actual checks."
})
print(json.dumps({"status": "integrated" if args.apply else "passed_read_only", "report": report_name, "report_sha256": sha(report_name), "replacement_count": len(replacements), "new_source_count": len(seen_new_proofs)}))
