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
BASE_MANIFEST = "reports/full-coverage/checkpoint-22-manifest.json"
BASE_SHA = "c8e4ce87ceceed0092e0593d4b6d5fed1340bc151af9aa2aaeb6e07f220413bb"
INVENTORY_SHA = "d746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41"


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
assert binding["status"] == "all_four_reviewed_current51_owner_candidates_bound_ready_for_root_execution"
assert binding["helper"]["file"] == str(Path(__file__).relative_to(ROOT))
assert binding["helper"]["sha256"] == hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
helper_peer = reference(binding["independent_helper_review"])
assert "passed" in helper_peer["status"] and helper_peer.get("errors", []) == []
assert helper_peer["helper_sha256"] == binding["helper"]["sha256"]
assert set(binding["owners"]) == set(OWNERS)
assert binding["baseline22_manifest"] == {"file": BASE_MANIFEST, "sha256": BASE_SHA}
assert sha(BASE_MANIFEST) == BASE_SHA
manifest = read(BASE_MANIFEST)
assert manifest["status"] == "formal_verification_passed_partial_coverage"
assert len(manifest["proof_files"]) == 1113 and len(manifest["frozen_inputs_sha256"]) == 34051
assert sha(manifest["selection"]) == manifest["selection_sha256"]
selection = read(manifest["selection"])
assert selection["proof_file_count"] == 1113
assert sha("book/coverage/inventory.json") == sha("book/coverage/inventory-after-correction51.json") == binding["inventory_sha256"] == INVENTORY_SHA
snapshot = safe_path(manifest["snapshot"])
assets = {name: digest for name, digest in manifest["frozen_inputs_sha256"].items() if name.startswith("SafeLearning/")}
assert len(assets) == 31
original22_assets = assets
assets = binding["exact_current51_safelearning_assets_sha256"]
assert assets.keys() == original22_assets.keys()
assert {n for n in assets if assets[n] != original22_assets[n]} == {"SafeLearning/cmdp.html", "SafeLearning/lyapunov-mpc.html"}
assert assets["SafeLearning/cmdp.html"] == "76c03226e17b8c058fa05085e55dbe9374272541fd1c347d7a0dc98542b3795a"
assert assets["SafeLearning/lyapunov-mpc.html"] == "228e4e22eaa32ad287069001abe9507706ec0112ec2ed9e1d3cfb2d569c4be7c"
source51 = reference(binding["actual_source51_apply"])
source51_postwrite = reference(binding["actual_source51_postwrite"])
assert source51["actual_exit_code"] == source51_postwrite["actual_exit_code"] == 0
assert source51_postwrite["inventory_after_sha256"] == INVENTORY_SHA
assert sha(source51["log"]) == source51["log_sha256"]
assert sha("book/coverage/material-corrections.json") == binding["source51_corrections_sha256"]
assert len(read("book/coverage/material-corrections.json")["corrections"]) == 51


def verify_frozen_and_sources():
    for name, digest in manifest["frozen_inputs_sha256"].items():
        original = snapshot / name
        assert original.resolve().is_relative_to(snapshot.resolve())
        assert hashlib.sha256(original.read_bytes()).hexdigest() == digest, ("frozen22", name)
    for name, row in manifest["proof_files"].items():
        assert sha(name) == row["sha256"], ("selected22", name)
    for name, digest in assets.items():
        assert sha(name) == digest, ("current51", name)
    assert sha("book/coverage/inventory.json") == sha("book/coverage/inventory-after-correction51.json") == INVENTORY_SHA


verify_frozen_and_sources()
replacements = []
retained_reference_sha256 = {binding["independent_helper_review"]["file"]: binding["independent_helper_review"]["sha256"]}
seen_new_proofs = {}
held22_non_safelearning_source_sha256 = {}
for owner in sorted(OWNERS):
    row = binding["owners"][owner]
    assert row["ready"] is True and row["held22_ledger"] == OWNERS[owner]
    assert row["held22_ledger_sha256"] == manifest["working_inputs_sha256"][OWNERS[owner]]
    assert sha(row["held22_ledger"]) == row["held22_ledger_sha256"], owner
    held22_ledger_data = read(row["held22_ledger"])
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
            # These chapter HTML sources belong to the exact held22 owner ledger.
            # Their absence from the frozen manifest must not be misreported.
            assert held22_ledger_data["source_sha256"][name] == digest, (owner, name)
            assert name not in held22_non_safelearning_source_sha256 or held22_non_safelearning_source_sha256[name] == digest
            held22_non_safelearning_source_sha256[name] = digest
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
    replacements.append({"destination": OWNERS[owner], "before_sha256": row["held22_ledger_sha256"], "candidate": candidate})
    assert len(row.get("companion_candidates", [])) == (1 if owner == "applied" else 0)
    for auxiliary in row.get("companion_candidates", []):
        destination = auxiliary["held22_asset"]
        assert owner == "applied" and destination in AUXILIARIES
        assert auxiliary["held22_asset_sha256"] == manifest["working_inputs_sha256"][destination] == sha(destination)
        reference(auxiliary["candidate"])
        assert offer["mapped_promotions"] == auxiliary["candidate"]["file"] and offer["mapped_promotions_sha256"] == auxiliary["candidate"]["sha256"]
        replacements.append({"destination": destination, "before_sha256": auxiliary["held22_asset_sha256"], "candidate": auxiliary["candidate"]})
    for ref in [row["reviewed_final_offer"], row["independent_candidate_mapping_peer"], row["actual_candidate_builder"]]:
        retained_reference_sha256[ref["file"]] = ref["sha256"]
assert len({row["destination"] for row in replacements}) == len(replacements)
allowed_destinations = set(OWNERS.values()) | AUXILIARIES
assert set(row["destination"] for row in replacements) <= allowed_destinations
authorized_source_updates = {"SafeLearning/cmdp.html", "SafeLearning/lyapunov-mpc.html", "book/coverage/inventory.json", "book/coverage/material-corrections.json"}
untouched_working = {name: digest for name, digest in manifest["working_inputs_sha256"].items() if name not in allowed_destinations | MUTABLE_DELIVERY_METADATA | authorized_source_updates}
for name, digest in untouched_working.items():
    assert sha(name) == digest, ("held22_working", name)
report_name = "reports/full-coverage/owner23-reviewed-candidate-integration-v1.json" if args.apply else "reports/full-coverage/owner23-integration-guard-dry-run-v1.json"
assert not safe_path(report_name).exists()
archive_name = "reports/full-coverage/owner22-originals-before-owner23-integration-v1"
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
        row["original22_byte_copy"] = str(preserved.relative_to(ROOT))
    for row in replacements:
        original = safe_path(row["destination"])
        assert sha(row["destination"]) == row["before_sha256"]
        assert sha(row["candidate"]["file"]) == row["candidate"]["sha256"]
        temporary = original.with_name(original.name + ".owner23-reviewed-copy-v1.tmp")
        assert not temporary.exists()
        with temporary.open("xb") as output:
            output.write(safe_path(row["candidate"]["file"]).read_bytes())
        assert hashlib.sha256(temporary.read_bytes()).hexdigest() == row["candidate"]["sha256"]
        os.replace(temporary, original)
        assert sha(row["destination"]) == row["candidate"]["sha256"]
    verify_frozen_and_sources()
    for name, digest in untouched_working.items():
        assert sha(name) == digest, ("held22_after_integration", name)
    for name, digest in retained_reference_sha256.items():
        assert sha(name) == digest, ("original_peer_after_integration", name)
    for name, digest in held22_non_safelearning_source_sha256.items():
        assert sha(name) == digest, ("held22_ledger_source_after_integration", name)
write_new(report_name, {
    "status": "four_exact_reviewed_owner23_candidate_bytes_integrated_pending_fresh_global_integrity_and_aggregate23_audit" if args.apply else "passed_read_only_complete_four_owner23_integration_preconditions",
    "checked_at_utc": datetime.now(timezone.utc).isoformat(), "actual_helper": str(Path(__file__).relative_to(ROOT)),
    "actual_helper_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), "binding_manifest": args.bindings, "binding_manifest_sha256": sha(args.bindings),
    "applied": args.apply, "exact_replacements": replacements, "all34051_frozen22_inputs_exact": True, "all1113_selected22_root_source_hashes_exact": True,
    "all31_current51_safelearning_assets_exact": True, "inventory_sha256": INVENTORY_SHA,
    "other_held22_working_inputs_rechecked": len(untouched_working), "original_semantic_and_candidate_peer_reference_sha256": retained_reference_sha256,
    "new_immutable_proof_sources_sha256": seen_new_proofs,
    "non_safelearning_source_sha256_bound_to_exact_held22_ledgers_and_current_bytes": held22_non_safelearning_source_sha256,
    "coverage_complete": False,
    "scope": "Only the explicit reviewed candidate bytes and the required Applied promotion companion may be copied. Existing22 snapshot, selected proofs, source51 HTML/inventory, original helpers/offers/semantic reviews and execution histories remain exact. Aggregate23 and site23 status require separate actual checks."
})
print(json.dumps({"status": "integrated" if args.apply else "passed_read_only", "report": report_name, "report_sha256": sha(report_name), "replacement_count": len(replacements), "new_source_count": len(seen_new_proofs)}))
