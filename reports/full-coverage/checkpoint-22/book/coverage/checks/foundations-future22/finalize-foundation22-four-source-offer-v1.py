"""Finalize only the independently reviewed immutable four-source owner offer."""
from datetime import datetime, timezone
import copy
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
HERE = ROOT / "book/coverage/checks/foundations-future22"
OFFER = ROOT / "book/coverage/foundations-audit22-source48-additions-v1.json"
FINAL = HERE / "foundations-source48-four-source-final-offer-readiness-v1.json"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_text())


def rel(path):
    return path.relative_to(ROOT).as_posix()


def write_new(path, data):
    with path.open("x") as output:
        output.write(json.dumps(data, ensure_ascii=False, indent=2) + "\n")


assert not OFFER.exists() and not FINAL.exists()
draft_path = HERE / "foundations-source48-integration-offer22-draft-v1.json"
assert sha(draft_path) == "bb4d6dcb74a62d1fd0e694c8e250383bad42624c7fae3a43896a7153e213ce89"
draft = read(draft_path)
peer_path = HERE / "foundations-source48-candidate22-independent-modules-confirmation-v2.json"
assert sha(peer_path) == "55a295eaad07c32ee0c49ee197fc96011d1e365b766ad80216a59db7acf7ab4b"
peer = read(peer_path)
assert "passed" in peer["status"] and peer["errors"] == [] and all(peer["checks"].values())
for own, other in [("mapped_ledger", "candidate_ledger"), ("material22_exact_interface_binding", "interface_binding")]:
    assert draft[own] == peer[other]
    assert sha(ROOT / draft[own]) == draft[own + "_sha256"] == peer[other + "_sha256"]
assert peer["draft_offer"] == rel(draft_path) and peer["draft_offer_sha256"] == sha(draft_path)
assert sha(ROOT / draft["held21_ledger"]) == draft["held21_ledger_sha256"] == peer["held21_ledger_sha256"]
assert sha(ROOT / draft["current_inventory"]) == draft["current_inventory_sha256"] == peer["inventory_sha256"]
assert sha(ROOT / "book/coverage/inventory.json") == draft["current_inventory_sha256"]
builder_path = ROOT / draft["current_owner_builder"]
assert sha(builder_path) == draft["current_owner_builder_sha256"]
builder_record_path = HERE / "foundations-source48-material22-builder-execution-v1.json"
builder_record = read(builder_record_path)
assert builder_record["actual_exit_code"] == 0 and builder_record["status"] == "passed"
assert builder_record["actual_checker_sha256"] == sha(builder_path)
assert sha(ROOT / builder_record["original_log"]) == builder_record["original_log_sha256"]
peer_record_path = HERE / "foundations-source48-candidate22-independent-modules-checker-execution-v2.json"
peer_record = read(peer_record_path)
assert peer_record["actual_exit_code"] == 0 and peer_record["status"] == "passed"
assert peer_record["actual_checker_sha256"] == peer["checker_sha256"]
assert sha(ROOT / peer_record["log"]) == peer_record["log_sha256"]
reader_history_path = HERE / "foundations-source48-candidate22-independent-reader-history-v1.json"
reader_history = read(reader_history_path)
for row in reader_history["copies"]:
    assert sha(ROOT / row["canonical_byte_copy"]) == row["sha256"]
for name in [reader_history["failed_actual_record"], reader_history["passing_actual_record"]]:
    record = read(ROOT / name)
    assert sha(ROOT / record["log"]) == record["log_sha256"]
assert read(ROOT / reader_history["failed_actual_record"])["actual_exit_code"] != 0
evidence = {}
for field in ["exact_source_reviews_sha256", "canonical_source_peer_bindings_sha256", "actual_canonical_execution_records_sha256"]:
    for name, digest in draft[field].items():
        assert sha(ROOT / name) == digest
        evidence[name] = digest
for name, row in draft["proof_files"].items():
    assert sha(ROOT / name) == row["sha256"]
    for record_name, digest in row["evidence_sha256"].items():
        record = read(ROOT / record_name)
        assert sha(ROOT / record_name) == digest and record["exit_code"] == 0
        assert record["source_sha256_before"] == record["source_sha256_after"] == row["sha256"]
        assert sha(ROOT / record["log"]) == record["log_sha256"]
selection = read(ROOT / draft["base_selection"])
assert sha(ROOT / draft["base_selection"]) == draft["base_selection_sha256"] and selection["proof_file_count"] == 1089
protected = {name: row["sha256"] for name, row in selection["proof_files"].items()}
protected.update(read(HERE / "original-tmp/foundations-future22-tmp-proof-index-v1.json")["held_checkpoint21_assets_exact"])
protected.update(read(ROOT / draft["held21_ledger"])["source_sha256"])
for name, digest in protected.items():
    assert sha(ROOT / name) == digest, name
offer = copy.deepcopy(draft)
offer.update({
    "status": "ready_actual_zero_source48_foundation22_material_proofs_and_independently_confirmed_candidate_mapping",
    "finalized_at_utc": datetime.now(timezone.utc).isoformat(),
    "original_reviewed_draft": rel(draft_path), "original_reviewed_draft_sha256": sha(draft_path),
    "independent_final_candidate_mapping_peer_pending": False,
    "independent_final_loader_mapping_peer_pending": False,
    "independent_final_candidate_mapping_peer": rel(peer_path), "independent_final_candidate_mapping_peer_sha256": sha(peer_path),
    "independent_final_candidate_mapping_peer_actual_execution": rel(peer_record_path),
    "independent_final_candidate_mapping_peer_actual_execution_sha256": sha(peer_record_path),
    "independent_candidate_reader_failure_and_correction_history": rel(reader_history_path),
    "independent_candidate_reader_failure_and_correction_history_sha256": sha(reader_history_path),
    "actual_builder_record": rel(builder_record_path), "actual_builder_record_sha256": sha(builder_record_path),
    "finalization_helper": rel(Path(__file__)), "finalization_helper_sha256": sha(Path(__file__)),
    "canonical_build_readiness": rel(HERE / "four-canonical-paired-build-readiness-v1.json"),
    "canonical_build_readiness_sha256": sha(HERE / "four-canonical-paired-build-readiness-v1.json"),
    "final_literal_peer_checker_archive": rel(HERE / "final-peer-checker-byte-copies-v1.json"),
    "final_literal_peer_checker_archive_sha256": sha(HERE / "final-peer-checker-byte-copies-v1.json"),
    "exercise_counts": {"whole": 119, "partial": 0, "pending": 0, "total": 119},
    "scope": "Four genuine future22 immutable proof additions and sixteen complete source48 material literals in a separate versioned candidate; held21 owner ledger remains exact."
})
write_new(OFFER, offer)
for name, digest in protected.items():
    assert sha(ROOT / name) == digest, name
write_new(FINAL, {
    "status": "passed_final_owner_offer_exact_independent_candidate_and_actual_execution_bound",
    "checked_at_utc": datetime.now(timezone.utc).isoformat(), "offer": rel(OFFER), "offer_sha256": sha(OFFER),
    "candidate_ledger": draft["mapped_ledger"], "candidate_ledger_sha256": draft["mapped_ledger_sha256"],
    "held21_ledger": draft["held21_ledger"], "held21_ledger_sha256": draft["held21_ledger_sha256"],
    "current_inventory_sha256": draft["current_inventory_sha256"],
    "independent_candidate_mapping_peer_sha256": sha(peer_path),
    "actual_builder_record_sha256": sha(builder_record_path), "actual_peer_execution_record_sha256": sha(peer_record_path),
    "actual_helper": rel(Path(__file__)), "actual_helper_sha256": sha(Path(__file__)),
    "protected21_paths_rechecked": len(protected), "all1089_selected21_sources_exact": True,
    "new_sources": 4, "new_theorems": 36, "whole_material_units": 16,
    "coverage_complete": False, "aggregate22_kernel_and_axiom_audit_required": True
})
print(json.dumps({"status": "passed", "offer": rel(OFFER), "offer_sha256": sha(OFFER), "final_readiness_sha256": sha(FINAL)}))
