"""Finalize a new v2 owner offer only after its independent delta peer passed."""
import argparse
import copy
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
HERE = ROOT / "book/coverage/checks/foundations-future22"
OFFER = ROOT / "book/coverage/foundations-audit22-source48-additions-v2.json"
READINESS = HERE / "foundations-source48-five-source-final-offer-readiness-v2.json"
PAIRS = HERE / "foundations-source48-five-source-actual-paired-record-readiness-v2.json"


def path(name):
    name = Path(name)
    return name if name.is_absolute() else ROOT / name


def sha(name):
    return hashlib.sha256(path(name).read_bytes()).hexdigest()


def read(name):
    return json.loads(path(name).read_text())


def rel(name):
    return path(name).relative_to(ROOT).as_posix()


def write_new(name, data):
    with path(name).open("x") as output:
        output.write(json.dumps(data, ensure_ascii=False, indent=2) + "\n")


arguments = argparse.ArgumentParser()
arguments.add_argument("peer")
arguments.add_argument("peer_sha256")
arguments.add_argument("peer_execution")
args = arguments.parse_args()
assert not OFFER.exists() and not READINESS.exists() and not PAIRS.exists()
draft_path = HERE / "foundations-source48-integration-offer22-draft-v2.json"
assert sha(draft_path) == "defa9e655ae484813647f075d36a993ea387852b911dac700dde10dd106066e2"
draft = read(draft_path)
assert sha(args.peer) == args.peer_sha256
peer = read(args.peer)
assert "passed" in peer["status"] and peer.get("errors", []) == []
for field in ["candidate_ledger", "interface_binding", "draft_offer"]:
    assert field in peer and field + "_sha256" in peer
expected = {"candidate_ledger": "mapped_ledger", "interface_binding": "material22_exact_interface_binding"}
for independent, own in expected.items():
    assert peer[independent] == draft[own]
    assert sha(draft[own]) == draft[own + "_sha256"] == peer[independent + "_sha256"]
assert peer["draft_offer"] == rel(draft_path) and peer["draft_offer_sha256"] == sha(draft_path)
for value in peer.get("checks", {}).values():
    assert value is True
peer_execution = read(args.peer_execution)
assert peer_execution["actual_exit_code"] == 0 and peer_execution["status"] == "passed"
assert peer_execution["actual_checker_sha256"] == peer["checker_sha256"]
peer_log_field = "log" if "log" in peer_execution else "original_log"
assert sha(peer_execution[peer_log_field]) == peer_execution[peer_log_field + "_sha256"]
assert sha(draft["prior_v1_final_offer"]) == draft["prior_v1_final_offer_sha256"] == "bf8432b89badbd44e5f3998470f26af3f3bb07ee88fe68853ceb6184e5eb1662"
assert sha(draft["held21_ledger"]) == draft["held21_ledger_sha256"] == "c16c0662b2f74a4d4e30d477d3c8bf0008e2456fdebf506d5f6f6144d150db11"
assert sha(draft["current_inventory"]) == sha("book/coverage/inventory.json") == draft["current_inventory_sha256"] == "2daa285ff1cbc2ad0db045e00e1271b6cb58ce809f5a8328120286748250c108"
assert sha(draft["current_owner_builder"]) == draft["current_owner_builder_sha256"]
builder_record_path = HERE / "foundations-source48-material22-builder-execution-v2.json"
builder_record = read(builder_record_path)
assert builder_record["status"] == "passed" and builder_record["actual_exit_code"] == 0
assert builder_record["actual_checker_sha256"] == draft["current_owner_builder_sha256"]
assert sha(builder_record["original_log"]) == builder_record["original_log_sha256"]
for field in ["exact_source_reviews_sha256", "canonical_source_peer_bindings_sha256", "actual_canonical_execution_records_sha256"]:
    for name, digest in draft[field].items():
        assert sha(name) == digest
assert len(draft["proof_files"]) == draft["new_proof_file_count"] == 5 and draft["new_theorem_or_lemma_count"] == 45
for name, row in draft["proof_files"].items():
    assert sha(name) == row["sha256"]
    for record_name, digest in row["evidence_sha256"].items():
        record = read(record_name)
        assert sha(record_name) == digest and record["exit_code"] == 0
        assert record["source_sha256_before"] == record["source_sha256_after"] == row["sha256"]
        assert sha(record["log"]) == record["log_sha256"]
integrity_path = HERE / "foundations-source48-v1-held-and-uniform-v2-extension-integrity-v1.json"
integrity = read(integrity_path)
for name, digest in integrity["protected_sha256"].items():
    if name == builder_record["original_log"]:
        assert digest == hashlib.sha256(b"").hexdigest()
        assert sha(name) == builder_record["original_log_sha256"]
    else:
        assert sha(name) == digest, name
assert integrity["new_candidate_sha256"] == draft["mapped_ledger_sha256"]
correction_path = HERE / "foundations-source48-v2-completed-builder-log-guard-correction-v1.json"
assert not correction_path.exists()
failed_finalizer_path = HERE / "foundations-source48-five-source-offer-finalization-execution-v2.json"
assert read(failed_finalizer_path)["actual_exit_code"] != 0
write_new(correction_path, {"status": "only_new_v2_builder_transient_empty_log_guard_bound_to_completed_actual_execution",
    "checked_at_utc": datetime.now(timezone.utc).isoformat(), "original_integrity": rel(integrity_path), "original_integrity_sha256": sha(integrity_path),
    "one_original_transient_entry": builder_record["original_log"], "original_precompletion_sha256": hashlib.sha256(b"").hexdigest(),
    "actual_completed_log_sha256": builder_record["original_log_sha256"], "actual_builder_record": rel(builder_record_path), "actual_builder_record_sha256": sha(builder_record_path),
    "preserved_failed_finalizer": rel(failed_finalizer_path), "preserved_failed_finalizer_sha256": sha(failed_finalizer_path),
    "all_original_v1_and_selected21_protected_entries_still_exact": True,
    "scope": "The wrapper created its new log before the v2 builder started; the builder snapshot saw it empty before genuine output was appended. Only that new running log is bound to its completed actual execution record. No original held21/v1 input, candidate, semantic peer, prior execution or integrity record is altered."})
assert len(draft["actual_canonical_execution_records_sha256"]) == 10
write_new(PAIRS, {"status": "five_immutable_sources_ten_actual_canonical_standalone_and_named_records_verified_exit_zero", "checked_at_utc": datetime.now(timezone.utc).isoformat(),
    "proof_source_sha256": {name: row["sha256"] for name, row in draft["proof_files"].items()}, "actual_records_sha256": draft["actual_canonical_execution_records_sha256"],
    "source_count": 5, "public_theorem_count": 45, "scope": "Exact existing individual canonical execution records are checked; no new compiler execution or aggregate22 audit is performed or inferred.", "coverage_complete": False})
offer = copy.deepcopy(draft)
offer["prior_v1_canonical_build_readiness"] = offer["canonical_build_readiness"]
offer["prior_v1_canonical_build_readiness_sha256"] = offer["canonical_build_readiness_sha256"]
offer.update({
    "status": "ready_actual_zero_source48_foundation22_v2_material_proofs_and_independently_confirmed_delta_mapping",
    "finalized_at_utc": datetime.now(timezone.utc).isoformat(),
    "original_reviewed_draft": rel(draft_path), "original_reviewed_draft_sha256": sha(draft_path),
    "independent_final_candidate_mapping_peer_pending": False, "independent_final_loader_mapping_peer_pending": False,
    "independent_final_candidate_mapping_peer": rel(args.peer), "independent_final_candidate_mapping_peer_sha256": sha(args.peer),
    "independent_final_candidate_mapping_peer_actual_execution": rel(args.peer_execution), "independent_final_candidate_mapping_peer_actual_execution_sha256": sha(args.peer_execution),
    "actual_builder_record": rel(builder_record_path), "actual_builder_record_sha256": sha(builder_record_path),
    "v1_preservation_and_new_uniform_v2_integrity": rel(integrity_path), "v1_preservation_and_new_uniform_v2_integrity_sha256": sha(integrity_path),
    "finalization_helper": rel(Path(__file__)), "finalization_helper_sha256": sha(Path(__file__)),
    "completed_v2_builder_log_guard_correction": rel(correction_path), "completed_v2_builder_log_guard_correction_sha256": sha(correction_path),
    "preserved_failed_finalization_v2": rel(failed_finalizer_path), "preserved_failed_finalization_v2_sha256": sha(failed_finalizer_path),
    "canonical_build_readiness": rel(PAIRS), "canonical_build_readiness_sha256": sha(PAIRS),
    "scope_notes": [
        "All original119 whole exercises, every earlier proved atom and all unrelated material decisions remain exact. Seventeen separately approved complete literals replace only their own nineteen pending clause records.",
        "The held21 owner ledger/helpers/offer and original four-source future22 candidate/interface/offer remain immutable. The mapped ledger is a new v2 candidate with only node1167 added to its sixteen prior complete decisions.",
        "Five new immutable sources/45 public theorem bodies have ten genuine canonical standalone and named target execution records with exits0. The four earlier source pairs are reused without rerunning or replacing any historical record.",
        "The fresh whole uniform-continuity review reads all nine actual theorem bodies, both Lipschitz branches, the exact point-dependent continuity distinction and both actual nonuniform counterexamples. Its original body and review time remain exact.",
        "A fresh aggregate22 build, kernel replay and axiom audit remain required before publication. This owner offer asserts only its actual paired source evidence and separately confirmed candidate mappings."
    ],
    "coverage_complete": False
})
write_new(OFFER, offer)
for name, digest in integrity["protected_sha256"].items():
    if name == builder_record["original_log"]:
        assert digest == hashlib.sha256(b"").hexdigest()
        assert sha(name) == builder_record["original_log_sha256"]
    else:
        assert sha(name) == digest, name
write_new(READINESS, {"status": "passed_final_five_source_owner_offer_exact_independent_delta_peer_and_actual_builder_bound", "checked_at_utc": datetime.now(timezone.utc).isoformat(),
    "offer": rel(OFFER), "offer_sha256": sha(OFFER), "candidate_ledger": draft["mapped_ledger"], "candidate_ledger_sha256": draft["mapped_ledger_sha256"],
    "held21_ledger_sha256": draft["held21_ledger_sha256"], "inventory_sha256": draft["current_inventory_sha256"],
    "prior_v1_offer_sha256": draft["prior_v1_final_offer_sha256"], "independent_delta_peer_sha256": sha(args.peer),
    "actual_builder_record_sha256": sha(builder_record_path), "actual_peer_execution_record_sha256": sha(args.peer_execution),
    "new_sources": 5, "new_public_theorems": 45, "complete_material_units": 17, "physical_material_counts": draft["material_counts"],
    "aggregate22_kernel_and_axiom_audit_required": True, "coverage_complete": False})
print(json.dumps({"status": "passed", "offer": rel(OFFER), "offer_sha256": sha(OFFER), "readiness_sha256": sha(READINESS)}))
