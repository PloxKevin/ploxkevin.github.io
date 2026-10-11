"""Build a separate source48 Foundation22 candidate from exact approved packets.

The held Foundation21 ledger/helpers/offer remain untouched. Final integration
offer publication is a separate step after independent candidate mapping review.
"""
from collections import Counter
import copy
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
HERE = ROOT / "book/coverage/checks/foundations-future22"
BASE = ROOT / "book/coverage/foundations.json"
BASE_SHA = "c16c0662b2f74a4d4e30d477d3c8bf0008e2456fdebf506d5f6f6144d150db11"
INVENTORY_SHA = "2daa285ff1cbc2ad0db045e00e1271b6cb58ce809f5a8328120286748250c108"
CANDIDATE = HERE / "foundations-source48-candidate-ledger22-v1.json"
BINDING = HERE / "foundations-source48-material22-interface-binding-v1.json"
DRAFT = HERE / "foundations-source48-integration-offer22-draft-v1.json"
CHECKER_COPIES = HERE / "final-peer-checker-byte-copies-v1.json"
sys.path.insert(0, str(ROOT / "book/coverage"))
from lean_names import declarations


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_text())


def fingerprint(data):
    return hashlib.sha256(json.dumps(data, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def write_new(path, data):
    with path.open("x") as output:
        output.write(json.dumps(data, ensure_ascii=False, indent=2) + "\n")


assert not any(path.exists() for path in [CANDIDATE, BINDING, DRAFT, CHECKER_COPIES])
assert sha(BASE) == BASE_SHA
baseline = read(BASE)
assert baseline["status"] == "partial"
inventory_path = ROOT / "book/coverage/inventory-after-correction48.json"
assert sha(inventory_path) == sha(ROOT / "book/coverage/inventory.json") == INVENTORY_SHA
inventory = {row["key"]: row for row in read(inventory_path)["material_source_units"]}
selection_path = ROOT / "reports/full-coverage/checkpoint-21-selection.json"
selection = read(selection_path)
assert selection["proof_file_count"] == 1089
audit_path = ROOT / "reports/full-coverage/lean-checkpoint-21/verification-original.json"
audit = read(audit_path)
assert audit["status"] == "passed" and audit["proof_file_count"] == 1089
assert all(row["exit_code"] == 0 for row in audit["checks"])
protected = dict(read(HERE / "original-tmp/foundations-future22-tmp-proof-index-v1.json")["held_checkpoint21_assets_exact"])
protected.update({name: row["sha256"] for name, row in selection["proof_files"].items()})
protected.update(baseline["source_sha256"])
for name, digest in protected.items():
    assert sha(ROOT / name) == digest, name

packets = [
    ("RKHSBounds22", "linalg-rkhs-bounds-two-units-independent-applied-source-review22-v1.json", "1d76fb496a73220f33bc5a5930ea37192cdfee09dcba157c31d2f22147cc0428", "applied", "7e4d8b8425ff76aabaf33adee6d368822e256a3f633718c8c55efcc534986633", 2, 5),
    ("WorkedSafety22", "foundations-worked-safety-nine-literals-independent-modules-source-review22-v1.json", "5e22ce19b0529961103aa9cdc33dc8484bb73c9cf82ac7bb099b3c9e8b21974f", "modules", "c35c478fb3da7fed385f2c7026741d113a608a2e7b21825087ad3783ebaa279b", 9, 15),
    ("ContinuousLevels22", "basics-continuous-levels-three-units-independent-applied-source-review22-v1.json", "8dbd2db6414b60e00fc14702c98a36a462442a9db6b93467988f7e0ac3e2bb1a", "applied", "e403ef68592be0072379e316692fd79371cd4f30f642e00c582e9fefe61884b8", 3, 7),
    ("MetricDefinitions22", "basics-metric-definitions-two-units-independent-applied-source-review22-v1.json", "6928d320b8e048d48b6bc1d02a610d4b6df363837efe8a88c44844c9439697b4", "applied", "e0d8d32e40c73148f4fbfe8d9be8c954b59236c7cecdb618c4cce5bb973aca09", 2, 9),
]
approved = {}
new_proofs = {}
review_hashes = {}
peer_hashes = {}
actual_execution_hashes = {}
checker_paths = {}
packet_rows = []
for suffix, original_name, original_sha, reviewer, peer_sha, units_count, theorem_count in packets:
    original_path = HERE / "original-tmp" / original_name
    assert sha(original_path) == original_sha
    original = read(original_path)
    peer_path = HERE / (suffix + "-canonical-source-and-review-binding-independent-" + reviewer + "-confirmation-v1.json")
    assert sha(peer_path) == peer_sha
    peer = read(peer_path)
    if reviewer == "applied":
        assert peer["status"] == "independent_original_whole_literals_exact_canonical_source_and_paired_execution_binding_confirmed"
        assert peer["errors"] == []
        binding = peer["binding"]
        assert binding["archived_original_review_sha256"] == original_sha
        assert binding["entire_original_body_decisions_and_time_preserved"]
        assert peer["material_units"] == original["material_units"]
        source_name = binding["canonical_source"]
        source_sha = binding["canonical_source_sha256"]
        combined_path = ROOT / peer["compound_actual_confirmation"]
        assert sha(combined_path) == peer["compound_actual_confirmation_sha256"]
        combined = read(combined_path)
        assert combined["errors"] == [] and combined["protected21_integrity"]["all_exact"]
        checker_paths[peer["extraction_checker"]] = peer["extraction_checker_sha256"]
        checker_paths[combined["checker"]] = combined["checker_sha256"]
    else:
        assert "passed" in peer["status"] and peer["original_semantic_body_unchanged"]
        assert peer["original_review_sha256"] == original_sha
        assert peer["original_reviewed_at_utc"] == original["reviewed_at_utc"]
        source_name = peer["canonical_source"]
        source_sha = peer["canonical_source_sha256"]
        for item, decision in zip(peer["exact_literal_decision_bindings"], original["material_units"]):
            assert item["source_unit_key"] == decision["source_unit_key"]
            assert item["original_unit_decision_sha256"] == fingerprint(decision)
            assert item["entire_inventory_record_sha256"] == fingerprint(decision["entire_inventory_record"])
        checker_paths[peer["checker"]] = peer["checker_sha256"]
    source_path = ROOT / source_name
    assert sha(source_path) == source_sha and source_name not in selection["proof_files"]
    assert sha(HERE / "sources" / (source_path.stem + "-source-v1.lean")) == source_sha
    names = declarations(source_path.read_text())
    assert sum(row["kind"] in {"theorem", "lemma"} for row in names) == theorem_count
    evidence = {}
    for mode in ["standalone-v1", "named-build-v1"]:
        record_path = HERE / (source_path.stem + "-" + mode + ".json")
        record = read(record_path)
        assert record["exit_code"] == 0
        assert record["source_sha256_before"] == record["source_sha256_after"] == source_sha
        assert sha(ROOT / record["log"]) == record["log_sha256"]
        evidence[record_path.relative_to(ROOT).as_posix()] = sha(record_path)
        actual_execution_hashes.update(evidence)
    new_proofs[source_name] = {"sha256": source_sha, "evidence_sha256": evidence,
                              "evidence_scope": "Actual canonical standalone and exact named target build passed for these immutable bytes; fresh aggregate22 audit is still required."}
    review_hashes[original_path.relative_to(ROOT).as_posix()] = original_sha
    peer_hashes[peer_path.relative_to(ROOT).as_posix()] = peer_sha
    assert len(original["material_units"]) == units_count
    for row in original["material_units"]:
        key = row["source_unit_key"]
        assert key not in approved and row["entire_inventory_record"] == inventory[key]
        assert row["material_status"] == "proved" and row["whole_unit_approved"] and row["missing_clauses"] == []
        assert row["lean_declarations"]
        approved[key] = {"original_unit_row": row, "original_review": original_path.relative_to(ROOT).as_posix(),
                         "original_review_sha256": original_sha, "original_reviewed_at_utc": original["reviewed_at_utc"],
                         "canonical_peer": peer_path.relative_to(ROOT).as_posix(), "canonical_peer_sha256": peer_sha}
    packet_rows.append({"module": source_path.stem, "source": source_name, "source_sha256": source_sha,
                        "whole_literal_units": units_count, "new_public_theorems": theorem_count,
                        "actual_execution_records_sha256": evidence, "original_review_sha256": original_sha,
                        "canonical_final_peer_sha256": peer_sha})
assert len(approved) == 16 and len(new_proofs) == 4
for original_name, digest in checker_paths.items():
    original = Path(original_name)
    assert sha(original) == digest
    target = HERE / "peer-checkers" / original.name
    target.parent.mkdir(exist_ok=True)
    assert not target.exists()
    with target.open("xb") as output:
        output.write(original.read_bytes())
    assert sha(target) == digest
write_new(CHECKER_COPIES, {"status": "exact_final_independent_peer_checkers_preserved", "original_to_canonical": {name: (HERE / "peer-checkers" / Path(name).name).relative_to(ROOT).as_posix() for name in checker_paths}, "original_sha256": checker_paths})

candidate = copy.deepcopy(baseline)
removed_pending = []
retained = []
for claim in baseline["material_claims"]:
    intersect = set(claim["source_unit_keys"]) & set(approved)
    if intersect:
        assert len(claim["source_unit_keys"]) == 1
        if claim["status"] == "pending":
            removed_pending.append(claim)
            continue
    retained.append(claim)
candidate["material_claims"] = copy.deepcopy(retained)
interface = []
for key, ref in sorted(approved.items()):
    row = ref["original_unit_row"]
    unit = inventory[key]
    old_claims = [claim for claim in baseline["material_claims"] if key in claim["source_unit_keys"]]
    assert any(claim["status"] == "pending" for claim in old_claims), key
    new_claim = {"id": key + "::reviewed22-whole-literal", "source_unit_keys": [key], "source": unit["source"],
                 "locator": unit["locator"], "source_text": unit["source_text"], "source_text_sha256": unit["text_sha256"],
                 "source_sha256": unit["source_sha256"], "statement_in_prose": unit["source_text"],
                 "kind": "independently_reviewed_complete_mathematical_literal", "status": "proved",
                 "lean_declarations": row["lean_declarations"], "hypotheses": row["hypotheses"],
                 "correspondence": row["per_unit_reason"] + " Original complete literal review: " + ref["original_review"] + ". Exact canonical source/paired evidence confirmation: " + ref["canonical_peer"] + ".",
                 "remaining_gaps": []}
    candidate["material_claims"].append(new_claim)
    interface.append({"source_unit_key": key, "exact_current48_inventory_record": unit, **ref,
                      "original_current21_claims": old_claims, "retained_original_proved_or_nonformal_claims": [claim for claim in old_claims if claim["status"] != "pending"],
                      "removed_pending_clauses": [claim for claim in old_claims if claim["status"] == "pending"], "new_candidate_claim": new_claim})
assert candidate["exercises"] == baseline["exercises"]
assert candidate["surrounding_prose_reviews"] == baseline["surrounding_prose_reviews"]
assert [claim for claim in candidate["material_claims"] if not set(claim["source_unit_keys"]) & set(approved)] == [claim for claim in baseline["material_claims"] if not set(claim["source_unit_keys"]) & set(approved)]
proof_files = set(baseline["proof_files"]) | set(new_proofs)
for row in approved.values():
    for name in row["original_unit_row"]["lean_declarations"]:
        assert name.startswith("SafeLearning."), name
        proof_files.add("verification/lean/SafeLearning/" + name.split(".")[1] + ".lean")
declared = set()
for name in sorted(proof_files):
    path = ROOT / name
    assert name in selection["proof_files"] or name in new_proofs, name
    if name in selection["proof_files"]:
        assert sha(path) == selection["proof_files"][name]["sha256"]
    declared.update(row["name"] for row in declarations(path.read_text()))
assert all(set(row["original_unit_row"]["lean_declarations"]) <= declared for row in approved.values())
candidate["proof_files"] = sorted(proof_files)
candidate["proof_sha256"] = {name: sha(ROOT / name) for name in sorted(proof_files)}
candidate["counts"]["material_claim_statuses"] = dict(Counter(claim["status"] for claim in candidate["material_claims"]))


def physical_counts(ledger):
    statuses = {}
    for claim in ledger["material_claims"]:
        for key in claim["source_unit_keys"]:
            statuses.setdefault(key, set()).add(claim["status"])
    counts = Counter("pending" if "pending" in values else "not_a_formal_claim" if values == {"not_a_formal_claim"} else "proved" for values in statuses.values())
    return {"total": len(statuses), "whole_proved": counts["proved"], "nonformal": counts["not_a_formal_claim"], "whole_pending": counts["pending"]}


before = physical_counts(baseline)
after = physical_counts(candidate)
assert after["total"] == before["total"] == 1756
assert after["whole_proved"] == before["whole_proved"] + 16
assert after["whole_pending"] == before["whole_pending"] - 16
assert after["nonformal"] == before["nonformal"]
candidate["current22_material_mapping"] = {"baseline_held21_ledger": BASE.relative_to(ROOT).as_posix(), "baseline_held21_ledger_sha256": BASE_SHA,
                                           "interface_binding": BINDING.relative_to(ROOT).as_posix(), "individually_whole_approved_material_units": 16,
                                           "removed_prior_pending_claims": len(removed_pending), "physical_before": before, "physical_after": after,
                                           "scope": "Separate future22 candidate only; no held current21 owner ledger mutation or exercise promotion."}
candidate["limits"].append("This is a source48 candidate with sixteen independently complete literals and genuine new standalone/named builds; integrator must separately select and run actual aggregate22 kernel/axiom verification before publication.")
write_new(CANDIDATE, candidate)
write_new(BINDING, {"status": "exact_source48_original_whole_reviews_and_canonical_pairs_bound_to_separate_foundation22_candidate", "prepared_at_utc": datetime.now(timezone.utc).isoformat(),
                    "baseline_held21_ledger": BASE.relative_to(ROOT).as_posix(), "baseline_held21_ledger_sha256": BASE_SHA,
                    "inventory": inventory_path.relative_to(ROOT).as_posix(), "inventory_sha256": INVENTORY_SHA,
                    "candidate_ledger": CANDIDATE.relative_to(ROOT).as_posix(), "candidate_ledger_sha256": sha(CANDIDATE),
                    "material_units": interface, "proof_packets": packet_rows, "physical_before": before, "physical_after": after,
                    "all119_original_whole_exercises_unchanged": True, "all_nonselected_material_rows_unchanged": True,
                    "all_original_approved_atoms_retained": True, "coverage_complete": False})
reused = {name: candidate["proof_sha256"][name] for name in sorted(proof_files - set(new_proofs))}
draft = {"schema_version": 1, "status": "draft_actual_zero_source48_foundation22_offer_requires_independent_candidate_mapping_review", "prepared_at_utc": datetime.now(timezone.utc).isoformat(),
         "base_selection": selection_path.relative_to(ROOT).as_posix(), "base_selection_sha256": sha(selection_path),
         "actual_passing_baseline_audit": audit_path.relative_to(ROOT).as_posix(), "actual_passing_baseline_audit_sha256": sha(audit_path),
         "proof_files": new_proofs, "new_proof_sources_for_checkpoint22": sorted(new_proofs), "new_proof_file_count": 4, "new_theorem_or_lemma_count": 36,
         "reused_selected21_proof_source_sha256": reused, "reused_selected21_proof_source_count": len(reused),
         "mapped_ledger": CANDIDATE.relative_to(ROOT).as_posix(), "mapped_ledger_sha256": sha(CANDIDATE),
         "held21_ledger": BASE.relative_to(ROOT).as_posix(), "held21_ledger_sha256": BASE_SHA,
         "source_sha256": baseline["source_sha256"], "current_inventory": inventory_path.relative_to(ROOT).as_posix(), "current_inventory_sha256": INVENTORY_SHA,
         "current_owner_builder": Path(__file__).relative_to(ROOT).as_posix(), "current_owner_builder_sha256": sha(Path(__file__)),
         "exact_source_reviews_sha256": review_hashes, "canonical_source_peer_bindings_sha256": peer_hashes,
         "actual_canonical_execution_records_sha256": actual_execution_hashes, "material22_exact_interface_binding": BINDING.relative_to(ROOT).as_posix(), "material22_exact_interface_binding_sha256": sha(BINDING),
         "new_material_dispositions": {"exact_current_rows": 16, "whole_proved": 16, "nonformal": 0, "whole_pending": 0, "previous_pending_claims_removed": len(removed_pending)},
         "exercise_counts": baseline["counts"]["exercise_statuses"], "material_counts": after,
         "original_tmp_history_manifest": (HERE / "original-tmp-packet-byte-copies-v1.json").relative_to(ROOT).as_posix(), "original_tmp_history_manifest_sha256": sha(HERE / "original-tmp-packet-byte-copies-v1.json"),
         "independent_final_candidate_mapping_peer_pending": True, "coverage_complete": False,
         "scope_notes": ["Every original119 whole exercise and all unrelated material decisions remain exact; only16 separately approved complete literal units replace their own pending clauses, while every earlier proved atom is retained.",
                         "The baseline held21 ledger/helpers/offer remain exact and unmodified; mapped_ledger names a separate versioned future22 candidate for the integrator.",
                         "Four genuine immutable new sources/36 theorems have actual canonical standalone and named exits0. A fresh aggregate22 build, kernel replay and axiom audit remain required.",
                         "UniformContinuity22 TMP history is archived but excluded from this offered proof selection and every material promotion."]}
write_new(DRAFT, draft)
for name, digest in protected.items():
    assert sha(ROOT / name) == digest, name
assert sha(BASE) == BASE_SHA
print(json.dumps({"status": "candidate_and_exact_interface_ready_for_independent_review", "candidate": CANDIDATE.relative_to(ROOT).as_posix(), "candidate_sha256": sha(CANDIDATE), "binding_sha256": sha(BINDING), "draft_offer_sha256": sha(DRAFT), "new_sources": 4, "new_theorems": 36, "new_whole_material_units": 16, "physical_before": before, "physical_after": after}))
