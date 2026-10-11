"""Build a new immutable v2 candidate adding the complete uniformity literal."""
from collections import Counter
from datetime import datetime, timezone
import copy
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
HERE = ROOT / "book/coverage/checks/foundations-future22"
EXT = HERE / "uniform-continuity-extension"
OLD_CANDIDATE = HERE / "foundations-source48-candidate-ledger22-v1.json"
OLD_BINDING = HERE / "foundations-source48-material22-interface-binding-v1.json"
OLD_OFFER = ROOT / "book/coverage/foundations-audit22-source48-additions-v1.json"
CANDIDATE = HERE / "foundations-source48-candidate-ledger22-v2.json"
BINDING = HERE / "foundations-source48-material22-interface-binding-v2.json"
DRAFT = HERE / "foundations-source48-integration-offer22-draft-v2.json"
INTEGRITY = HERE / "foundations-source48-v1-held-and-uniform-v2-extension-integrity-v1.json"
PEER = EXT / "basics1167-independent-applied-complete-literal-review22-v1.json"
SOURCE = ROOT / "verification/lean/SafeLearning/CompleteFoundationsUniformContinuity22.lean"
SOURCE_SHA = "ca8ba22fe9cb9287de6cb9fc8e6f2edf797908be0deb7acd00aacc5586bef31a"
sys.path.insert(0, str(ROOT / "book/coverage"))
from lean_names import declarations


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_text())


def rel(path):
    return path.relative_to(ROOT).as_posix()


def write_new(path, data):
    with path.open("x") as output:
        output.write(json.dumps(data, ensure_ascii=False, indent=2) + "\n")


def physical(ledger):
    statuses = {}
    for row in ledger["material_claims"]:
        for key in row["source_unit_keys"]:
            statuses.setdefault(key, set()).add(row["status"])
    result = Counter("pending" if "pending" in values else "not_a_formal_claim" if values == {"not_a_formal_claim"} else "proved" for values in statuses.values())
    return {"total": len(statuses), "whole_proved": result["proved"], "nonformal": result["not_a_formal_claim"], "whole_pending": result["pending"]}


assert not any(path.exists() for path in [CANDIDATE, BINDING, DRAFT, INTEGRITY])
assert sha(OLD_CANDIDATE) == "cba5b6308dc33346cb3e86dc7fc3c5e2f43773ec95b55d0c4a0b42bdd0cb4cbb"
assert sha(OLD_BINDING) == "7a0729299f3545ced42662c820681c01fc95a11ef3a9343955f937767bdde31c"
assert sha(OLD_OFFER) == "bf8432b89badbd44e5f3998470f26af3f3bb07ee88fe68853ceb6184e5eb1662"
assert sha(PEER) == "f926443ed435f3d07a06d20b40724806b3251ef7bfdb7e306ceec83c24fc4331"
old = read(OLD_CANDIDATE)
old_binding = read(OLD_BINDING)
old_offer = read(OLD_OFFER)
peer = read(PEER)
assert peer["status"] == "independent_complete_uniform_continuity_literal_review_passed" and peer["errors"] == []
assert peer["protected21"]["all_exact"] and peer["protected21"]["unchanged_four_source_candidate_sha256"] == sha(OLD_CANDIDATE)
assert len(peer["material_units"]) == 1
row = peer["material_units"][0]
key = row["source_unit_key"]
assert key == "primer-basics.html::node-1167" and row["material_status"] == "proved" and row["whole_unit_approved"] and row["missing_clauses"] == []
inventory_path = ROOT / old_offer["current_inventory"]
assert sha(inventory_path) == sha(ROOT / "book/coverage/inventory.json") == old_offer["current_inventory_sha256"] == peer["inventory_sha256"]
unit = next(unit for unit in read(inventory_path)["material_source_units"] if unit["key"] == key)
assert unit == row["entire_inventory_record"] and sha(ROOT / unit["source"]) == unit["source_sha256"]
assert sha(SOURCE) == SOURCE_SHA == peer["proof_source_sha256"][rel(SOURCE)]
assert sha(EXT / "CompleteFoundationsUniformContinuity22-source-v1.lean") == SOURCE_SHA
public = [entry["name"] for entry in declarations(SOURCE.read_text()) if entry["kind"] in {"theorem", "lemma"}]
assert len(public) == 9 and row["lean_declarations"] == public
actual_records = {}
for reference in peer["actual_canonical_execution_records"]:
    record_path = ROOT / reference["file"]
    assert sha(record_path) == reference["sha256"] and read(record_path) == reference["record"]
    record = reference["record"]
    assert record["exit_code"] == 0 and record["source_sha256_before"] == record["source_sha256_after"] == SOURCE_SHA
    assert sha(ROOT / record["log"]) == record["log_sha256"]
    assert sha(ROOT / record["preserved_source"]) == SOURCE_SHA
    actual_records[rel(record_path)] = sha(record_path)
assert len(actual_records) == 2
for name, proof in old_offer["proof_files"].items():
    assert sha(ROOT / name) == proof["sha256"]
    for record_name, digest in proof["evidence_sha256"].items():
        assert sha(ROOT / record_name) == digest
        record = read(ROOT / record_name)
        assert record["exit_code"] == 0 and sha(ROOT / record["log"]) == record["log_sha256"]
assert sha(ROOT / old_offer["held21_ledger"]) == old_offer["held21_ledger_sha256"]
selection = read(ROOT / old_offer["base_selection"])
protected = {name: source["sha256"] for name, source in selection["proof_files"].items()}
assert len(protected) == selection["proof_file_count"] == 1089
protected.update(read(HERE / "original-tmp/foundations-future22-tmp-proof-index-v1.json")["held_checkpoint21_assets_exact"])
protected.update(old["source_sha256"])
protected[rel(OLD_OFFER)] = sha(OLD_OFFER)
protected.update({rel(path): sha(path) for path in HERE.rglob("*") if path.is_file()})
for name, digest in protected.items():
    assert sha(ROOT / name) == digest, name
checker = Path(peer["independent_checker"])
assert sha(checker) == peer["independent_checker_sha256"]
checker_copy = EXT / "peer-checkers" / checker.name
checker_copy.parent.mkdir(exist_ok=True)
assert not checker_copy.exists()
with checker_copy.open("xb") as output:
    output.write(checker.read_bytes())
assert sha(checker_copy) == peer["independent_checker_sha256"]
candidate = copy.deepcopy(old)
old_claims = [claim for claim in old["material_claims"] if key in claim["source_unit_keys"]]
removed = [claim for claim in old_claims if claim["status"] == "pending"]
assert len(removed) == 1 and removed[0]["source_unit_keys"] == [key]
candidate["material_claims"] = [copy.deepcopy(claim) for claim in old["material_claims"] if claim not in removed]
claim = {"id": key + "::reviewed22-whole-literal", "source_unit_keys": [key], "source": unit["source"], "locator": unit["locator"],
         "source_text": unit["source_text"], "source_text_sha256": unit["text_sha256"], "source_sha256": unit["source_sha256"],
         "statement_in_prose": unit["source_text"], "kind": "independently_reviewed_complete_mathematical_literal", "status": "proved",
         "lean_declarations": row["lean_declarations"], "hypotheses": row["hypotheses"], "correspondence": row["per_unit_reason"], "remaining_gaps": [],
         "source_review": {"file": rel(PEER), "sha256": sha(PEER), "reviewed_at_utc": peer["reviewed_at_utc"], "reviewer": peer["reviewer"]}}
candidate["material_claims"].append(claim)
assert candidate["exercises"] == old["exercises"] and candidate["surrounding_prose_reviews"] == old["surrounding_prose_reviews"]
assert [claim for claim in candidate["material_claims"] if key not in claim["source_unit_keys"]] == [claim for claim in old["material_claims"] if key not in claim["source_unit_keys"]]
assert all(claim in candidate["material_claims"] for claim in old_claims if claim["status"] != "pending")
candidate["proof_files"] = sorted(old["proof_files"] + [rel(SOURCE)])
assert rel(SOURCE) not in old["proof_files"] and rel(SOURCE) not in selection["proof_files"]
candidate["proof_sha256"][rel(SOURCE)] = SOURCE_SHA
candidate["counts"]["material_claim_statuses"] = dict(Counter(claim["status"] for claim in candidate["material_claims"]))
before = physical(old)
after = physical(candidate)
assert before == {"total": 1756, "whole_proved": 747, "nonformal": 524, "whole_pending": 485}
assert after == {"total": 1756, "whole_proved": 748, "nonformal": 524, "whole_pending": 484}
candidate["original_current22_four_source_mapping_v1"] = copy.deepcopy(old["current22_material_mapping"])
candidate["current22_material_mapping"].update({"interface_binding": rel(BINDING), "individually_whole_approved_material_units": 17,
    "removed_prior_pending_claims": old["current22_material_mapping"]["removed_prior_pending_claims"] + 1, "physical_after": after,
    "scope": "Separate versioned combined future22 candidate; prior four-source candidate remains byte-exact and only one additional complete literal replaces its own pending clause."})
candidate["limits"].append("V2 adds the one independently complete uniform-continuity paragraph with a ninth-theorem immutable source and actual standalone/named execution pair. Prior four-source candidate and every earlier semantic review/time remain exact.")
write_new(CANDIDATE, candidate)
new_packet = {"module": SOURCE.stem, "source": rel(SOURCE), "source_sha256": SOURCE_SHA, "whole_literal_units": 1, "new_public_theorems": 9,
              "actual_execution_records_sha256": actual_records, "original_review_sha256": sha(PEER), "canonical_final_peer_sha256": sha(PEER)}
binding = copy.deepcopy(old_binding)
binding.update({"status": "exact_source48_prior_four_source_mapping_and_fresh_uniform_complete_literal_bound_to_new_v2_candidate", "prepared_at_utc": datetime.now(timezone.utc).isoformat(),
    "candidate_ledger": rel(CANDIDATE), "candidate_ledger_sha256": sha(CANDIDATE), "physical_after": after,
    "prior_v1_candidate": rel(OLD_CANDIDATE), "prior_v1_candidate_sha256": sha(OLD_CANDIDATE),
    "prior_v1_interface": rel(OLD_BINDING), "prior_v1_interface_sha256": sha(OLD_BINDING), "prior_v1_final_offer": rel(OLD_OFFER), "prior_v1_final_offer_sha256": sha(OLD_OFFER)})
binding["material_units"].append({"source_unit_key": key, "exact_current48_inventory_record": unit, "original_unit_row": row,
    "original_review": rel(PEER), "original_review_sha256": sha(PEER), "original_reviewed_at_utc": peer["reviewed_at_utc"],
    "canonical_peer": rel(PEER), "canonical_peer_sha256": sha(PEER), "original_current21_claims": old_claims,
    "retained_original_proved_or_nonformal_claims": [claim for claim in old_claims if claim["status"] != "pending"],
    "removed_pending_clauses": removed, "new_candidate_claim": claim})
binding["proof_packets"].append(new_packet)
assert binding["material_units"][:-1] == old_binding["material_units"] and binding["proof_packets"][:-1] == old_binding["proof_packets"]
write_new(BINDING, binding)
draft = copy.deepcopy(old_offer)
for field in ["original_reviewed_draft", "independent_final_candidate_mapping_peer", "independent_final_candidate_mapping_peer_actual_execution", "actual_builder_record", "finalization_helper"]:
    if field in draft:
        draft["prior_v1_" + field] = draft.pop(field)
        draft["prior_v1_" + field + "_sha256"] = draft.pop(field + "_sha256")
draft.update({"status": "draft_actual_zero_source48_foundation22_v2_uniform_extension_requires_independent_delta_mapping_review",
    "prepared_at_utc": datetime.now(timezone.utc).isoformat(), "prior_v1_final_offer": rel(OLD_OFFER), "prior_v1_final_offer_sha256": sha(OLD_OFFER),
    "mapped_ledger": rel(CANDIDATE), "mapped_ledger_sha256": sha(CANDIDATE), "current_owner_builder": rel(Path(__file__)), "current_owner_builder_sha256": sha(Path(__file__)),
    "new_proof_file_count": 5, "new_theorem_or_lemma_count": 45, "material22_exact_interface_binding": rel(BINDING), "material22_exact_interface_binding_sha256": sha(BINDING),
    "new_material_dispositions": {"exact_current_rows": 17, "whole_proved": 17, "nonformal": 0, "whole_pending": 0, "previous_pending_claims_removed": 19},
    "material_counts": after, "independent_final_candidate_mapping_peer_pending": True, "independent_final_loader_mapping_peer_pending": True,
    "uniform_extension_complete_literal_peer": rel(PEER), "uniform_extension_complete_literal_peer_sha256": sha(PEER),
    "uniform_complete_literal_peer_checker_copy": rel(checker_copy), "uniform_complete_literal_peer_checker_copy_sha256": sha(checker_copy),
    "scope": "Five genuine future22 proof additions/45 exports and seventeen complete source48 material units; exactly one whole uniform-continuity literal extends the independently approved prior four-source candidate.",
    "coverage_complete": False})
draft.pop("finalized_at_utc")
draft["proof_files"][rel(SOURCE)] = {"sha256": SOURCE_SHA, "evidence_sha256": actual_records, "evidence_scope": "Actual unchanged canonical standalone and named target builds exit0; full fresh independent complete-literal review passed. No aggregate22 execution is inferred."}
draft["new_proof_sources_for_checkpoint22"] = sorted(draft["proof_files"])
draft["exact_source_reviews_sha256"][rel(PEER)] = sha(PEER)
draft["canonical_source_peer_bindings_sha256"][rel(PEER)] = sha(PEER)
draft["actual_canonical_execution_records_sha256"].update(actual_records)
draft["scope_notes"] = [note for note in draft["scope_notes"] if "UniformContinuity22 TMP history" not in note]
draft["scope_notes"].append("The exact prior four-source offer/candidate, all sixteen original complete decisions and times, and every genuine proof/trial/checker record remain historical and byte-exact. This V2 packet adds only node1167 with its fresh full-literal peer and two genuine canonical executions.")
write_new(DRAFT, draft)
for name, digest in protected.items():
    assert sha(ROOT / name) == digest, name
write_new(INTEGRITY, {"status": "passed_all_existing_foundation22_v1_and_selected21_assets_exact_after_new_uniform_v2_candidate", "checked_at_utc": datetime.now(timezone.utc).isoformat(),
    "protected_sha256": protected, "new_candidate_sha256": sha(CANDIDATE), "new_interface_sha256": sha(BINDING), "new_draft_sha256": sha(DRAFT),
    "all119_whole_exercises_and_all16_prior_complete_literals_exact": True, "exactly_one_additional_whole_literal": key, "new_source_count": 1, "new_theorem_count": 9,
    "physical_before_v1": before, "physical_after_v2": after, "coverage_complete": False})
print(json.dumps({"status": "new_v2_candidate_and_exact_one_unit_delta_ready_for_independent_review", "candidate": rel(CANDIDATE), "candidate_sha256": sha(CANDIDATE), "binding_sha256": sha(BINDING), "draft_sha256": sha(DRAFT), "integrity_sha256": sha(INTEGRITY), "combined_new_sources": 5, "combined_new_exports": 45, "combined_whole_material_units": 17, "physical_after": after}))
