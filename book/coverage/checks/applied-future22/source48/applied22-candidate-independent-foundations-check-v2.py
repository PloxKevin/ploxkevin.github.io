"""Independently bind an isolated candidate to exact original literal decisions."""
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[5]
HERE = Path(__file__).resolve().parent
OUTPUT = HERE / "applied22-candidate-independent-foundations-review-v2.json"
HISTORY = HERE / "applied22-candidate-independent-foundations-original-failure-copies-v2.json"
sys.path.insert(0, str(ROOT / "book/coverage"))
from lean_names import declarations


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


assert not OUTPUT.exists() and not HISTORY.exists()
offer_path = HERE / "applied-audit22-candidate-source48-additions-v1.json"
assert sha(offer_path) == "383923d543b68a8457cb460ccd7b104e659ce6919e7ff6b84005b6b8399a2679"
offer = read(offer_path)
for name in ["mapped_ledger", "mapped_promotions", "candidate_builder", "original_review_bindings", "canonical_path_aliases", "base_selection", "actual_passing_base_aggregate", "inventory"]:
    assert sha(offer[name]) == offer[name + "_sha256"], name
assert offer["inventory_sha256"] == sha("book/coverage/inventory.json") == "2daa285ff1cbc2ad0db045e00e1271b6cb58ce809f5a8328120286748250c108"
inventory = read(offer["inventory"])
units = {row["key"]: row for row in inventory["material_source_units"]}
baseline = read(HERE / "baseline21/applied.json")
old_promotions = read(HERE / "baseline21/applied-promotions.json")
candidate = read(offer["mapped_ledger"])
promotions = read(offer["mapped_promotions"])
binding = read(offer["original_review_bindings"])
aliases = read(offer["canonical_path_aliases"])["aliases"]
assert aliases == binding["canonical_original_path_aliases"]
for original, row in aliases.items():
    assert sha(original) == sha(row["path"]) == row["sha256"]
for row in offer["baseline21_owner_assets"]:
    assert sha(row["original"]) == sha(row["byte_exact_copy"]) == row["sha256"]
assert binding["baseline21_history"] == offer["baseline21_owner_assets"]
assert binding["exact_owned_exercise_records"] == [row for row in inventory["exercises"] if row["source"] in baseline["scope_pages"]]
assert len(binding["exact_owned_exercise_records"]) == 128
assert binding["exact_owned_material_records"] == [row for row in inventory["material_source_units"] if row["source"] in baseline["scope_pages"]]
assert len(binding["exact_owned_material_records"]) == 2059
assert baseline["source_sha256"] == candidate["source_sha256"] == offer["source_sha256"] == binding["source_sha256"]
for name, digest in offer["source_sha256"].items():
    assert sha(name) == digest
assert candidate["exercises"] == baseline["exercises"] and promotions["exercises"] == old_promotions["exercises"]
assert len(candidate["exercises"]) == 128 and candidate["counts"]["exercise_claims"] == baseline["counts"]["exercise_claims"] == 468
assert len(baseline["proof_files"]) == 295
new = offer["proof_files"]
assert len(new) == 3
assert {name: digest for name, digest in candidate["proof_files"].items() if name not in new} == baseline["proof_files"]
for key in baseline:
    if key not in {"generated_at_utc", "material_claims", "proof_files"}:
        assert candidate[key] == baseline[key], key
for key in old_promotions:
    if key != "material":
        assert promotions[key] == old_promotions[key], key
original_reviews = {}
decisions = {}
review_times = {}
expected_hashes = {"16980feb5a01af7baf6955f93760dd47ee8d64721a90160c4d9a79f7ce6539dc", "e6e9e336c1768ae8de5e35da74006b74161e9aa70ae95a81611d1a9d27903467", "ece08993a867c8873f3db9f132571bdfba78990b9b82fb0be758278b6dd88842"}
assert {row["reference"]["sha256"] for row in binding["reviews"]} == expected_hashes
for entry in binding["reviews"]:
    ref = entry["reference"]
    original = read(ref["file"])
    assert sha(ref["file"]) == sha(ref["byte_exact_original_copy"]) == ref["sha256"]
    assert original == entry["exact_original_body"] and "passed" in original["status"]
    assert ref["original_review_time"] == original["reviewed_at_utc"] and ref["reviewer"] == original["reviewer"]
    original_reviews[ref["file"]] = ref["sha256"]
    review_times[ref["file"]] = original["reviewed_at_utc"]
    for row in original["material_units"]:
        key = row["source_unit_key"]
        assert key not in decisions and row["missing_clauses"] == []
        assert row.get("entire_inventory_record", row.get("exact_current48_inventory_record")) == units[key]
        decisions[key] = row
assert len(decisions) == 34 and set(decisions) == set(offer["new_material_keys"])
assert Counter(row["material_status"] for row in decisions.values()) == {"proved": 26, "not_a_formal_claim": 8}
assert len(baseline["material_claims"]) == len(candidate["material_claims"])
changed = {}
for old, current in zip(baseline["material_claims"], candidate["material_claims"]):
    overlap = set(old["source_unit_keys"]) & set(decisions)
    if not overlap:
        assert old == current
        continue
    assert len(overlap) == len(old["source_unit_keys"]) == 1 and old["status"] == "pending"
    key = next(iter(overlap))
    assert key not in changed
    row = decisions[key]
    assert current["status"] == row["material_status"]
    assert current["lean_declarations"] == row["lean_declarations"] and current["hypotheses"] == row["hypotheses"]
    assert current["correspondence"] == row["per_unit_reason"] and current["remaining_gaps"] == []
    for field in old:
        if field not in {"kind", "status", "lean_declarations", "hypotheses", "correspondence", "remaining_gaps", "source_review"}:
            assert current[field] == old[field], (key, field)
    unit = units[key]
    assert current["statement_in_prose"] == unit["source_text"] and current["text_sha256"] == unit["text_sha256"]
    assert current["source_sha256"] == unit["source_sha256"] and current["source"] == unit["source"]
    source_review = current["source_review"]
    assert original_reviews[source_review["file"]] == source_review["sha256"]
    assert review_times[source_review["file"]] == source_review["original_review_time"]
    assert source_review["classification_scope"] == row["per_unit_reason"]
    assert promotions["material"][key]["source_text_sha256"] == unit["text_sha256"]
    assert promotions["material"][key]["claim"] == {field: value for field, value in current.items() if field not in {"source", "source_unit_keys", "source_sha256", "text_sha256"}}
    assert promotions["material"][key]["source_review"] == source_review
    changed[key] = current
assert set(changed) == set(decisions)
for key, value in old_promotions["material"].items():
    if key not in changed:
        assert promotions["material"][key] == value
assert set(promotions["material"]) == set(old_promotions["material"]) | set(changed)
for row in binding["material_rows"]:
    key = row["source_unit_key"]
    assert row["entire_current48_inventory_record"] == units[key]
    assert row["original_complete_reviewed_row"] == decisions[key]
    assert row["normalized_exact_ledger_claim"] == changed[key]
selection = read(offer["base_selection"])
assert len(selection["proof_files"]) == 1089
assert sha(selection["selection"]) == selection["selection_sha256"]
assert read(selection["selection"])["proof_file_count"] == 1089
assert read(offer["actual_passing_base_aggregate"])["status"] == "passed"
names = set()
for name, row in selection["proof_files"].items():
    assert sha(name) == row["sha256"]
    names.update(row["name"] for row in declarations(path(name).read_text()))
exports = []
actual_records = {}
for name, row in new.items():
    assert name not in selection["proof_files"] and name not in baseline["proof_files"]
    assert sha(name) == row["sha256"] == candidate["proof_files"][name]
    public = [entry["name"] for entry in declarations(path(name).read_text()) if entry["kind"] in {"theorem", "lemma"}]
    assert public == row["mapped_named_declarations"] and len(public) == row["theorem_count"]
    exports.extend(public)
    names.update(entry["name"] for entry in declarations(path(name).read_text()))
    for field in ["standalone_evidence", "named_evidence"]:
        record_path = row[field]
        record = read(record_path)
        assert sha(record_path) == row[field + "_sha256"]
        assert record["exit_code"] == 0 and record["source"] == name
        assert record["source_sha256_before"] == record["source_sha256_after"] == row["sha256"]
        assert sha(record["log"]) == record["log_sha256"]
        for field in ["source_snapshot", "preserved_source"]:
            if field in record:
                assert sha(record[field]) == row["sha256"]
        actual_records[record_path] = sha(record_path)
    for evidence_path, digest in row["evidence_sha256"].items():
        assert sha(evidence_path) == digest
assert len(exports) == 16 and len(actual_records) == 6
assert all(set(row["lean_declarations"]) <= names for row in decisions.values())
for row in offer["new_actual_paired_records"]:
    assert row["sha256"] == actual_records[row["file"]] and row["actual_original_record"] == read(row["file"])
builder_record_path = HERE / "candidate-builder-actual-execution-v3.json"
builder_record = read(builder_record_path)
assert builder_record["actual_exit_code"] == 0 and builder_record["helper_sha256"] == offer["candidate_builder_sha256"]
assert builder_record["actual_reported_output"]["offer_sha256"] == sha(offer_path)
supplement_path = HERE / "candidate-builder-failure-and-execution-byte-copies-supplement-v1.json"
assert sha(supplement_path) == "2721da8353e23ea431293fe82366d72566d55f15bbbfc2d0899c64f2ed157a25"
supplement = read(supplement_path)
assert supplement["unchanged_candidate_offer"]["sha256"] == sha(offer_path)
for original, row in supplement["aliases"].items():
    assert sha(original) == sha(row["path"]) == row["sha256"]
copies = []
own_history_dir = HERE / "independent-foundations-original-failures"
own_history_dir.mkdir(exist_ok=True)
for field in ["preserved_initial_builder_failure", "preserved_second_builder_failure"]:
    row = binding[field]
    failure = read(row["file"])
    assert sha(row["file"]) == row["sha256"] and failure["actual_exit_code"] != 0
    assert sha(row["helper_copy"]) == row["helper_sha256"]
    originals = [row["file"], row["helper_copy"]]
    if "preserved_reported_failure_summary" in failure:
        originals.append(failure["preserved_reported_failure_summary"])
    for original in originals:
        destination = own_history_dir / path(original).name
        assert not destination.exists()
        with destination.open("xb") as output:
            output.write(path(original).read_bytes())
        assert sha(original) == sha(destination)
        copies.append({"original": original, "byte_exact_copy": rel(destination), "sha256": sha(destination)})
write_new(HISTORY, {"status": "both_actual_prior_builder_failure_records_helpers_and_reported_summary_byte_preserved", "copied_at_utc": datetime.now(timezone.utc).isoformat(), "copies": copies, "scope": "Exact original failure records and the honestly labeled reported failure summary are archived without synthesizing any missing raw PTY transcript or process timing."})
for row in offer["baseline21_owner_assets"]:
    assert sha(row["original"]) == row["sha256"]
write_new(OUTPUT, {
    "status": "independent_exact_source48_applied22_isolated_candidate_mechanics_review_passed",
    "reviewer": "/root/config21_next", "reviewed_at_utc": datetime.now(timezone.utc).isoformat(),
    "checker": rel(Path(__file__)), "checker_sha256": sha(Path(__file__)),
    "offer": rel(offer_path), "offer_sha256": sha(offer_path), "candidate_ledger": offer["mapped_ledger"], "candidate_ledger_sha256": offer["mapped_ledger_sha256"],
    "candidate_promotions": offer["mapped_promotions"], "candidate_promotions_sha256": offer["mapped_promotions_sha256"],
    "exact_original_review_binding": offer["original_review_bindings"], "exact_original_review_binding_sha256": offer["original_review_bindings_sha256"],
    "inventory_sha256": offer["inventory_sha256"], "original_review_times_preserved": review_times,
    "actual_builder_record": rel(builder_record_path), "actual_builder_record_sha256": sha(builder_record_path),
    "owner_builder_failure_and_execution_supplement": rel(supplement_path), "owner_builder_failure_and_execution_supplement_sha256": sha(supplement_path),
    "original_failed_builder_history": rel(HISTORY), "original_failed_builder_history_sha256": sha(HISTORY),
    "actual_zero_paired_records_sha256": actual_records, "canonical_original_path_aliases_sha256": offer["canonical_path_aliases_sha256"],
    "checks": {"all128_whole_exercises_and468_claim_bodies_exact": True, "all295_prior_proof_rows_exact": True,
               "exact34_pending_literals_only_changed_26proved_8nonformal": True, "original_complete_decisions_hypotheses_and_declarations_exact": True,
               "all_other_material_and_promotion_rows_exact": True, "all2059_physical_and128_exercise_inventory_records_exact": True,
               "three_genuine_sources16_theorems_six_actual_zero_records": True, "all1089_selected21_source_hashes_exact": True,
               "original_three_peer_bodies_and_review_times_exact": True, "actual_failed_builder_history_archived_exact": True},
    "preserved_original_failed_reader": rel(HERE / "applied22-candidate-independent-foundations-execution-v1.json"),
    "preserved_original_failed_reader_sha256": sha(HERE / "applied22-candidate-independent-foundations-execution-v1.json"),
    "original_reader_correction": "V1 used the selection count field on a freeze manifest. V2 checks the actual1089 manifest proof map and its exact referenced selection/count instead. No owner artifact or earlier decision changed.",
    "coverage_complete": False, "errors": [],
    "scope": "Independent candidate mapping mechanics only, bound to the original three complete-literal semantic decisions and real immutable proof pairs. No live owner ledger integration or fresh aggregate22 execution is asserted."
})
print(json.dumps({"status": "passed", "review": rel(OUTPUT), "review_sha256": sha(OUTPUT), "original_failure_history_sha256": sha(HISTORY)}))
