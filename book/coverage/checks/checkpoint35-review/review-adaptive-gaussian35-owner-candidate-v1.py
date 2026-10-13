#!/usr/bin/env python3
"""Independently replay checkpoint35 owner changes without editing their inputs."""
from collections import Counter, defaultdict
from datetime import datetime, timezone
from pathlib import Path
import copy
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[4]
OUT = Path(__file__).resolve().parent
BINDING = "book/coverage/checks/checkpoint35-ledgers/owner-candidate-binding-v1.json"
BINDING_SHA = "0f9e6484bf38f7f722ef69943edbe5e86201ba5703d51b3dd27822ba2a18ed52"
GAUSSIAN = "book/coverage/checks/checkpoint35-review/adaptive-gaussian35-proposed-exact-mapping-v1.json"
DIAGONAL = "book/coverage/checks/checkpoint35-review/diagonal35-exact-material-mapping-proposal-v1.json"
SOURCE_REVIEW = "book/coverage/checks/checkpoint35-review/adaptive-gaussian35-independent-source-review-v1.json"
FIELDS = ["status", "lean_declarations", "hypotheses", "correspondence", "remaining_gaps"]


def ref(name):
    return {"file": name, "sha256": hashlib.sha256((ROOT / name).read_bytes()).hexdigest()}


def read(name):
    return json.loads((ROOT / name).read_text())


def exact(row):
    assert ref(row["file"])["sha256"] == row["sha256"], "Changed referenced input: " + row["file"]
    if "bytes" in row:
        assert (ROOT / row["file"]).stat().st_size == row["bytes"], row["file"]
    return read(row["file"]) if row["file"].endswith(".json") else None


def locate(document, pointer):
    parent = document
    for part in pointer[:-1]:
        parent = parent[part]
    return parent, pointer[-1]


def forward(original, patches):
    value = copy.deepcopy(original)
    for patch in patches:
        parent, key = locate(value, patch["pointer"])
        exists = key < len(parent) if isinstance(parent, list) else key in parent
        assert exists == patch["before_exists"], patch["pointer"]
        assert (parent[key] if exists else None) == patch["before"], patch["pointer"]
        if isinstance(parent, list) and not exists:
            assert key == len(parent), patch["pointer"]
            parent.append(copy.deepcopy(patch["after"]))
        else:
            parent[key] = copy.deepcopy(patch["after"])
    return value


def inverse(candidate, patches):
    value = copy.deepcopy(candidate)
    for patch in reversed(patches):
        parent, key = locate(value, patch["pointer"])
        assert parent[key] == patch["after"], patch["pointer"]
        if patch["before_exists"]:
            parent[key] = copy.deepcopy(patch["before"])
        elif isinstance(parent, list):
            assert key == len(parent) - 1, patch["pointer"]
            parent.pop()
        else:
            del parent[key]
    return value


def global_counts(owners):
    exercises = Counter()
    statuses = defaultdict(list)
    for owner in owners.values():
        exercises.update(e["status"] for e in owner["exercises"])
        for claim in owner["material_claims"] + [c for e in owner["exercises"] for c in e["claims"]]:
            for key in claim.get("source_unit_keys", []):
                statuses[key].append(claim["status"])
        for key in owner.get("pending_source_units", []):
            if isinstance(key, dict):
                key = key.get("key", key.get("inventory_key"))
            statuses[key].append("pending")
    materials = Counter("pending" if "pending" in values else "reviewed" for values in statuses.values())
    return dict(exercises), dict(materials)


def main():
    assert ref(BINDING)["sha256"] == BINDING_SHA
    binding = read(BINDING)
    inventory = exact(binding["inventory"])
    units = {row["key"]: row for row in inventory["material_source_units"]}
    exercise_units = {row["key"]: row for row in inventory["exercises"]}
    source_review = exact(ref(SOURCE_REVIEW))
    assert source_review["status"] == "approved" and source_review["errors"] == []
    for row in source_review["proof_sources"] + source_review["source_sources"]:
        exact(row)
    proposals = {}
    for row in binding["mapping_proposals"]:
        document = exact(row)
        assert document["status"].startswith("approved") and document["errors"] == []
        assert document["inventory"]["sha256"] == binding["inventory"]["sha256"]
        exact(document["independent_source_review"])
        for source in document["proof_sources"]:
            exact(source)
        proposals[row["file"]] = document
    assert set(proposals) == {GAUSSIAN, DIAGONAL}
    assert proposals[GAUSSIAN]["independent_source_review"]["sha256"] == ref(SOURCE_REVIEW)["sha256"]
    gaussian = proposals[GAUSSIAN]
    assert gaussian["declaration_count"] == 7
    assert gaussian["whole_exercise"]["original_pending_claim_ids"] == [
        "safe-bo-theory.html#book-m5-b2::requirement-1",
        "safe-bo-theory.html#book-m5-b2::requirement-2",
        "safe-bo-theory.html#book-m5-b2::requirement-3",
    ]
    for name, fingerprint in binding["protected_input_sha256"].items():
        assert ref(name)["sha256"] == fingerprint, name
    for name, fingerprint in inventory["source_sha256"].items():
        assert ref(name)["sha256"] == fingerprint, name

    originals, candidates, expected, replacement_rows = {}, {}, {}, {}
    hardlink_checks = []
    patch_counts = {}
    for replacement in binding["replacements"]:
        domain = Path(replacement["destination"]).stem
        assert domain in {"modules", "core"}
        original = exact(replacement["preserved_original"])
        candidate = exact(replacement["candidate"])
        reverse = exact(replacement["exact_inverse"])
        assert replacement["before"]["sha256"] == replacement["preserved_original"]["sha256"]
        assert ref(replacement["destination"]) == replacement["before"]
        assert reverse["baseline"] == replacement["before"]
        assert reverse["candidate"] == replacement["candidate"]
        assert reverse["preserved_original"] == replacement["preserved_original"]
        old_stat = (ROOT / replacement["preserved_original"]["file"]).stat()
        live_stat = (ROOT / replacement["destination"]).stat()
        assert old_stat.st_ino == live_stat.st_ino and old_stat.st_dev == live_stat.st_dev
        assert old_stat.st_nlink >= 2
        hardlink_checks.append({
            "destination": replacement["destination"],
            "original": replacement["preserved_original"],
            "same_native_device_and_inode_before_installation": True,
            "original_link_count": old_stat.st_nlink,
        })
        assert forward(original, reverse["patches"]) == candidate
        assert inverse(candidate, reverse["patches"]) == original
        originals[domain], candidates[domain] = original, candidate
        expected[domain] = copy.deepcopy(original)
        replacement_rows[domain] = replacement
        patch_counts[domain] = len(reverse["patches"])
    assert patch_counts == {"modules": 38, "core": 13}
    for domain in ("foundations", "applied"):
        originals[domain] = read("book/coverage/" + domain + ".json")
        candidates[domain] = originals[domain]
    assert global_counts(originals) == (
        {"complete_math": 538, "pending": 11, "partial": 7},
        {"reviewed": 4858, "pending": 7916},
    )

    material_changes = []
    refreshes = []
    material_details = []
    for proposal_name, proposal in proposals.items():
        for mapping in proposal["material_mappings"]:
            key = mapping["material_unit_key"]
            unit = units[key]
            assert mapping["source"] == unit["source"]
            assert mapping["source_sha256"] == unit["source_sha256"]
            assert mapping.get("exact_text_sha256", mapping.get("text_sha256")) == unit["text_sha256"]
            assert hashlib.sha256(unit["source_text"].encode()).hexdigest() == unit["text_sha256"]
            domain = mapping.get("owner", "modules")
            matched = [
                (index, row) for index, row in enumerate(originals[domain]["material_claims"])
                if row.get("source_unit_keys") == [key]
                and row["id"].endswith(("::claim-review", "::semantic-review"))
            ]
            assert len(matched) == 1, key
            index, before = matched[0]
            assert before["statement_in_prose"] == unit["source_text"], key
            assert candidates[domain]["material_claims"][index]["source_unit_keys"] == [key]
            if "claim_id" in mapping:
                assert before["id"] == mapping["claim_id"]
            after = copy.deepcopy(before)
            for field in FIELDS:
                after[field] = copy.deepcopy(mapping[field])
            after["independent_source_review35"] = proposal["independent_source_review"]
            after["exact_source90_mapping_proposal35"] = ref(proposal_name)
            after["exact_source90_text_sha256"] = unit["text_sha256"]
            assert after == candidates[domain]["material_claims"][index], key
            assert after["status"] != "pending" and after["remaining_gaps"] == []
            expected[domain]["material_claims"][index] = after
            (material_changes if before["status"] == "pending" else refreshes).append(key)
            material_details.append({
                "owner": domain, "material_unit_key": key,
                "before_status": before["status"], "after_status": after["status"],
                "text_sha256": unit["text_sha256"],
                "proposal": ref(proposal_name),
            })
    assert len(material_details) == 23 and len(set(row["material_unit_key"] for row in material_details)) == 23
    assert material_changes == binding["changed_whole_material_units"]
    assert refreshes == binding["refreshed_material_units"]
    assert len(material_changes) == 20 and len(refreshes) == 3
    assert len(proposals[GAUSSIAN]["material_mappings"]) == 7
    assert len(proposals[DIAGONAL]["material_mappings"]) == 16

    whole = gaussian["whole_exercise"]
    exercise_key = whole["inventory_key"]
    assert exercise_key == "safe-bo-theory.html#book-m5-b2"
    index = next(i for i, row in enumerate(originals["modules"]["exercises"]) if row["inventory_key"] == exercise_key)
    before = originals["modules"]["exercises"][index]
    after = copy.deepcopy(before)
    assert before["status"] == "partial" and len(before["claims"]) == 4
    assert whole["exact_text_sha256"] == exercise_units[exercise_key]["text_sha256"]
    assert whole["source_sha256"] == exercise_units[exercise_key]["source_sha256"]
    assert whole["status"] == "complete_math" and whole["remaining_gaps"] == []
    assert len(whole["solution_clauses"]) == 6
    assert set(whole["original_pending_claim_ids"]) == {row["id"] for row in before["claims"] if row["status"] == "pending"}
    for mapping in gaussian["exercise_claim_mappings"]:
        claim_index = next(i for i, row in enumerate(before["claims"]) if row["id"] == mapping["claim_id"])
        old_claim = before["claims"][claim_index]
        assert mapping["statement_in_prose"] == old_claim["statement_in_prose"]
        assert mapping["exact_text_sha256"] == hashlib.sha256(old_claim["statement_in_prose"].encode()).hexdigest()
        if old_claim["status"] == "proved":
            assert old_claim["lean_declarations"] == [
                "SafeLearning.CompleteModulesTheory.finite_failure_union",
                "SafeLearning.CompleteModulesTheory.simultaneous_success",
            ]
            assert set(old_claim["lean_declarations"]) <= set(mapping["lean_declarations"])
            assert old_claim["remaining_gaps"] and mapping["remaining_gaps"] == []
        claim = copy.deepcopy(old_claim)
        for field in FIELDS:
            claim[field] = copy.deepcopy(mapping[field])
        claim["independent_source_review35"] = gaussian["independent_source_review"]
        claim["exact_source90_mapping_proposal35"] = ref(GAUSSIAN)
        after["claims"][claim_index] = claim
    after["status"] = "complete_math"
    after["independent_whole_exercise_review35"] = {
        "source_review": gaussian["independent_source_review"],
        "exact_mapping": ref(GAUSSIAN),
        "text_sha256": whole["exact_text_sha256"],
        "all_prompt_hint_and_solution_clauses_reviewed": True,
    }
    assert after == candidates["modules"]["exercises"][index]
    assert all(row["status"] == "proved" and row["remaining_gaps"] == [] for row in after["claims"])
    expected["modules"]["exercises"][index] = after

    plan_file = "book/coverage/checks/checkpoint35-root/compiled-reviewed-additions-plan-v1.json"
    plan = read(plan_file)
    new_declarations = []
    new_sources = []
    for row in plan["sources"]:
        source = row["source"]
        exact(source)
        name = source["file"]
        new_sources.append(source)
        assert name not in originals["modules"]["proof_files"]
        expected["modules"]["proof_files"][name] = source["sha256"]
        if "Diagonal" in name:
            assert name not in originals["core"]["proof_files"]
            expected["core"]["proof_files"][name] = source["sha256"]
        text = (ROOT / name).read_text()
        namespace = re.search(r"^namespace\s+(\S+)", text, re.M).group(1)
        for kind, bare in re.findall(r"^(theorem|lemma)\s+(\w+)", text, re.M):
            new_declarations.append({"name": namespace + "." + bare, "kind": kind, "file": name})
    assert len(new_sources) == 3 and len(new_declarations) == 13
    assert [row["name"] for row in new_declarations if "AdaptiveGaussian" in row["file"]] == gaussian["declarations"]
    assert len({row["name"] for row in new_declarations}) == 13
    expected["modules"]["declarations"].extend(new_declarations)
    assert expected["modules"]["declarations"] == candidates["modules"]["declarations"]
    assert len(candidates["modules"]["declarations"]) - len(originals["modules"]["declarations"]) == 13
    for domain in ("modules", "core"):
        expected[domain]["current_checkpoint35_identity"] = {
            "status": "prepared_exact_Source90_reviewed_owner_candidate",
            "baseline_owner": replacement_rows[domain]["before"],
            "inventory": binding["inventory"],
            "mapping_proposals": binding["mapping_proposals"],
            "unchanged_site_sources": True,
            "coverage_complete": False,
        }
        counts = copy.deepcopy(originals[domain]["counts"])
        if domain == "modules":
            counts["exercise_status"] = dict(Counter(row["status"] for row in expected[domain]["exercises"]))
            counts["exercise_claim_status"] = dict(Counter(row["status"] for exercise in expected[domain]["exercises"] for row in exercise["claims"]))
            counts["material_claim_status"] = dict(Counter(row["status"] for row in expected[domain]["material_claims"]))
            counts["new_declarations"] = len(expected[domain]["declarations"])
        else:
            counts["exercise_statuses"] = dict(Counter(row["status"] for row in expected[domain]["exercises"]))
            counts["proof_files"] = len(expected[domain]["proof_files"])
        expected[domain]["counts"] = counts
        assert expected[domain] == candidates[domain], "Extra/unapproved semantic mutation in " + domain
    assert global_counts(candidates) == (
        {"complete_math": 539, "pending": 11, "partial": 6},
        {"reviewed": 4878, "pending": 7896},
    )
    assert binding["exercise_counts"] == global_counts(candidates)[0]
    assert binding["material_counts"] == global_counts(candidates)[1]
    assert binding["whole_material_units_completed"] == 20 and binding["refreshed_existing_material_units"] == 3
    assert binding["closed_exercises"] == [exercise_key] and binding["exercises_completed"] == 1
    assert binding["historical_evidence_rewritten"] == 0
    assert binding["coverage_complete"] is False and binding["owner_installation_claimed"] is False
    return {
        "schema_version": 1,
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "status": "approved_exact_gaussian35_owner_installation_scope",
        "reviewer": "/root/review_gaussian35",
        "binding": ref(BINDING),
        "errors": [],
        "approved_mapping_proposals": [GAUSSIAN],
        "source_review": ref(SOURCE_REVIEW),
        "source_refs": source_review["source_sources"],
        "gaussian_proof_ref": source_review["proof_sources"][0],
        "inventory": binding["inventory"],
        "candidate_inverse_and_preserved_original_refs": binding["replacements"],
        "native_original_preservation_checks": hardlink_checks,
        "independent_semantic_forward_and_inverse_replay": {"passed": True, "patch_counts": patch_counts},
        "full_candidate_reconstructed_only_from_approved_changes": True,
        "material_rows_changed": 23,
        "new_whole_material_units": 20,
        "refreshed_existing_material_units": 3,
        "gaussian_new_whole_units": 7,
        "diagonal_new_whole_units": 13,
        "material_row_details": material_details,
        "new_proof_sources": new_sources,
        "new_theorem_records": 13,
        "new_gaussian_theorem_records": 7,
        "b2_exact_source_text_sha256": whole["exact_text_sha256"],
        "b2_three_pending_requirements_now_proved": True,
        "b2_original_two_proved_union_declarations_retained": True,
        "b2_historical_gaps_closed_only_by_exact_approved_mapping": True,
        "b2_prompt_hint_and_complete_six_sentence_solution_reviewed": True,
        "unrelated_exercises_or_broad_parent_rows_mutated": False,
        "candidate_exercise_counts": binding["exercise_counts"],
        "candidate_material_counts": binding["material_counts"],
        "protected_input_hashes_checked": len(binding["protected_input_sha256"]),
        "inventory_native_source_hashes_checked": len(inventory["source_sha256"]),
        "scope": "Approves the exact Gaussian mapping proposal and its installation in the hash-bound owner candidates. Diagonal changes were checked for exact confinement to their separate approved proposal; mathematical approval of that proposal is the diagonal peer's responsibility. No compiler rerun, source edit, owner installation, complete coverage or publication success is claimed.",
        "numeric_scope_preserved": "Safety retains the exact E and radius expressions. The six-decimal values remain approximations; the candidate copies the approved hypotheses/correspondences without broadening them.",
        "original_history_scope": "The candidate retains original row kinds and source/history metadata; only the approved mapping fields and exact review references change. Native original ledgers are preserved as hard links before atomic replacement, and both complete semantic inverses reconstruct those originals.",
    }


if __name__ == "__main__":
    try:
        result = main()
    except Exception as error:
        result = {
            "status": "failed_independent_gaussian35_owner_installation_review",
            "reviewer": "/root/review_gaussian35",
            "binding": ref(BINDING),
            "errors": [type(error).__name__ + ": " + str(error)],
            "approved_mapping_proposals": [],
        }
    destination = OUT / "adaptive-gaussian35-owner-candidate-installation-review-v1.json"
    with destination.open("x") as stream:
        json.dump(result, stream, indent=2, ensure_ascii=False)
        stream.write("\n")
    print(json.dumps({"status": result["status"], "errors": result["errors"], "review": ref(str(destination.relative_to(ROOT)))}))
    if result["errors"]:
        raise SystemExit(1)
