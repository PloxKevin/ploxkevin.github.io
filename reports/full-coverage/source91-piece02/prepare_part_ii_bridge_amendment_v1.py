#!/usr/bin/env python3
"""Record read-only review of new bridge bodies; grant no source completion."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[3]
BASE = "reports/full-coverage/source91-piece02/landscape-ar-part-ii-independent-preparation-v1.json"
PROOF = "verification/lean/SafeLearning/CompleteModulesLandscapeSource91ARPartII.lean"
OUT = "reports/full-coverage/source91-piece02/landscape-ar-part-ii-new-bridge-independent-amendment-v1.json"
N = "SafeLearning.CompleteModulesLandscapeSource91ARPartII."


def ref(path):
    return {"file": path, "sha256": hashlib.sha256((ROOT / path).read_bytes()).hexdigest()}


def read(path):
    return json.loads((ROOT / path).read_bytes())


THEOREM_NOTES = {
    "actual_infinite_state_is_measurable": "Induction on the literal primitive recursive trajectory uses measurable coordinate projections and real sums/products. This is ordinary Measurable, resolving the earlier distinction from publicly exported HasLaw/AEMeasurable.",
    "actual_infinite_positive_time_state_has_the_existing_standard_deviation_law": "The actual infinite marginal law is rewritten using stateSD=NNReal.sqrt(trueVariance.toNNReal) and sq_sqrt. It holds at every natural time despite its name; at time zero it correctly gives the degenerate Gaussian. The state's SD is not confused with the recurrence noise scale.",
    "the_printed_standardized_event_is_pointwise_the_original_infinite_state_event": "At positive true variance, the real square root is positive. Positive-denominator division and common translation prove both event directions for every w. It is the actual same infinite state, not an assumed standardized random variable.",
    "actual_standardized_infinite_positive_time_state_has_standard_gaussian_law": "Actual infinite state HasLaw is derived, then subtraction/scaling of Gaussian laws is used. Positive time and nonzero noise give nonzero stateSD; its square is exactly the NNReal scaling variance, so variance division gives one and centered mean gives zero. Real.sqrt matches the NNReal SD representation. No target normalized-law hypothesis is assumed.",
    "actual_infinite_one_based_failure_probability_is_the_true_piecewise_tail": "Actual finite-prefix HasLaw transfers the measurable finite-state event. Literal prefix agreement identifies the state at t.val+1; an explicit set identity replaces the event before applying the existing finite piecewise-tail theorem. Fin T means exactly times one through T, and the T=0 case has no indices.",
    "actual_infinite_violation_count_is_the_finite_prefix_count_pointwise": "The newly defined infiniteViolationCount equals the existing violationCount pulled back by the Fin T prefix projection for each w. Both sum the same strict indicator at t.val+1. The recurrence prefix equality has the justified bound t.val+1<=T; no noise after the finite horizon enters.",
    "actual_infinite_violation_count_is_integrable": "A finite sum of indicator functions is integrable under the normalized infinite Gaussian measure. Each event is ordinarily measurable by the new state measurability theorem; no unproved AEMeasurable upgrade or independent-state premise is used.",
    "actual_one_to_T_infinite_indicator_expectation_is_the_sum_of_its_marginal_probabilities": "Direct integral_finsetSum on the infinite noise space is justified by integrability of each measurable bounded indicator. integral_indicator_one produces its actual event probability. No state independence appears among the hypotheses.",
    "actual_one_to_T_infinite_count_expectation_is_the_printed_piecewise_tail_sum": "Actual infinite count expectation is first identified with its true one-based marginal probabilities, then the finite-prefix-derived probability theorem gives exactTail. The formula holds for arbitrary real parameters and all T, including sigma=0 and T=0.",
    "actual_positive_noise_one_to_T_infinite_count_expectation_is_the_printed_erfc_sum": "The hypothesis is sigma!=0, stronger in scope than the printed sigma>0 case despite the theorem name. This selects the nondegenerate branch, then genuine CDF-complement/density and erfc change-of-variable identities transform each summand. The real erfc sum has no floating-point implementation or accuracy claim.",
    "actual_zero_noise_infinite_count_uses_strict_mean_indicators_and_boundary_equality_is_safe": "At zero noise the expectation is the sum of strict trueMean indicators; each mean equal to one gives zero actual infinite-state violation probability. For the general per-time indicator formula also cite the public infinite piecewise probability theorem; a summed expectation alone is not treated as an individual probability statement.",
    "actual_zero_noise_has_zero_variance_and_zero_standardizing_denominator": "The actual trueVariance definition specializes to zero and its real square root is zero at all times. This breaks the method's positive-variance precondition; it does not claim Lean real division is undefined. The separate deterministic probability branch prevents substituting Q(0)=1/2.",
    "actual_time_zero_is_safe_and_zero_horizon_has_zero_count_expectation": "The literal path starts at zero for every w, its strict upper-one event is empty with probability zero, and the empty Fin 0 count has zero expectation. These conclusions hold for all real parameters, including nonzero noise.",
    "actual_nonzero_noise_positive_horizon_count_is_positive_so_a_rounded_zero_cannot_certify_zero_cost": "All true marginal probabilities are nonnegative and the first one-based event has strictly positive probability for sigma!=0. A nonempty Fin T sum is therefore positive when T>0. The endpoint proves only positivity of the true expectation. It implies rejection of the exact zero budget, but does not prove existence or accuracy of any rounded display, CDF rounding or underflow model.",
}

CLAIM_NEW_SUPPORT = {
    "actual-gaussian-marginal": [],
    "positive-standardizing-denominator": ["actual_infinite_positive_time_state_has_the_existing_standard_deviation_law"],
    "actual-standardized-law": ["actual_infinite_positive_time_state_has_the_existing_standard_deviation_law", "actual_standardized_infinite_positive_time_state_has_standard_gaussian_law"],
    "displayed-standardized-event-chain": ["the_printed_standardized_event_is_pointwise_the_original_infinite_state_event", "actual_standardized_infinite_positive_time_state_has_standard_gaussian_law", "actual_infinite_one_based_failure_probability_is_the_true_piecewise_tail"],
    "tail-cdf-complement": ["actual_standardized_infinite_positive_time_state_has_standard_gaussian_law", "actual_infinite_one_based_failure_probability_is_the_true_piecewise_tail"],
    "cdf-definition": [],
    "same-process-one-to-T-count": ["actual_infinite_violation_count_is_the_finite_prefix_count_pointwise"],
    "linearity-and-integrability-no-state-independence": ["actual_infinite_state_is_measurable", "actual_infinite_violation_count_is_integrable", "actual_one_to_T_infinite_indicator_expectation_is_the_sum_of_its_marginal_probabilities"],
    "expected-count-cdf-tail-sum": ["actual_one_to_T_infinite_count_expectation_is_the_printed_piecewise_tail_sum", "actual_infinite_one_based_failure_probability_is_the_true_piecewise_tail", "actual_positive_noise_one_to_T_infinite_count_expectation_is_the_printed_erfc_sum"],
    "time-zero-safe": ["actual_time_zero_is_safe_and_zero_horizon_has_zero_count_expectation"],
    "zero-noise-degeneracy": ["actual_zero_noise_has_zero_variance_and_zero_standardizing_denominator", "actual_zero_noise_infinite_count_uses_strict_mean_indicators_and_boundary_equality_is_safe"],
    "zero-noise-strict-tail-and-boundary": ["actual_infinite_one_based_failure_probability_is_the_true_piecewise_tail", "actual_zero_noise_infinite_count_uses_strict_mean_indicators_and_boundary_equality_is_safe"],
    "genuine-erfc-definition": [],
    "erfc-identity-and-change-of-variable": ["actual_positive_noise_one_to_T_infinite_count_expectation_is_the_printed_erfc_sum"],
    "positive-true-finite-threshold-tails": ["actual_infinite_one_based_failure_probability_is_the_true_piecewise_tail", "actual_standardized_infinite_positive_time_state_has_standard_gaussian_law"],
    "positive-count-rejects-zero-budget": ["actual_nonzero_noise_positive_horizon_count_is_positive_so_a_rounded_zero_cannot_certify_zero_cost", "actual_time_zero_is_safe_and_zero_horizon_has_zero_count_expectation"],
}

UNIT_NEW_SUPPORT = {
    1446: ["actual_infinite_positive_time_state_has_the_existing_standard_deviation_law", "actual_standardized_infinite_positive_time_state_has_standard_gaussian_law"],
    1448: ["the_printed_standardized_event_is_pointwise_the_original_infinite_state_event", "actual_standardized_infinite_positive_time_state_has_standard_gaussian_law", "actual_infinite_one_based_failure_probability_is_the_true_piecewise_tail"],
    1449: ["actual_infinite_state_is_measurable", "actual_infinite_violation_count_is_integrable", "actual_one_to_T_infinite_indicator_expectation_is_the_sum_of_its_marginal_probabilities"],
    1450: ["actual_infinite_violation_count_is_the_finite_prefix_count_pointwise", "actual_one_to_T_infinite_indicator_expectation_is_the_sum_of_its_marginal_probabilities", "actual_one_to_T_infinite_count_expectation_is_the_printed_piecewise_tail_sum", "actual_positive_noise_one_to_T_infinite_count_expectation_is_the_printed_erfc_sum"],
    1451: ["actual_time_zero_is_safe_and_zero_horizon_has_zero_count_expectation", "actual_zero_noise_has_zero_variance_and_zero_standardizing_denominator", "actual_infinite_one_based_failure_probability_is_the_true_piecewise_tail", "actual_zero_noise_infinite_count_uses_strict_mean_indicators_and_boundary_equality_is_safe", "actual_one_to_T_infinite_indicator_expectation_is_the_sum_of_its_marginal_probabilities"],
    1452: ["actual_positive_noise_one_to_T_infinite_count_expectation_is_the_printed_erfc_sum", "actual_nonzero_noise_positive_horizon_count_is_positive_so_a_rounded_zero_cannot_certify_zero_cost"],
}


def main():
    if (ROOT / OUT).exists():
        raise RuntimeError("Refusing to overwrite immutable amendment")
    baseline = read(BASE)
    assert ref(BASE)["sha256"] == "b9b7120b50a3a5c9d339c970d22caa3beb07c5d921f7e0bff62a3b04a601e94c"
    assert ref(PROOF)["sha256"] == "eb37637d11b19bd76be5e469987668ef2edd9a2b2b50a06a2c93f0aea2e602b5"
    assert ref(baseline["reader_source"]["file"]) == baseline["reader_source"]
    source_bytes = (ROOT / baseline["reader_source"]["file"]).read_bytes()
    fragment = baseline["fragment"]
    assert hashlib.sha256(source_bytes[fragment["start_byte"]:fragment["end_byte"]]).hexdigest() == fragment["sha256"]
    for binding in baseline["proof_sources"]:
        assert ref(binding["file"]) == {"file": binding["file"], "sha256": binding["sha256"]}
    text = (ROOT / PROOF).read_text()
    assert not re.search(r"\b(sorry|admit)\b|^\s*axiom\b", text, re.M)
    matches = list(re.finditer(r"^theorem\s+(\w+)", text, re.M))
    assert {m.group(1) for m in matches} == set(THEOREM_NOTES)
    declarations = []
    for i, match in enumerate(matches):
        stop = matches[i+1].start() if i+1<len(matches) else text.index("\nend " + N[:-1], match.start())
        excerpt = text[match.start():stop].strip()
        declarations.append({"name": N + match.group(1), "file": PROOF,
                             "signature": excerpt.partition(":=")[0].strip(),
                             "start_line": text.count("\n", 0, match.start())+1,
                             "declaration_excerpt_sha256": hashlib.sha256(excerpt.encode()).hexdigest(),
                             "mathematical_body_verdict": "no_mathematical_findings",
                             "body_review": THEOREM_NOTES[match.group(1)]})
    receipts = []
    p = ROOT / "reports/full-coverage/source91-piece02"
    for file in sorted(p.glob("new-bridge-named-build-native-v*.json")):
        if file.name.endswith(".started.json"):
            continue
        path = str(file.relative_to(ROOT))
        receipt = read(path)
        assert ref(receipt["log"])["sha256"] == receipt["log_sha256"]
        receipts.append({**ref(path), "actual_status": receipt["status"],
                         "actual_exit_code": receipt["actual_exit_code"],
                         "actual_command": receipt["actual_command"], "log": ref(receipt["log"]),
                         "protected_hashes_before": receipt["helper_sha256_before"],
                         "protected_hashes_after": receipt["helper_sha256_after"],
                         "binding_errors_after": receipt["binding_errors_after"]})
    current_pass = any(r["actual_status"] == "passed" and r["actual_exit_code"] == 0 and
                       not r["binding_errors_after"] and
                       r["protected_hashes_before"].get(PROOF) == ref(PROOF)["sha256"] and
                       r["protected_hashes_after"].get(PROOF) == ref(PROOF)["sha256"] for r in receipts)
    claims = []
    for old in baseline["claims"]:
        key = old["id"].rsplit("::",1)[1]
        new = CLAIM_NEW_SUPPORT.get(key, [])
        record = {"id": old["id"], "material_unit_key": old["material_unit_key"],
                  "exact_unit_text_sha256": old["exact_unit_text_sha256"],
                  "exact_unit_html_sha256": old["exact_unit_html_sha256"],
                  "existing_lean_declarations": old["lean_declarations"],
                  "new_bridge_declarations": [N+n for n in new], "completion_credit": 0}
        if key in ("cdf-rounding-and-false-zero", "underflow-caveat"):
            record.update(status="pending_numerical_model_or_narrow_justified_classification",
                          remaining_gaps=old["remaining_gaps"])
        elif key in ("direct-tail-evaluation-advice", "analytical-versus-numerical-exactness"):
            record.update(status="candidate_narrow_instruction_or_meta_classification_retained",
                          remaining_gaps=[], correspondence=old["correspondence_assessment"])
        else:
            record.update(status="candidate_real_math_supported_awaiting_installed_source_packet_and_audit",
                          remaining_gaps=[], correspondence="New exact public bridges plus original actual real-valued proofs support this mathematical clause. This amendment gives no Source91/Source92 completion credit.")
            if key == "positive-count-rejects-zero-budget":
                record["remaining_gaps"] = ["No arithmetic model proves a particular displayed value actually rounds to zero; only true expectation positivity and its exact zero-budget implication are supported."]
            if key == "expected-count-cdf-tail-sum":
                record["guard"] = "Unbranched Q/erfc sum requires nonzero noise/all positive-time variances. The exactTail sum and zero-noise deterministic branch remain unconditional; empty horizon is valid."
        claims.append(record)
    units = []
    for old in baseline["source_units"]:
        number = int(old["key"].rsplit("-",1)[1])
        assert hashlib.sha256(source_bytes[old["start_byte"]:old["end_byte"]]).hexdigest() == old["exact_html_sha256"]
        mixed = number == 1452
        units.append({"key": old["key"], "material_unit_key": old["key"],
                      "status": "candidate_mixed_leaf_partial_only" if mixed else "candidate_supported_for_future_whole_leaf_review",
                      "exact_text_sha256": old["exact_text_sha256"],
                      "exact_html_sha256": old["exact_html_sha256"],
                      "start_byte": old["start_byte"], "end_byte": old["end_byte"],
                      "existing_mathematical_declaration_support": old["existing_mathematical_declaration_support"],
                      "new_mathematical_declaration_support": [N+n for n in UNIT_NEW_SUPPORT[number]],
                      "completion_credit": 0,
                      "remaining_gaps": ["CDF rounding/false-zero possibility and underflow remain unmodeled. Real erfc identities/positive expectation do not prove the full mixed paragraph."] if mixed else [],
                      "future_review_gate": "Fresh exact installed Source92 inventory/claim packet, current proof hashes and selected native/axiom audit. No automatic Source91-to-Source92 transfer."})
    histories = [ref(str(file.relative_to(ROOT))) for file in sorted((p/"history").glob("*.lean.txt"))]
    record = {
        "schema": "source91-piece02-new-bridge-independent-amendment-v1",
        "status": "preparation_amendment_current_named_build_passed_awaiting_installed_source_packet" if current_pass else "preparation_amendment_native_build_pending_no_completion_credit",
        "errors_in_mathematical_bodies": [], "binding_errors": [],
        "reviewer": "/root/review_gaussian35", "helper": ref(str(Path(__file__).relative_to(ROOT))),
        "original_preparation": ref(BASE), "candidate_packet": baseline["candidate_packet"],
        "current_Source91_inventory": baseline["inventory"], "reader_source": baseline["reader_source"],
        "fragment": fragment, "new_proof_source": ref(PROOF),
        "declaration_count": len(declarations), "declarations": declarations,
        "new_count_definition": {"name": N+"infiniteViolationCount", "scope": "Exactly T strict unsafe-event indicators at t.val+1 for t:Fin T on the actual infinite state process."},
        "claims": claims, "source_units": units, "native_build_receipts": receipts,
        "current_named_build_passed_at_review": current_pass,
        "preserved_failed_source_versions": histories,
        "current_axiom_audit_status": "The previous piece01 audit covers imported existing proofs; the 14 new declarations need Root's fresh selected audit. No current axiom-audit success is claimed here.",
        "future_source92_gate": "No Source92 installed inventory/claim packet has been reviewed in this amendment. Re-read exact Source92 bytes and scopes, including the unchanged part(i) seven leaves, before recording final correspondence. Student solution review alone is not a new Lean proof or formal count.",
        "scope": "Actual new 14 proof bodies manually reviewed without edits. Same-process mathematical gaps are addressed; source-level five-leaf completion is only a future recommendation, and the sixth mixed paragraph remains partial. All parent/question/part(iii) scopes remain pending.",
        "new_complete_clauses": 0, "new_complete_material_units": 0, "new_complete_exercises": 0,
        "canonical_or_proof_owner_progress_publication_changes": False,
    }
    (ROOT / OUT).write_text(json.dumps(record, indent=2, ensure_ascii=False)+"\n")
    print(json.dumps({"report": ref(OUT), "status": record["status"], "declarations": len(declarations),
                      "candidate_pure_whole_leaves": 5, "mixed_leaf_whole_completion": False,
                      "current_named_build_passed_at_review": current_pass, "new_completion_credit": 0}))


if __name__ == "__main__":
    main()
