#!/usr/bin/env python3
"""Write the bounded independent B2 review; never mutate coverage or source files."""
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import re
import sys

ROOT = Path(__file__).resolve().parents[4]
OUT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / "book"))
from validate import Document


def digest(data):
    return hashlib.sha256(data).hexdigest()


def ref(name):
    path = ROOT / name
    raw = path.read_bytes()
    return {"file": name, "sha256": digest(raw), "bytes": len(raw)}


def text_hash(value):
    return digest(value.encode())


NEW = "SafeLearning.CompleteModulesAdaptiveGaussianEnvelope35."
HORIZON = "SafeLearning.CompleteModulesLoSBOGaussianHorizon."
GAUSSIAN = "SafeLearning.CompleteModulesLoSBOGaussianNoise."
THEORY = "SafeLearning.CompleteModulesTheory."
BOOK = "SafeLearning.CompleteModulesBook."
SAFETY = "SafeLearning.CompleteModulesSafeExploration."
PROOF = "verification/lean/SafeLearning/CompleteModulesAdaptiveGaussianEnvelope35.lean"
new_names = [
    NEW + "conditional_gaussian_kernel_implies_genuine_marginal_gaussian_law",
    NEW + "adaptive_conditional_gaussian_errors_obey_the_finite_horizon_envelope",
    NEW + "source_envelope_is_the_actual_printed_expression",
    NEW + "actual_log_twenty_thousand_has_a_rational_enclosure",
    NEW + "source_envelope_and_first_radius_have_the_printed_six_decimal_roundings",
    NEW + "actual_source_hundred_adaptive_errors_fail_the_envelope_with_probability_at_most_one_percent",
    NEW + "first_reading_and_lipschitz_bound_certify_every_point_in_the_source_radius",
]
support_names = [
    HORIZON + "actual_centered_gaussian_law_has_its_genuine_subgaussian_mgf",
    HORIZON + "actual_gaussian_two_sided_tail_has_the_literal_exponential_bound",
    HORIZON + "actual_horizon_radius_gives_the_exact_delta_tail_allocation",
    HORIZON + "actual_all_horizon_gaussian_noise_exceedance_probability_is_at_most_delta",
    GAUSSIAN + "actual_nondegenerate_gaussian_has_positive_probability_outside_every_finite_bound",
    GAUSSIAN + "actual_independent_gaussian_first_T_noise_bounds_have_probability_p_power_T",
    GAUSSIAN + "actual_nondegenerate_independent_gaussian_eventually_exceeds_each_chosen_finite_fixed_bound",
    THEORY + "finite_failure_union",
    THEORY + "simultaneous_success",
    BOOK + "losbo_cones",
    SAFETY + "lipschitz_query_safety",
]
proof_files = [
    PROOF,
    "verification/lean/SafeLearning/CompleteModulesLoSBOGaussianHorizon.lean",
    "verification/lean/SafeLearning/CompleteModulesGPNumerics.lean",
    "verification/lean/SafeLearning/CompleteModulesLoSBOGaussianNoise.lean",
    "verification/lean/SafeLearning/CompleteModulesTheory.lean",
    "verification/lean/SafeLearning/CompleteModulesBook.lean",
    "verification/lean/SafeLearning/CompleteModulesSafeExploration.lean",
]
local_dependencies = [
    "verification/lean/.lake/packages/mathlib/Mathlib/Probability/Kernel/CondDistrib.lean",
    "verification/lean/.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Probability.lean",
    "verification/lean/.lake/packages/mathlib/Mathlib/Analysis/Complex/ExponentialBounds.lean",
]
source_files = [
    "book/chapters/safe-bo-theory.html",
    "SafeLearning/safe-bo-theory.html",
]
baseline_files = [
    "book/coverage/inventory.json",
    "book/coverage/inventory-after-correction90.json",
    "book/coverage/modules.json",
    "book/coverage/core.json",
    "book/coverage/foundations.json",
    "book/coverage/applied.json",
    "book/coverage/progress.json",
]
frozen = {name: ref(name) for name in proof_files + source_files + baseline_files}
inventory = json.loads((ROOT / "book/coverage/inventory.json").read_text())
ledger = json.loads((ROOT / "book/coverage/modules.json").read_text())
exercise_key = "safe-bo-theory.html#book-m5-b2"
exercise = next(x for x in inventory["exercises"] if x["key"] == exercise_key)
original_exercise = next(x for x in ledger["exercises"] if x["inventory_key"] == exercise_key)
units = {u["key"]: u for u in inventory["material_source_units"]}
unit_numbers = [845, 864, 865, 885, 886, 892, 896]
selected_keys = [f"safe-bo-theory.html::node-{n}" for n in unit_numbers]
material_claims = {k: r for r in ledger["material_claims"] for k in r.get("source_unit_keys", [])}
site_bytes = (ROOT / source_files[1]).read_bytes()
start = site_bytes.index(b"<!-- BOOK APPLICATION START -->") + len(b"<!-- BOOK APPLICATION START -->")
end = site_bytes.index(b"<!-- BOOK APPLICATION END -->", start)
embedded = site_bytes[start:end].strip() + b"\n"
chapter_bytes = (ROOT / source_files[0]).read_bytes()
assert embedded == chapter_bytes
site_document = Document(site_bytes.decode())
chapter_document = Document(chapter_bytes.decode())
assert site_document.by_id["book-m5-b2"].text() == exercise["source_text"]
assert chapter_document.by_id["book-m5-b2"].text() == exercise["source_text"]
assert text_hash(exercise["source_text"]) == exercise["text_sha256"]
for key in selected_keys:
    number = int(key.rsplit("-", 1)[1])
    assert site_document.nodes[number - 1].text() == units[key]["source_text"]
    assert text_hash(units[key]["source_text"]) == units[key]["text_sha256"]
    assert units[key]["source_sha256"] == frozen[source_files[1]]["sha256"]
assert frozen["book/coverage/inventory.json"]["sha256"] == frozen["book/coverage/inventory-after-correction90.json"]["sha256"]
assert inventory["source_sha256"][source_files[1]] == frozen[source_files[1]]["sha256"]
source_proof = (ROOT / PROOF).read_text()
actual_theorems = re.findall(r"^theorem\s+(\w+)", source_proof, re.M)
assert [NEW + n for n in actual_theorems] == new_names
assert not re.search(r"\b(sorry|admit|axiom|native_decide)\b", source_proof)

actual_receipts = []
for stem in ("adaptive-gaussian35-standalone-execution-v3", "adaptive-gaussian35-named-execution-v1"):
    receipt_file = "reports/full-coverage/" + stem + ".json"
    receipt = json.loads((ROOT / receipt_file).read_text())
    log = ref(receipt["log"])
    assert receipt["status"] == "passed" and receipt["actual_exit_code"] == 0
    assert receipt["helper_sha256_before"][PROOF] == frozen[PROOF]["sha256"]
    assert receipt["helper_sha256_after"][PROOF] == frozen[PROOF]["sha256"]
    assert log["sha256"] == receipt["log_sha256"]
    actual_receipts.append({
        "receipt": ref(receipt_file),
        "log": log,
        "actual_exit_code": receipt["actual_exit_code"],
        "actual_command": receipt["actual_command"],
        "proof_sha256": frozen[PROOF]["sha256"],
        "review_scope": "Read the existing native receipt and actual log and checked their hashes. The independent reviewer did not rerun this command or infer a fresh aggregate/kernel/axiom audit.",
    })

conditional_hypotheses = [
    "An actual probability measure P on a measurable experiment space.",
    "For each time t, the actual error and pre-query history are AEMeasurable under P.",
    "The selected history represents the relevant information available before that error, including an adaptively selected gain; the theorem does not validate a physical sensor or infer this assumption from observations.",
    "The actual regular conditional distribution condDistrib (noise t) (history t) P equals the constant centered gaussianReal law of variance sigma^2, almost everywhere under the actual P.map history law.",
    "sigma>0, a finite positive horizon, and 0<delta<=1; the source specialization uses sigma=3/20, horizon=100, delta=1/100.",
    "No independence of different errors or queries is assumed for the finite union bound.",
]
radius_hypotheses = [
    "The fixed headroom function is globally LipschitzWith 4/5 in the metric used for the gain; on the real line this is the source absolute-difference assumption.",
    "The actual first observation satisfies 19/20=f(center)+error, and |error|<=sourceEnvelope on the good noise event.",
    "The candidate has distance from that center at most the exact sourceCertifiedRadius; source threshold is zero and boundary equality is allowed.",
]
numeric_limits = [
    "The sufficient E is the exact 0.15*sqrt(2*log(20000)) expression. The printed 0.667575 is a nearest six-decimal approximation and is below the exact E; it is not substituted into the safety theorem.",
    "The certified radius is the exact (0.95-E)/0.8 expression. The printed 0.353031 is a nearest six-decimal approximation and is above the exact radius; it is not silently treated as a certified outer endpoint.",
    "The Gaussian envelope is a finite unconditional failure-probability bound on the experiment law. It is not a posterior probability after conditioning on the observed value y0=0.95.",
    "At most 100 errors is covered by a subset of the displayed 100-event failure union. There is no theorem here for a 101st error, an unbounded run, or a new risk budget after a reset.",
    "The implication protects true headroom pointwise on the noise event. It does not validate the hardware model, identify the Lipschitz constant, make a GP authoritative, or claim maximum possible safe reach.",
]
new_reviews = [
    {
        "declaration": new_names[0], "status": "approved",
        "review": "The hypothesis is equality of the actual Mathlib regular conditional-distribution kernel under the actual history pushforward, not a supplied HasLaw conclusion or a predicate renamed 'conditional'. condDistrib_comp_map integrates the kernel to P.map noise; Measure.comp_congr replaces it by the constant Gaussian kernel; const_comp and the history probability mass yield the real Gaussian marginal. Both AEMeasurable assumptions are used by the disintegration identity, so map totalization cannot provide the claimed law for an arbitrary nonmeasurable error. inferInstance supplies the probability-map instance available in the installed Mathlib.",
    },
    {
        "declaration": new_names[1], "status": "approved",
        "review": "Each genuine conditional law is converted by the previous declaration to an actual marginal Gaussian law with variance sigma^2. The imported genuine Gaussian MGF/Chernoff result and finite event union give the stated actual P.real failure bound. The target event is not a hypothesis. No joint independence, filtration chain, query law, or sensor-validity conclusion is smuggled in. Arbitrary adaptive query choices are allowed to the extent that the supplied pre-query history kernels retain the source conditional Gaussian law.",
    },
    {
        "declaration": new_names[2], "status": "approved",
        "review": "sourceSigma is exact NNReal 3/20, sourceEnvelope is actualHorizonRadius sourceSigma 100 (1/100), and norm_num converts 2*100/(1/100) to 20000. gaussianReal's parameter is variance; the probability specialization correctly uses sourceSigma^2.",
    },
    {
        "declaration": new_names[3], "status": "approved",
        "review": "The rational identity 20000=20^4/2^3 converts the actual logarithm to 4*log20-3*log2. The imported rational log20 enclosure and the installed Mathlib rational log2 bounds imply 9.9034875<log20000<9.9034876. There is no float-evaluation premise or approximation axiom.",
    },
    {
        "declaration": new_names[4], "status": "approved",
        "review": "The square-root argument proves its argument is nonnegative, uses the real sqrt squared identity and sqrt nonnegativity, and obtains 0.6675754<sourceEnvelope<0.6675755 before linear propagation through the exact radius. Both printed values have strict error<0.0000005. The same rational enclosure proves 0<sourceCertifiedRadius<1, which substantiates the comparison with the original radius 1. Rounded decimals are not used as certificate parameters.",
    },
    {
        "declaration": new_names[5], "status": "approved",
        "review": "The source uses a genuine Fin100 error family, the actual conditional kernels, exact sigma=3/20 and delta=1/100. The result bounds the actual event that any of these errors exceeds the exact sourceEnvelope. Relabel Fin100 indices 0..99 as the first 100 source errors; no conclusion about later errors is obtained.",
    },
    {
        "declaration": new_names[6], "status": "approved",
        "review": "The genuine reading identity and |error|<=E imply f(center)>=0.95-E. The actual Lipschitz distance inequality implies f(point)>=f(center)-0.8*dist(point,center). Distance<=the exact (0.95-E)/0.8 pays that loss and proves f(point)>=0. The target safety conclusion is not assumed. This works pointwise for every point in the closed ball, including the boundary, and on the real gain line gives the source first interval around a0=0.",
    },
]


def clause(value, names, correspondence, hypotheses=None, status="proved"):
    return {
        "statement_in_prose": value,
        "exact_text_sha256": text_hash(value),
        "status": status,
        "lean_declarations": names,
        "hypotheses": hypotheses or [],
        "correspondence": correspondence,
        "remaining_gaps": [],
    }


prompt_clauses = [
    clause(original_exercise["claims"][0]["statement_in_prose"], new_names[:2] + [new_names[5]],
           "The conditional Gaussian model is an explicit actual condDistrib kernel hypothesis with mean 0 and variance (3/20)^2. The law is adopted as the source assumption and then integrated to an actual Gaussian marginal and actual finite-horizon failure bound; the theorem does not claim to prove the sensor assumption from data.", conditional_hypotheses),
    clause(original_exercise["claims"][1]["statement_in_prose"], [new_names[5]],
           "Specialize the general result to the first 100 errors and delta=1/100. Any smaller selected prefix has a failure event contained in that 100-event union.", conditional_hypotheses),
    clause(original_exercise["claims"][2]["statement_in_prose"], new_names + support_names[:4],
           "The imported actual Gaussian MGF/two-sided tail supplies the displayed exponential bound; actualHorizonRadius and exact tail-allocation identity supply a sufficient exact E. The new exact expression, rational log enclosure, both six-decimal error bounds, and direct true-function radius implication complete both requested outputs.", conditional_hypotheses + radius_hypotheses),
]
hint_text = units["safe-bo-theory.html::node-892"]["source_text"]
hint_clause = clause(
    hint_text,
    [new_names[0], new_names[1], new_names[5]] + support_names[:4] + support_names[7:9],
    "For each actual Gaussian law the two-sided Chernoff bound at actualHorizonRadius is 2*exp(-E^2/(2*sigma^2)); the imported exact allocation identity sets 100 times this bound to 1/100, so each is (1/100)/100. The finite-union proof sums these real-measure bounds without an independence hypothesis.",
    conditional_hypotheses,
)
solution_text = units["safe-bo-theory.html::node-896"]["source_text"]
solution_sentences = [
    r"Choose $E=0.15\sqrt{2\log(2\cdot100/0.01)}\approx0.667575$ degrees.",
    "The probability that any of the first 100 errors exceeds this envelope is at most 0.01.",
    r"On its complement, the first safe radius is $(0.95-E)/0.8\approx0.353031$.",
    "This region is much smaller than radius 1 under the original deterministic bound.",
    "The new statement is probabilistic and finite-horizon; continuing beyond 100 evaluations requires a new budget or an all-time construction.",
    "The Gaussian conditional assumption matters because query adaptation must not invalidate the stated tail bound.",
]
assert " ".join(solution_sentences) == solution_text
solution_clauses = [
    clause(solution_sentences[0], [new_names[2], new_names[3], new_names[4], new_names[5]],
           "The source exact E equals sourceEnvelope; the actual log enclosure and sqrt proof establish the strict six-decimal rounding error. The exact expression, rather than the lower printed decimal, is the sufficient certificate.", conditional_hypotheses),
    clause(solution_sentences[1], [new_names[0], new_names[1], new_names[5]] + support_names[:4],
           "The actual conditional kernels give actual centered Gaussian laws; their genuine tails and a 100-event union bound prove the literal probability<=0.01.", conditional_hypotheses),
    clause(solution_sentences[2], [new_names[4], new_names[6]],
           "On the complement of the strict exceedance union, the first error has |error|<=sourceEnvelope. The reading identity plus Lipschitz bound proves true nonnegative headroom for every point at distance<=sourceCertifiedRadius. The exact radius definition and strict half-unit error give the displayed approximation; the upper rounded decimal is not used as an outer certificate.", radius_hypotheses),
    clause(solution_sentences[3], [new_names[4], support_names[9]],
           "The new numerical theorem proves 0<sourceCertifiedRadius<1 and its approximate value 0.353031; losbo_cones identifies the original deterministic first cone with [-1,1]. The words 'much smaller' are the pedagogical comparison of these checked radii, not a separate exact inequality threshold."),
    clause(solution_sentences[4], [new_names[1], new_names[5]],
           "The quantified theorem covers a finite horizon and actual failure probability. Its Fin100 specialization gives no 101st-event or all-time claim. 'Requires a new budget or an all-time construction' is scope guidance for extending this theorem, not a new all-time safety result.", conditional_hypotheses),
    clause(solution_sentences[5], [new_names[0], new_names[1], new_names[5]],
           "The actual conditional law is retained for the relevant pre-query history and converted to the tail law used in the bound. The error family can be dependent, and gain adaptation needs no independent-query assumption. Correct noise kernels remain a hypothesis; no theorem says adaptation always preserves them.", conditional_hypotheses),
]
exercise_mappings = []
for original, mapped in zip(original_exercise["claims"][:3], prompt_clauses):
    assert original["status"] == "pending"
    exercise_mappings.append({
        "claim_id": original["id"],
        "inventory_key": exercise_key,
        **mapped,
        "original_status": original["status"],
    })
component = original_exercise["claims"][3]
assert component["status"] == "proved"
exercise_mappings.append({
    "claim_id": component["id"],
    "inventory_key": exercise_key,
    **clause(component["statement_in_prose"], component["lean_declarations"] + new_names[:2] + [new_names[5]] + support_names[:4],
             "Retain the existing finite union/success component. The previously listed Gaussian-tail, log/square-root E, actual conditional-law adaptation, and radius-approximation gaps are now discharged by the seven new declarations and reviewed actual Gaussian horizon support.",
             conditional_hypotheses),
    "original_status": "proved",
})
material_mappings = []
for number in unit_numbers:
    key = f"safe-bo-theory.html::node-{number}"
    unit = units[key]
    if number == 845:
        names = [new_names[0], new_names[1], new_names[5]] + support_names[:4]
        correspondence = "The complete literal is a learning objective with mathematical content. The reviewed genuine-law, actual finite-horizon-radius, true tail and finite-union declarations perform the stated conversion; it is not excluded merely because it is an objective."
        hypotheses = conditional_hypotheses
        kind = "mathematical_statement"
        status = "proved"
        parts = []
    elif number == 864:
        names = []
        correspondence = "Read the complete literal in its warning context. This box-label names a common mistake; it does not assert the quoted mistake as a theorem. Its substantive body is separately covered by node-865, and no support-bound conclusion is inferred from the label."
        hypotheses = []
        kind = "literal_pedagogical_topic_route_or_local_navigation"
        status = "not_a_formal_claim"
        parts = []
    elif number == 865:
        names = support_names[4:7] + [new_names[0], new_names[5]]
        correspondence = "Read the complete warning. The actual nondegenerate Gaussian theorem proves probability<1 of every finite bounded interval, in particular bound=sigma=3/20. The actual independent Gaussian finite-prefix and all-time statements supply a counterexample to promoting finitely observed small calibration errors to a universal support bound: every chosen fixed bound is eventually exceeded almost surely in that admissible model. Independence is used only in this counterexample, not in B2's finite envelope proof. The new conditional-law envelope theorem displays the honest finite probability and horizon. The warning is a mathematical non-inference, not a nonformal calibration disclaimer."
        hypotheses = [
            "The sensor's centered Gaussian variance is (3/20)^2!=0.",
            "For the finite-calibration counterexample, choose genuinely independent measurable centered Gaussian errors; this exhibits lack of a universal inference from finite small observations, without claiming all conditional-law families are independent.",
            "The B2 envelope retains its actual conditional-law and finite100 hypotheses.",
        ]
        kind = "mathematical_statement"
        status = "proved"
        parts = []
    elif number == 885:
        names = new_names + support_names[:4]
        correspondence = "All three sentences of the exact prompt have been mapped as the original pending requirements 1..3. This whole prompt adopts actual conditional noise and finite-budget hypotheses and requests both sufficient E and true-function radius; all requested outputs are covered, including the displayed Gaussian tail."
        hypotheses = conditional_hypotheses + radius_hypotheses
        kind = "mathematical_statement"
        status = "proved"
        parts = prompt_clauses
    elif number == 886:
        names = []
        correspondence = "The complete paragraph only links the learner to the existing #losbo noise-assumptions explanation. It contains no formula, value, or quantified mathematical claim. The linked LoSBO parents remain separate inventory units and are not promoted by this navigation review."
        hypotheses = []
        kind = "literal_pedagogical_topic_route_or_local_navigation"
        status = "not_a_formal_claim"
        parts = []
    elif number == 892:
        names = hint_clause["lean_declarations"]
        correspondence = hint_clause["correspondence"]
        hypotheses = conditional_hypotheses
        kind = "mathematical_statement"
        status = "proved"
        parts = [hint_clause]
    else:
        names = new_names + support_names[:4] + [support_names[9]]
        correspondence = "Independently read all six sentences of the entire solution, including both numerical approximations, genuine finite failure bound, true-function radius on the complement, original-radius comparison, horizon/scope guidance, and actual conditional-law requirement for adaptation. The clause mappings cover the complete literal; no suffix is dropped or declared nonformal to hide a mathematical gap."
        hypotheses = conditional_hypotheses + radius_hypotheses
        kind = "mathematical_statement"
        status = "proved"
        parts = solution_clauses
    material_mappings.append({
        "claim_id": material_claims[key]["id"],
        "material_unit_key": key,
        "source": unit["source"],
        "source_line": unit["line"],
        "source_sha256": unit["source_sha256"],
        "exact_text_sha256": unit["text_sha256"],
        "statement_in_prose": unit["source_text"],
        "original_status": material_claims[key]["status"],
        "status": status,
        "kind": kind,
        "lean_declarations": list(dict.fromkeys(names)),
        "hypotheses": hypotheses,
        "correspondence": correspondence,
        "remaining_gaps": [],
        "clause_mappings": parts,
    })
all_exercise_names = list(dict.fromkeys(
    new_names + support_names[:4] + support_names[7:10]))
whole_exercise = {
    "inventory_key": exercise_key,
    "status": "complete_math",
    "original_status": original_exercise["status"],
    "source": exercise["source"],
    "locator": exercise["locator"],
    "source_sha256": exercise["source_sha256"],
    "exact_text_sha256": exercise["text_sha256"],
    "statement_in_prose": exercise["source_text"],
    "lean_declarations": all_exercise_names,
    "hypotheses": conditional_hypotheses + radius_hypotheses,
    "correspondence": "Complete question, review route, hint and six-sentence worked solution were read in both exact chapter and embedded native source. All three original pending requirements and every solution sentence have explicit mappings. The review paragraph and interactive 'Show hint'/'Show worked solution' labels are navigation only. The finite-horizon extension recommendation is scope guidance; numerical, probability, radius, original-radius comparison and conditional-law content remain mathematical and are formally mapped.",
    "remaining_gaps": [],
    "original_pending_claim_ids": [x["id"] for x in original_exercise["claims"] if x["status"] == "pending"],
    "prompt_clauses": prompt_clauses,
    "hint_clause": hint_clause,
    "solution_clauses": solution_clauses,
    "legitimately_nonformal_clauses": [
        {
            "text": "Review: Noise assumptions in the safety proof.",
            "status": "not_a_formal_claim",
            "reason": "Local navigation to #losbo; it does not certify the linked theorem body.",
        },
        {
            "text": "Show hint / Show worked solution",
            "status": "not_a_formal_claim",
            "reason": "Disclosure-control labels only; their mathematical child paragraphs are fully mapped.",
        },
        {
            "text": "continuing beyond 100 evaluations requires a new budget or an all-time construction",
            "status": "scope_guidance_only",
            "reason": "Instruction for extending the displayed finite theorem; the finite horizon and probability statement are explicitly retained as mathematical scope.",
        },
    ],
}
context_keys = [349, 353, 356, 358, 360, 361, 364, 365, 366, 370, 373, 374, 375,
                847, 848, 849, 851, 853, 854, 855, 857, 859, 861, 898, 899]
contexts = [
    {
        "material_unit_key": f"safe-bo-theory.html::node-{n}",
        "source_line": units[f"safe-bo-theory.html::node-{n}"]["line"],
        "exact_text_sha256": units[f"safe-bo-theory.html::node-{n}"]["text_sha256"],
        "current_status": material_claims[f"safe-bo-theory.html::node-{n}"]["status"],
        "disposition": "reviewed_for_context_only_no_promotion",
        "reason": "The complete background or commissioning literal was read to interpret B2. The focused conditional100 proof does not by association discharge this separate unit's full general/hardware/acquisition/domain or deterministic worked-decision scope.",
    }
    for n in context_keys
]
already_complete_contexts = [
    {
        "material_unit_key": f"safe-bo-theory.html::node-{n}",
        "exact_text_sha256": units[f"safe-bo-theory.html::node-{n}"]["text_sha256"],
        "current_status": material_claims[f"safe-bo-theory.html::node-{n}"]["status"],
        "disposition": "existing_proved_scope_not_promoted_again",
    }
    for n in [1112, 1193]
]
source_review = {
    "schema_version": 1,
    "generated_at_utc": datetime.now(timezone.utc).isoformat(),
    "reviewer": "/root/review_gaussian35",
    "kind": "independent_exact_native_source_and_full_scope_review",
    "status": "approved",
    "errors": [],
    "findings": [],
    "inventory": frozen["book/coverage/inventory.json"],
    "source90_inventory_identity": frozen["book/coverage/inventory-after-correction90.json"],
    "baseline_owner": frozen["book/coverage/modules.json"],
    "source_sources": [frozen[n] for n in source_files],
    "proof_sources": [frozen[n] for n in proof_files],
    "local_dependency_sources": [ref(n) for n in local_dependencies],
    "declarations": new_names,
    "declaration_count": len(new_names),
    "supporting_declarations": support_names,
    "supporting_declaration_count": len(support_names),
    "new_declaration_reviews": new_reviews,
    "actual_native_execution_receipts_read": actual_receipts,
    "independent_reviewer_compiler_execution": False,
    "actual_compile_evidence_limit": "The native standalone and named receipts are genuine completed launches for the current proof hash. This source review neither replaces nor asserts a fresh aggregate build, kernel replay, transitive-axiom audit or selection/integration of checkpoint35.",
    "chapter_and_embedded_fragment_exact_bytes": {
        "same": True, "sha256": digest(chapter_bytes), "bytes": len(chapter_bytes),
        "method": "Strip only surrounding whitespace between native BOOK APPLICATION markers and append the chapter trailing newline.",
    },
    "full_exercise_literal_check": {
        "native_site_and_native_chapter_match_inventory_text": True,
        "inventory_key": exercise_key,
        "source_text_sha256": exercise["text_sha256"],
        "original_pending_claim_ids": whole_exercise["original_pending_claim_ids"],
        "solution_material_unit_key": "safe-bo-theory.html::node-896",
        "whole_solution_text_sha256": units["safe-bo-theory.html::node-896"]["text_sha256"],
        "whole_solution_sentence_count": len(solution_sentences),
    },
    "whole_exercise_mapping": whole_exercise,
    "exercise_claim_mappings": exercise_mappings,
    "material_mappings": material_mappings,
    "proposed_material_unit_keys": selected_keys,
    "proposed_proved_material_count": sum(x["status"] == "proved" for x in material_mappings),
    "proposed_nonformal_material_count": sum(x["status"] == "not_a_formal_claim" for x in material_mappings),
    "background_and_overlapping_parent_scope": contexts,
    "already_proved_related_scopes": already_complete_contexts,
    "scope_limits": numeric_limits,
    "no_external_browsing_needed": "The exact HTML source, immediate proof imports, supporting proofs and installed Mathlib conditional-distribution/numeric definitions are given locally. No paper attribution or new external empirical claim is approved here.",
    "preservation": {
        "canonical_proofs_site_owners_progress_not_edited": True,
        "no_archive_or_lake_copy": True,
        "original_receipts_and_logs_preserved": True,
    },
}
review_path = OUT / "adaptive-gaussian35-independent-source-review-v1.json"
proposal_path = OUT / "adaptive-gaussian35-proposed-exact-mapping-v1.json"
for name, before in frozen.items():
    assert ref(name) == before, name
with review_path.open("x") as stream:
    json.dump(source_review, stream, indent=2, ensure_ascii=False)
    stream.write("\n")
proposal = {
    "schema_version": 1,
    "generated_at_utc": source_review["generated_at_utc"],
    "reviewer": source_review["reviewer"],
    "kind": "independent_proposed_mapping_only_no_ledger_mutation",
    "status": "approved",
    "errors": [],
    "findings": [],
    "independent_source_review": ref(str(review_path.relative_to(ROOT))),
    "inventory": source_review["inventory"],
    "proof_sources": source_review["proof_sources"],
    "source_sources": source_review["source_sources"],
    "declarations": new_names,
    "declaration_count": len(new_names),
    "whole_exercise": whole_exercise,
    "exercise_claim_mappings": exercise_mappings,
    "material_mappings": material_mappings,
    "scope_limits": numeric_limits,
    "integration_owner": "Root must prepare candidates, apply these mappings conservatively, and obtain final independent candidate review before installation.",
}
with proposal_path.open("x") as stream:
    json.dump(proposal, stream, indent=2, ensure_ascii=False)
    stream.write("\n")
print(json.dumps({
    "status": "approved",
    "review": ref(str(review_path.relative_to(ROOT))),
    "proposed_mapping": ref(str(proposal_path.relative_to(ROOT))),
    "declarations": len(new_names),
    "original_pending_exercise_claims": len(whole_exercise["original_pending_claim_ids"]),
    "material_proved": source_review["proposed_proved_material_count"],
    "material_nonformal": source_review["proposed_nonformal_material_count"],
    "errors": [],
}))
