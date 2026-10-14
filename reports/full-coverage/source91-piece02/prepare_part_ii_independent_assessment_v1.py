#!/usr/bin/env python3
"""Save manually reviewed mathematical scopes with independently checked bytes.

No source, proof, owner or progress file is modified. Existing compiler evidence
is read and hash-bound; no compiler success is newly claimed by this preparation.
"""
import hashlib
import json
from pathlib import Path
import re
import runpy

ROOT = Path(__file__).resolve().parents[3]
PACKET = "reports/full-coverage/source91-piece01/next-piece02-candidate-v1.json"
REPORT = "reports/full-coverage/source91-piece02/landscape-ar-part-ii-independent-preparation-v1.json"
PREVIOUS_REVIEW = "reports/full-coverage/source91-piece01/landscape-ar-part-i-independent-source-review-v1.json"
P = "SafeLearning.CompleteModulesLandscapeSource91ARPartI."
L = "SafeLearning.CompleteModulesLandscapeARGaussianLaw."
A = "SafeLearning.CompleteModulesLandscapeARGaussianAlgebra."
F = "SafeLearning.CompleteModulesLandscapeARPathFluctuation."
G = "SafeLearning.CompleteModulesLandscapeGaussianTailCounts."
V = "SafeLearning.CompleteModulesLandscapeARViolationCounts."
E = "SafeLearning.CompleteModulesGaussianErfcTail."
C = "SafeLearning.CompleteAppliedGaussianCDF."
I = "SafeLearning.CompleteModulesLandscapeFiniteCounts."


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def ref(path):
    return {"file": path, "sha256": sha((ROOT / path).read_bytes())}


def read(path):
    return json.loads((ROOT / path).read_bytes())


def clause(identifier, unit, statement, declarations, hypotheses, assessment, gaps=(), classification="mathematical"):
    return {"id": "landscape-1.5-part-ii::" + identifier,
            "material_unit_key": "landscape.html::node-" + str(unit),
            "status": "candidate_existing_support" if not gaps else "candidate_remaining_gap",
            "classification": classification, "statement_in_prose": statement,
            "lean_declarations": declarations, "actual_hypotheses": hypotheses,
            "correspondence_assessment": assessment, "remaining_gaps": list(gaps),
            "completion_credit": 0}


CLAUSES = [
    clause("actual-gaussian-marginal", 1446,
           "A finite linear transformation of the independent Gaussian noises gives the actual state law N(m_t,v_t).",
           [L + "actual_recursive_trajectory_has_a_genuine_joint_gaussian_law",
            L + "actual_vector_trajectory_is_exactly_the_affine_finite_gaussian_noise_map",
            P + "actual_infinite_state_has_the_same_internally_derived_gaussian_marginal",
            P + "actual_infinite_state_mean_and_variance_are_the_printed_finite_formulas"],
           ["Canonical independent standard Gaussian infinite noise law; arbitrary real parameters and natural time."],
           "Already sufficient for this real-valued assertion: the law is derived from the literal recurrence and actual product noises, then transported to the infinite process. Gaussian variance is trueVariance.toNNReal, with nonnegativity proved. No target Gaussian law is assumed for the state."),
    clause("positive-standardizing-denominator", 1446,
           "v_t>0 makes sqrt(v_t)>0, so the standardization is legitimate.",
           [V + "actual_positive_time_and_nonzero_noise_make_the_standardizing_denominator_nonzero",
            A + "actual_positive_time_and_nonzero_noise_have_strictly_positive_variance"],
           ["Either assume v_t>0 directly, or use t>0 and sigma!=0 for the actual source state."],
           "The actual source variance is strictly positive at every positive time when the noise scale is nonzero; its real square root and NNReal stateSD are strictly positive/nonzero. The parameter called sigma in the generic GaussianTailCounts theorem is the state's standard deviation, not the recurrence's noise scale."),
    clause("actual-standardized-law", 1448,
           "(x_t-m_t)/sqrt(v_t) has the actual standard-normal law on infiniteNoiseLaw.",
           [G + "actual_gaussian_upper_tail_is_the_standard_cdf_complement",
            P + "actual_infinite_state_has_the_same_internally_derived_gaussian_marginal",
            V + "actual_one_based_state_has_the_true_derived_gaussian_law"],
           ["Positive true state variance; instantiate the generic SD by NNReal.sqrt(trueVariance.toNNReal)."],
           "The generic tail proof internally constructs this law using gaussianReal_sub_const and gaussianReal_div_const; the finite AR theorem correctly identifies stateSD^2 with the actual variance. This is a genuine existing mathematical bridge, but no public current-source statement exports the normalized infinite state law.",
           ["Make the infinite-state HasLaw instantiation and variance/SD conversion explicit in a current-source declaration or exact formal composition. Do not provide an unexplained HasLaw premise for the desired normalized state."]),
    clause("displayed-standardized-event-chain", 1448,
           "Pr(x_t>1)=Pr((x_t-m_t)/sqrt(v_t)>(1-m_t)/sqrt(v_t)).",
           [G + "actual_gaussian_upper_tail_is_the_standard_cdf_complement",
            V + "actual_positive_time_and_nonzero_noise_make_the_standardizing_denominator_nonzero"],
           ["sqrt(v_t)>0; the two events use the same actual infinite process and measure."],
           "The generic tail theorem's body proves the exact set identity by positive-denominator division and translation. Its endpoint exposes only the final CDF complement, so the displayed middle event needs an explicit same-process instantiation, not just a renamed tail quantity.",
           ["Export/compose the pointwise event equivalence and actual probability equality on infiniteNoiseLaw for the displayed threshold one."]),
    clause("tail-cdf-complement", 1448,
           "The true standardized tail is Q(z)=1-Phi(z), with a strict upper event.",
           [E + "actual_standard_gaussian_upper_tail_is_the_cdf_complement_and_density_integral",
            G + "actual_gaussian_upper_tail_is_the_standard_cdf_complement"],
           ["z is real; Phi=standardCDF is standard-normal mass of Iic z; Q=upperTail is mass of Ioi z."],
           "The complement of Iic z is Ioi z and standard Gaussian total mass is one. This proves the exact strict-tail complement, rather than defining an arbitrary function called Q. Combine with the normalized actual-state bridge above for the full display."),
    clause("cdf-definition", 1449,
           "Phi denotes the standard-normal cumulative distribution function.",
           [C + "actual_standard_gaussian_cdf_is_its_density_integral"],
           ["standardCDF x is defined as (gaussianReal 0 1).real(Iic x)."],
           "The definition is the actual probability CDF and its density integral is proved. The notation sentence is definitional; it does not assert a numerical approximation or software implementation."),
    clause("same-process-one-to-T-count", 1450,
           "N is the actual sum of T strict unsafe-event indicators at times one through T on the same infinite path.",
           [F + "actual_infinite_trajectory_agrees_with_every_existing_finite_horizon_prefix",
            F + "actual_infinite_noise_prefix_has_the_existing_finite_product_law",
            V + "actual_source_expected_violation_count_is_the_one_to_T_sum_of_true_tails",
            I + "actual_step_cost_is_the_zero_one_source_indicator"],
           ["Finite T>=0; one-based time is t.val+1 for t:Fin T; events are x_t>1."],
           "Existing violationCount is the right finite-horizon count under noiseLaw T. Existing prefix agreement gives pointwise agreement of every monitored infinite state with stateAt on the projected Fin T noises. The source count on the infinite space still needs that explicit pullback equality or a direct definition and proof.",
           ["Define the literal infinite-path count and prove it equals finite violationCount composed with the prefix projection, or prove the complete expectation directly on infiniteNoiseLaw with the actual one-based states.",
            "Do not instantiate the generic Fin(N+1) theorem with N=T: it would monitor T+1 times and include degenerate time zero. Handle T=0 correctly."]),
    clause("linearity-and-integrability-no-state-independence", 1449,
           "The expectation of the finite count is the sum of marginal probabilities, without independent states.",
           [I + "actual_expected_indicator_count_is_sum_of_marginal_probabilities",
            I + "actual_count_and_event_indicators_are_integrable",
            V + "actual_source_expected_violation_count_is_the_one_to_T_sum_of_true_tails"],
           ["Probability measure; finitely many measurable strict unsafe events; no independence hypothesis for the state family."],
           "Both existing bodies integrate bounded event indicators, use integral_finsetSum, then integral_indicator_one. No independent-state premise appears. For a direct infinite-space instantiation, establish actual state/event measurability; PartI publicly exports HasLaw/AEMeasurable, so ordinary MeasurableSet preimages need an explicit measurable finite-prefix composition or an appropriate AE-measurable argument.",
           ["Record the literal infinite count and its required measurability/integrability, avoiding an unjustified upgrade from AEMeasurable to Measurable."]),
    clause("expected-count-cdf-tail-sum", 1450,
           "E[N]=sum_{t=1}^T p_t=sum_{t=1}^T Q((1-m_t)/sqrt(v_t)) under positive state variances.",
           [V + "actual_source_expected_violation_count_is_the_one_to_T_sum_of_true_tails",
            V + "actual_each_one_based_violation_probability_is_the_printed_piecewise_tail"],
           ["Nonzero recurrence noise scale, or all monitored variances positive, for the unbranched Q-sum. The piecewise exactTail formula is valid also at sigma=0."],
           "The existing finite count theorem proves the complete piecewise identity for every real gain, goal and noise scale and any T. For sigma!=0, exactTail reduces to the printed CDF complement; for sigma=0 it is a strict deterministic indicator. The index set Fin T exactly represents times one through T.",
           ["Transport/derive this expectation for the same infinite process, preserving the positive-variance condition on the unbranched displayed Q-sum."]),
    clause("time-zero-safe", 1451,
           "Time zero can be omitted because x0=0<=1.",
           [V + "actual_initial_state_never_violates_and_zero_horizon_has_zero_count",
            F + "actual_infinite_trajectory_satisfies_the_literal_initial_condition_and_recursion"],
           ["All real parameters and every noise sequence; strict unsafe threshold is one."],
           "Actual finite and infinite recurrences both start at zero. This is enough for a direct infinite zero-time safety specialization, and the finite theorem correctly includes a zero-count empty horizon."),
    clause("zero-noise-degeneracy", 1451,
           "sigma=0 gives variance zero and a deterministic state; standard-normal normalization cannot be used.",
           [F + "actual_zero_noise_infinite_state_path_is_the_true_deterministic_mean",
            P + "actual_infinite_state_mean_and_variance_are_the_printed_finite_formulas",
            V + "actual_each_one_based_violation_probability_is_the_printed_piecewise_tail"],
           ["sigma=0; t>=0; no stability restriction is needed for finite-time determinism."],
           "The actual infinite state is trueMean for every noise sequence and trueVariance is zero. In Lean real division is total with division by zero returning zero, so do not treat that convention as a valid probabilistic standardization. The zero-noise branch must use the deterministic tail rather than Q(0)=1/2. The sentence 'standardization is invalid' is the method's positive-variance precondition, not a claim that Lean's division operation is undefined."),
    clause("zero-noise-strict-tail-and-boundary", 1451,
           "p_t=1{m_t>1} at sigma=0, and m_t=1 is safe.",
           [G + "actual_zero_variance_gaussian_tail_is_the_deterministic_strict_indicator",
            V + "actual_zero_noise_is_deterministic_and_equality_at_the_boundary_is_safe",
            P + "actual_infinite_state_has_the_same_internally_derived_gaussian_marginal"],
           ["Actual zero-noise state law; strict event 1<x_t."],
           "The generic proof uses the actual Dirac law and strict Ioi event; the finite AR theorem proves both the indicator formula and equality-at-one implication. The existing infinite marginal becomes the same zero-variance law, so a fresh exact instantiation suffices.",
           ["Include the infinite-state strict indicator/boundary specialization in the current source bridge or explicitly bind the derived Dirac law composition."]),
    clause("genuine-erfc-definition", 1452,
           "erfc(u)=2/sqrt(pi) times the genuine improper integral from u to infinity of exp(-s^2).",
           [E + "actual_complementary_error_function_uses_a_genuine_improper_integral"],
           ["u is any real; exp(-s^2) is integrable on the real line and the half-line."],
           "erfc is defined by the actual Ioi set integral. The theorem proves IntegrableOn and the atTop limit of finite interval integrals, so the improper-integral notation is justified and not a bare renaming of a target probability."),
    clause("erfc-identity-and-change-of-variable", 1452,
           "Q(z)=1/2 erfc(z/sqrt(2)); the substitution r=sqrt(2)*s produces this identity.",
           [E + "actual_standard_gaussian_upper_tail_is_the_cdf_complement_and_density_integral",
            E + "actual_density_change_of_variable_gives_the_complementary_error_function"],
           ["z is real; sqrt(2)>0; true Gaussian normalization and density integral."],
           "The actual integral change-of-variable theorem, square-root identity, transformed lower endpoint and Jacobian factor are all present in the proof body. The normalized density integral is the actual standard Gaussian upper-tail probability. No new mathematical implication is missing here."),
    clause("cdf-rounding-and-false-zero", 1452,
           "A finite-arithmetic CDF may round to one while the true Gaussian upper tail remains positive, causing a computed zero in 1-Phi.",
           [E + "actual_gaussian_upper_tail_is_positive_at_every_finite_threshold"],
           ["A specified finite rounding model is required to claim an arithmetic theorem."],
           "Real positivity is proved. None of the inspected audited sources defines a CDF approximation, rounding operator or finite floating format. A proof assuming roundedCDF=1 merely derives subtraction of one from one; it would not establish the asserted possible discrepancy for an actual positive Gaussian tail.",
           ["Either retain this assertion pending a stated nonvacuous numerical model, or explicitly classify only this exact implementation warning outside the real-probability formalization with a justified scope.",
            "For a mathematical rounding model, derive actual upperTail(z)>0 and arbitrarily small tails, then show CDF rounding to one in its defined upper rounding cell. Do not assume the desired false zero as the bridge hypothesis."],
           "numerical_arithmetic_warning_not_formalized_by_existing_real_proofs"),
    clause("direct-tail-evaluation-advice", 1452,
           "Use the direct upper-tail expression to avoid subtracting a near-one CDF from one.",
           [E + "actual_density_change_of_variable_gives_the_complementary_error_function"],
           ["This is an evaluation recommendation; no erfc routine or error model is specified."],
           "The exact real erfc identity supports the alternative expression. The recommendation and its outer formula avoid the particular CDF subtraction, but no theorem certifies a black-box erfc implementation or guarantees a nonzero numerical result. A narrow instructional/implementation classification is legitimate; it cannot discharge the neighboring rounding/underflow assertions.",
           [], "candidate_nonformal_implementation_advice_with_analytic_identity_support"),
    clause("underflow-caveat", 1452,
           "Even a direct upper-tail evaluation can underflow for sufficiently extreme tails.",
           [E + "actual_gaussian_upper_tail_is_positive_at_every_finite_threshold"],
           ["An arithmetic format with a smallest positive representable magnitude, or an explicit evaluation model, is required."],
           "The real-valued probability never underflows. Existing real erfc proofs contain no representability, exponent-range or rounding rule. The warning appropriately limits the recommendation, but it is a separate finite-arithmetic assertion.",
           ["Keep the arithmetic assertion pending or narrowly justify an implementation-scope classification. If proving a model, derive an actual positive tail below its zero-rounding/underflow cell; no theorem here proves Gaussian-tail decay at infinity or this model consequence."],
           "numerical_arithmetic_warning_not_formalized_by_existing_real_proofs"),
    clause("positive-true-finite-threshold-tails", 1452,
           "For nonzero noise, every monitored positive-time finite-threshold true Gaussian tail is positive.",
           [G + "actual_nondegenerate_gaussian_upper_tail_is_strictly_positive",
            V + "actual_nondegenerate_noise_makes_every_positive_time_violation_probability_positive",
            E + "actual_gaussian_upper_tail_is_positive_at_every_finite_threshold",
            P + "actual_infinite_state_has_the_same_internally_derived_gaussian_marginal"],
           ["sigma>0 in the source is sufficient for sigma!=0; monitored times are >=1; thresholds are real."],
           "Actual Gaussian measures are mutually absolutely continuous with volume at nonzero variance, making every finite strict upper half-line have positive mass. Finite AR probabilities are proved positive. The infinite marginal law gives the same positivity after a direct source bridge. This claim does not include deterministic time zero."),
    clause("positive-count-rejects-zero-budget", 1452,
           "A displayed rounded zero cannot certify a true zero expected unsafe-count budget when sigma>0 and T>0.",
           [V + "actual_source_expected_violation_count_is_the_one_to_T_sum_of_true_tails",
            V + "actual_nondegenerate_noise_makes_every_positive_time_violation_probability_positive",
            V + "actual_initial_state_never_violates_and_zero_horizon_has_zero_count"],
           ["Positive monitored horizon T>0 and nonzero noise scale; exact budget compares the true expected count with zero."],
           "Each true one-based tail is positive, so their nonempty finite sum is positive. The existing count identity and positive-tail statements imply the finite result; the same-process bridge is still needed for the current infinite count. A machine-displayed zero is not an upper bound on this positive real expectation. T=0 is a necessary exception: its true count is zero even with positive noise scale.",
           ["Add/compose a true expected-count positivity and zero-budget rejection result on the actual infinite process for T>0. Preserve the valid zero-horizon case.",
            "A separate rounding model is needed to prove that a particular display actually becomes zero." ]),
    clause("analytical-versus-numerical-exactness", 1452,
           "'Exact expectation' names the analytical identity; a finite-precision evaluation is an approximation subject to rounding.",
           [V + "actual_source_expected_violation_count_is_the_one_to_T_sum_of_true_tails"],
           ["Interpret the word exact as a real mathematical identity, not exact machine arithmetic or certified numerical rounding."],
           "This is a terminology and implementation-scope explanation. The analytical identity is formal mathematics. The sentence does not assert that every possible evaluation has strictly nonzero error, nor does it supply a certified error bound. A narrow nonformal/meta classification is justified without relabeling the whole mixed paragraph.",
           [], "candidate_nonformal_terminology_and_numerical_scope_explanation"),
]


def main():
    if (ROOT / REPORT).exists():
        raise RuntimeError("Refusing to overwrite immutable preparation")
    packet = read(PACKET)
    assert ref(PACKET)["sha256"] == "5e9f610956bdb5da0c8c981efebc4fd1c9a3f7b4bf221bd54ec504f3727dbc85"
    for k in ("inventory", "reader_source", "existing_selected_audit"):
        assert ref(packet[k]["file"]) == packet[k]
    raw = (ROOT / packet["reader_source"]["file"]).read_bytes()
    fragment = packet["fragment"]
    assert raw[fragment["start_byte"]:fragment["end_byte"]] == fragment["html"].encode()
    assert sha(fragment["html"].encode()) == fragment["sha256"]
    inventory = read(packet["inventory"]["file"])
    units = {u["key"]: u for u in inventory["material_source_units"]}
    previous = read(PREVIOUS_REVIEW)
    parser_binding = previous["helper"]
    assert ref(parser_binding["file"]) == parser_binding
    RawParser = runpy.run_path(str(ROOT / parser_binding["file"]), run_name="reuse_independent_raw_parser")["RawParser"]
    source = raw.decode()
    parser = RawParser(source)
    parser.feed(source)
    parser.close()
    node_by_slice = {(len(source[:n.start].encode()), len(source[:n.end].encode())): n
                     for n in parser.nodes if n.end is not None}
    audit = read(packet["existing_selected_audit"]["file"])
    assert audit["status"] == "passed"
    audited_names = {d["name"] for d in audit["declarations"]}
    declarations, proof_sources = {}, []
    bindings = packet["candidate_existing_audited_proofs"] + [
        ref("verification/lean/SafeLearning/CompleteAppliedGaussianCDF.lean"),
        ref("verification/lean/SafeLearning/CompleteModulesLandscapeFiniteCounts.lean"),
        ref("verification/lean/SafeLearning/CompleteModulesLandscapeARGaussianAlgebra.lean"),
        ref("verification/lean/SafeLearning/CompleteModulesLandscapeARPathFluctuation.lean"),
    ]
    for binding in bindings:
        assert ref(binding["file"]) == binding
        assert audit["proof_sha256"][binding["file"]] == binding["sha256"]
        text = (ROOT / binding["file"]).read_text()
        namespace = re.search(r"^namespace\s+(\S+)", text, re.M).group(1)
        matches = list(re.finditer(r"^theorem\s+(\w+)", text, re.M))
        names = []
        for i, match in enumerate(matches):
            stop = matches[i + 1].start() if i + 1 < len(matches) else text.index("\nend " + namespace, match.start())
            excerpt = text[match.start():stop].strip()
            name = namespace + "." + match.group(1)
            assert name in audited_names
            assert set(audit["axiom_dependencies"][name]) <= set(audit["allowed_standard_axioms"])
            declarations[name] = {"name": name, "file": binding["file"],
                                  "start_line": text.count("\n", 0, match.start()) + 1,
                                  "signature": excerpt.partition(":=")[0].strip(),
                                  "declaration_excerpt_sha256": sha(excerpt.encode())}
            names.append(name)
        proof_sources.append({**binding, "declaration_count": len(names), "declarations": names})
    assert len(CLAUSES) == 20
    unit_nodes, unit_reviews = [], []
    for unit in packet["source_units"]:
        row, key = unit["source_unit"], unit["key"]
        assert units[key] == row
        start, end = unit["start_byte"], unit["end_byte"]
        assert sha(raw[start:end]) == unit["html_sha256"]
        node = node_by_slice[(start, end)]
        assert node.tag == row["tag"] and "".join(node.text).strip() == row["source_text"]
        assert sha(row["source_text"].encode()) == row["text_sha256"]
        unit_nodes.append(node)
        clauses = [c for c in CLAUSES if c["material_unit_key"] == key]
        support = sorted({d for c in clauses for d in c["lean_declarations"]})
        assert support and all(d in declarations for d in support)
        gaps = list(dict.fromkeys(g for c in clauses for g in c["remaining_gaps"]))
        for c in clauses:
            c["exact_unit_text_sha256"] = row["text_sha256"]
            c["exact_unit_html_sha256"] = unit["html_sha256"]
        unit_reviews.append({"key": key, "material_unit_key": key,
                             "status": "candidate_no_completion_credit",
                             "whole_leaf_completion_proposed": False,
                             "start_byte": start, "end_byte": end, "line": row["line"],
                             "exact_html_sha256": unit["html_sha256"],
                             "exact_text_sha256": row["text_sha256"], "exact_text": row["source_text"],
                             "candidate_clause_ids": [c["id"] for c in clauses],
                             "existing_mathematical_declaration_support": support,
                             "remaining_gaps": gaps,
                             "mixed_numerical_scope": key.endswith("node-1452")})
    assert {u["key"] for u in unit_reviews} == {"landscape.html::node-" + str(n) for n in (1446,1448,1449,1450,1451,1452)}
    parent = unit_nodes[0].parent
    assert all(n.parent is parent for n in unit_nodes)
    direct = [n for n in parent.children if n.end is not None and
              fragment["start_byte"] <= len(source[:n.start].encode()) and
              len(source[:n.end].encode()) <= fragment["end_byte"]]
    assert direct == unit_nodes
    assert raw[fragment["end_byte"]:].startswith(b"<p><strong>(iii) Substitute and sum")
    # This report proposes bounded work; it intentionally grants zero completions.
    report = {
        "schema": "source91-piece02-independent-preparation-v1",
        "status": "preparation_candidate_no_completion_credit",
        "reviewer": "/root/review_gaussian35", "binding_errors": [],
        "candidate_packet": ref(PACKET), "inventory": packet["inventory"],
        "reader_source": packet["reader_source"],
        "fragment": {k: v for k, v in fragment.items() if k != "html"},
        "helper": ref(str(Path(__file__).relative_to(ROOT))),
        "independent_raw_parser": parser_binding, "previous_part_i_source_review": ref(PREVIOUS_REVIEW),
        "proof_sources": proof_sources, "declaration_count": len(declarations),
        "declarations": list(declarations.values()), "claims": CLAUSES, "source_units": unit_reviews,
        "existing_selected_audit": {**packet["existing_selected_audit"], "actual_status": "passed",
                                     "relevant_native_proof_hashes_match": True,
                                     "relevant_declarations_listed": True,
                                     "relevant_axioms_within_audited_standard_allowlist": True},
        "missing_bridge_summary": [
            "Actual infinite-state standardized normal law and the displayed same-measure event/probability chain.",
            "Literal infinite one-to-T indicator count with either finite-prefix pullback/expectation equality or a direct integrable finite-sum proof on the infinite space.",
            "Explicit actual event measurability when using ordinary MeasurableSet indicator lemmas; no automatic AEMeasurable-to-Measurable conversion.",
            "Exact infinite zero-noise strict indicator/boundary case, safe time zero and a valid empty horizon.",
            "For T>0 and sigma!=0, actual infinite expected-count positivity and consequent zero-budget rejection.",
            "A stated nonvacuous finite-arithmetic model for the rounding/underflow assertions, or explicit narrow justified numerical-implementation classifications. Do not classify the whole last paragraph as nonformal or complete it from erfc alone.",
        ],
        "minimal_optional_arithmetic_model": {
            "scope": "Proposal only; no model or theorem is authored/selected here.",
            "cdf_cancellation": "Define a nearest-rounding cell below representable one, with positive gap delta. Derive an actual tail 0<Q(z)<delta/2 and the corresponding CDF near one, then prove rounding to one and false zero. A conditional theorem whose premise already says the desired computed zero is not sufficient to prove possibility.",
            "direct_tail_underflow": "Define the lowest positive representable magnitude eta and its zero-rounding cell. Derive 0<Q(z)<eta/2, then the model's direct rounded tail is zero. The actual real erfc expression stays positive.",
            "analytic_prerequisite": "An actual Gaussian upper-tail-at-infinity limit gives arbitrarily small positive tails; no such public theorem is in these inspected candidate sources, though general measure/CDF convergence may supply it.",
            "limitations": "An abstract stated cell model illustrates the qualitative warning; it does not certify a concrete IEEE format, CDF/erfc library, implementation error or platform-specific cutoff.",
        },
        "scope": "Only current Source91 Exercise1.5 answer part(ii), six exact complete sibling leaves. Mathematical assertions, notation, method instructions, machine warnings and terminology are classified clause by clause. Canonical text is read, never edited. The existing real proofs contain no identified mathematical flaw; the gaps are exact same-process correspondence and unmodeled numerical assertions.",
        "new_complete_clauses": 0, "new_complete_material_units": 0, "new_complete_exercises": 0,
        "whole_exercise_status": "partial_from_delivered_part_i_only",
        "part_iii_and_all_ancestors": "pending_not_promoted_by_this_candidate",
        "historical_Source90_coverage": "Unchanged; no automatic mapping or count transfer.",
        "fresh_native_compilation_or_axiom_audit_claimed": False,
        "canonical_proof_owner_progress_or_publication_mutations": False,
    }
    (ROOT / REPORT).write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps({"report": ref(REPORT), "status": report["status"],
                      "candidate_clauses": len(CLAUSES), "candidate_whole_leaves": len(unit_reviews),
                      "existing_declarations_bound": len(declarations), "new_completion_credit": 0}))


if __name__ == "__main__":
    main()
