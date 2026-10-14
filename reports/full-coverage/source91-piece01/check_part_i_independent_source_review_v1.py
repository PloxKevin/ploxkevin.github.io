#!/usr/bin/env python3
"""Record a manually performed independent source review with native bindings.

The mathematical judgments below were made by reading each actual proof body.
Stdlib hashing and an independent raw HTML parser check their exact scope.
No Root claim/coverage/build helper is imported or invoked.
"""
import hashlib
from html.parser import HTMLParser
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[3]
PACKET = "book/coverage/source91-piece01/claims-v2.json"
REPORT = "reports/full-coverage/source91-piece01/landscape-ar-part-i-independent-source-review-v1.json"
PREPARATION = "reports/full-coverage/source91-piece01/landscape-ar-part-i-independent-preparation-v1.json"
P = "SafeLearning.CompleteModulesLandscapeSource91ARPartI."
A = "SafeLearning.CompleteModulesLandscapeARGaussianAlgebra."
L = "SafeLearning.CompleteModulesLandscapeARGaussianLaw."
M = "SafeLearning.CompleteModulesLandscapeARStableMoments."
S = "SafeLearning.CompleteModulesLandscapeARStationaryGaussian."
C = "SafeLearning.CompleteModulesLandscapeStationaryCharacterization."
F = "SafeLearning.CompleteModulesLandscapeARPathFluctuation."


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def ref(path):
    return {"file": path, "sha256": digest((ROOT / path).read_bytes())}


def read(path):
    return json.loads((ROOT / path).read_bytes())


class Node:
    def __init__(self, tag, attrs, start, parent):
        self.tag, self.attrs, self.start, self.parent = tag, dict(attrs), start, parent
        self.end = None
        self.children = []
        self.text = []


class RawParser(HTMLParser):
    VOID = set("area base br col embed hr img input link meta param source track wbr".split())

    def __init__(self, source):
        super().__init__(convert_charrefs=True)
        self.source = source
        self.line_starts = [0]
        self.line_starts.extend(i + 1 for i, c in enumerate(source) if c == "\n")
        self.stack, self.nodes = [], []

    def pos(self):
        line, col = self.getpos()
        return self.line_starts[line - 1] + col

    def handle_starttag(self, tag, attrs):
        node = Node(tag, attrs, self.pos(), self.stack[-1] if self.stack else None)
        if node.parent:
            node.parent.children.append(node)
        self.nodes.append(node)
        if tag in self.VOID:
            node.end = node.start + len(self.get_starttag_text())
        else:
            self.stack.append(node)

    def handle_startendtag(self, tag, attrs):
        self.handle_starttag(tag, attrs)
        if self.stack and self.stack[-1] is self.nodes[-1]:
            self.stack.pop().end = self.pos() + len(self.get_starttag_text())

    def handle_endtag(self, tag):
        for i in range(len(self.stack) - 1, -1, -1):
            if self.stack[i].tag == tag:
                self.stack[i].end = self.source.index(">", self.pos()) + 1
                del self.stack[i:]
                return

    def handle_data(self, data):
        for node in self.stack:
            node.text.append(data)


CLAUSE_NOTES = {
    "centering": ("k, goal, sigma are arbitrary reals; w is an arbitrary real noise sequence.",
                  "The primitive recursive infiniteTrajectory literally starts at zero and uses the printed update. Subtraction and ring prove the centered initial value and recurrence; no desired centered recursion is assumed."),
    "stability-iff": ("k is real; no one-sided stability hypothesis is assumed in the equivalence.",
                      "Both real inequalities are proved in both directions by abs_lt and linear arithmetic. The source abbreviation a=1-k preserves the exact strict inequalities."),
    "first-two-substitutions": ("Arbitrary real k, goal, sigma and real sequence w.",
                                "The two conjuncts unfold the actual original recurrence at times one and two, then ring. e0=-goal, so both intermediate substitutions match the source."),
    "unrolled-state": ("Arbitrary real parameters and w; every t in Nat, including zero.",
                       "The actual infinite path equals its finite prefix at horizon t. The finite affine trajectory theorem supplies the impulse coefficients; the explicitly typed finite-range sum and real algebra supply the printed sigma-times-sum expression. No recurrence solution or target formula is postulated."),
    "noise-moments-and-cross-covariances": ("Normalized infinite product of standard Gaussian laws; distinct indices s!=t for cross-covariance.",
                                           "Actual coordinate HasLaw gives zero means, unit variances and L2 membership. Actual iIndepFun gives independence for each distinct pair, then covariance_eq_zero. The independence and finite second moments are proved from the measure rather than left as an unexplained noise assumption."),
    "actual-state-moments": ("Canonical infinite standard Gaussian noise measure; arbitrary real parameters and every natural time.",
                             "Finite-prefix HasLaw composition transports the actual finite recursive Gaussian marginal to the same infinite path. Its integral and true variance give the printed mean and forward sum. Nonnegative trueVariance justifies toNNReal without clipping. sum_range_reflect proves the backward sum equality, with an empty sum at t=0."),
    "positive-geometric-denominator": ("0<k<2; a abbreviates 1-k.",
                                       "The wrapper proves 1-a^2=k(2-k)>0. Therefore a^2<1 by subtraction, with a^2>=0 from square nonnegativity. Expanding either polynomial gives 2k-k^2, the intermediate factorization in the prose. StableMoments' actual geometric proof uses geom_sum_mul_neg and pow_mul, not an assumed closed formula."),
    "geometric-formula-and-limits": ("0<k<2; arbitrary real goal and sigma; actual infinite-path moments already identified.",
                                     "The finite sum is proved equal to the closed expression after proving the denominator nonzero. The strict absolute multiplier bound gives power convergence and the actual mean limit; the square ratio bound gives the variance limit. Negative multipliers for 1<k<2 are included. Sigma=0 and t=0 are valid without division by a standard deviation."),
    "gaussian-update": ("Gaussian state has mean goal and variance v:NNReal; fresh noise is independent standard Gaussian; arbitrary real gain and sigma.",
                        "The actual independent product measure supplies the state and fresh noise laws. Scaling, independent Gaussian addition, and the constant shift derive a Gaussian of mean goal and variance (1-k)^2*v+sigma^2. This is a substitution test for a stationary law, not an assumption that the initial zero state is already stationary."),
    "stationary-variance-characterization": ("0<k<2; v>=0; independent fresh standard Gaussian noise and a Gaussian state of mean goal.",
                                             "Gaussian extensionality proves invariance iff the actual variance update is fixed. Positive k(2-k) then proves both directions of v=sigma^2/[k(2-k)]; the wrapper identifies this denominator with 1-a^2. Existing StationaryGaussian constructs this normalized law and proves its actual one-step invariance. This is uniqueness among mean-goal Gaussian laws, not arbitrary invariant measures."),
    "same-process-distribution-limit": ("0<k<2; all states use the one infinite independent Gaussian measure.",
                                       "The wrapper explicitly equates each infinite state pushforward to the internally derived finite actualTimeLaw, then transports actual characteristic-function convergence into the official TendstoInDistribution statement. The limit is the independently verified stationary Gaussian. Changing finite spaces are intermediate models, not the path process used in the final conclusion."),
    "no-noisy-path-limit": ("sigma>0 in the source, which implies the theorem's sigma!=0; no gain restriction is needed for this stronger path conclusion.",
                            "Positive Gaussian probabilities of >1 and <-1 are derived via mutual absolute continuity with volume. Independent coordinate events have divergent probability sums; second Borel-Cantelli puts both repeated crossings on a single almost-sure event. This excludes every finite noise limit on that event. Actual recurrence algebra shows any finite state-path limit would force a finite noise limit. Consequently the noisy state cannot converge to goal almost surely. No uncountable intersection of null sets is used."),
}

UNIT_SUPPORT = {
    1438: [P + "actual_centered_infinite_state_has_the_printed_initial_value_and_recursion",
           P + "source_stability_interval_is_exactly_the_strict_absolute_multiplier_condition",
           P + "actual_first_two_centered_substitutions_are_the_printed_values"],
    1440: [P + "actual_centered_infinite_state_has_the_printed_unrolled_finite_sum"],
    1441: [F + "actual_infinite_noises_are_independent_normalized_standard_gaussians",
           P + "actual_infinite_standard_noise_has_zero_mean_and_unit_variance",
           P + "actual_distinct_infinite_noise_cross_covariances_are_zero",
           P + "actual_centered_infinite_state_has_the_printed_unrolled_finite_sum",
           P + "actual_infinite_state_mean_and_variance_are_the_printed_finite_formulas",
           L + "actual_recursive_trajectory_coordinate_means_are_the_printed_means"],
    1442: [P + "actual_infinite_state_has_the_same_internally_derived_gaussian_marginal",
           P + "actual_infinite_state_mean_and_variance_are_the_printed_finite_formulas",
           P + "the_two_printed_variance_sums_are_equal"],
    1443: [P + "the_printed_denominator_factorization_is_positive_on_the_source_stability_interval",
           P + "source_stability_interval_is_exactly_the_strict_absolute_multiplier_condition",
           M + "actual_true_variance_has_the_printed_closed_geometric_formula"],
    1444: [P + "actual_infinite_state_mean_and_variance_are_the_printed_finite_formulas",
           M + "actual_true_variance_has_the_printed_closed_geometric_formula",
           M + "actual_state_mean_converges_to_the_goal_for_every_stable_source_gain",
           M + "actual_state_variance_converges_to_the_printed_stationary_variance"],
    1445: [C + "actual_arbitrary_gaussian_state_and_independent_fresh_noise_have_the_source_updated_law",
           C + "actual_gaussian_law_is_unchanged_exactly_when_the_true_variance_is_fixed",
           C + "actual_stable_gain_has_exactly_the_printed_gaussian_stationary_variance",
           P + "the_printed_denominator_factorization_is_positive_on_the_source_stability_interval",
           S + "actual_stationary_variance_is_the_printed_nonnegative_real_variance",
           S + "actual_stable_gaussian_law_is_invariant_under_one_update_with_independent_standard_noise",
           P + "actual_states_on_one_infinite_noise_space_converge_in_distribution_to_the_stationary_law",
           F + "actual_noisy_original_state_path_has_no_finite_real_limit_almost_surely"],
}
UNIT_NOTES = {
    1438: "Whole paragraph: centering and initial value, both stability directions, and both explicit first substitutions. The lead-in/header and definitions e=x-goal and a=1-k introduce notation, with no additional unproved mathematical assertion.",
    1440: "Whole unrolled identity, with exact finite time and index range and the empty t=0 sum.",
    1441: "Whole prose, including deterministic initial contribution to the mean. Unrolling and the actual coordinate-mean calculation show that zero-mean finite Gaussian noise contributes zero; noise means, unit variances, actual independence, and all distinct cross-covariances are supported. This leaf is not approved from its first noise-moment sentence alone.",
    1442: "All equalities: actual expectation, actual variance, backward weighted variance sum, and reflected forward sum. The deterministic mean and the centered-state abbreviation agree with the literal original state.",
    1443: "Whole geometric-method prose: ratio square is nonnegative and strictly below one; the denominator expansion 1-(1-k)^2=2k-k^2=k(2-k) and its strict positivity hold under exactly 0<k<2. Real expansion/subtraction are immediate consequences of the exact factorization; the finite geometric sum is proved in the cited theorem body.",
    1444: "Entire displayed closed variance formula and both limits, identified with actual process moments. No merely defined recurrence or assumed asymptotic variance is substituted for the probabilistic claims.",
    1445: "Entire final paragraph: actual independent Gaussian update, variance fixed-point equivalence, constructed stationary Gaussian, official distribution convergence of the same infinite process, and sigma>0 almost-sure failure to settle at goal. The path proof is stronger (no finite real limit) and does not assert every deterministic noise sequence fails to converge.",
}


def main():
    target = ROOT / REPORT
    if target.exists():
        raise RuntimeError("Refusing overwrite of independent review")
    packet = read(PACKET)
    assert ref(PACKET)["sha256"] == "3c36aaf6fa44e454492a2d63bbac11a3e1fac31d89b1fa13091975c3b7e84b87"
    inventory_ref = packet["inventory"]
    assert ref(inventory_ref["file"]) == inventory_ref
    inventory = read(inventory_ref["file"])
    exercise = next(e for e in inventory["exercises"] if e["key"] == packet["exercise"]["key"])
    assert exercise == packet["exercise"]
    assert digest(exercise["source_text"].encode()) == exercise["text_sha256"]
    raw = (ROOT / packet["reader_source"]["file"]).read_bytes()
    assert ref(packet["reader_source"]["file"]) == packet["reader_source"]
    fragment = packet["part_i"]
    assert raw[fragment["start_byte"]:fragment["end_byte"]] == fragment["html"].encode()
    assert digest(fragment["html"].encode()) == fragment["sha256"]
    source = raw.decode()
    parser = RawParser(source)
    parser.feed(source)
    parser.close()
    nodes = {}
    for node in parser.nodes:
        if node.end is not None:
            nodes[(len(source[:node.start].encode()), len(source[:node.end].encode()))] = node
    units_by_key = {u["key"]: u for u in inventory["material_source_units"]}
    expected_keys = {"landscape.html::node-" + str(n) for n in UNIT_SUPPORT}
    assert {u["source_unit"]["key"] for u in packet["source_units"]} == expected_keys
    assert len(packet["source_units"]) == 7
    declarations = {}
    proof_sources = []
    for binding in packet["proof_sources"]:
        assert ref(binding["file"]) == binding
        text = (ROOT / binding["file"]).read_text()
        assert not re.search(r"^\s*(axiom|sorry|admit)\b", text, re.M)
        namespace = re.search(r"^namespace\s+(\S+)", text, re.M).group(1)
        matches = list(re.finditer(r"^theorem\s+(\w+)", text, re.M))
        names = []
        for i, match in enumerate(matches):
            end = matches[i + 1].start() if i + 1 < len(matches) else text.index("\nend " + namespace, match.start())
            excerpt = text[match.start():end].strip()
            name = namespace + "." + match.group(1)
            declarations[name] = {"name": name, "file": binding["file"],
                                  "start_line": text.count("\n", 0, match.start()) + 1,
                                  "signature": excerpt.partition(":=")[0].strip(),
                                  "declaration_excerpt_sha256": digest(excerpt.encode())}
            names.append(name)
        proof_sources.append({**binding, "declaration_count": len(names), "declarations": names})
    assert len(declarations) == 68
    assert len(packet["claims"]) == len(CLAUSE_NOTES) == 12
    claims = []
    for claim in packet["claims"]:
        name = claim["id"].rsplit("::", 1)[1]
        hypotheses, correspondence = CLAUSE_NOTES[name]
        assert all(d in declarations for d in claim["lean_declarations"])
        assert claim["source_fragment"] in packet["source_units"]
        claims.append({"id": claim["id"], "verdict": "approved", "status": "proved_source_correspondence_reviewed",
                       "source_unit_key": claim["source_fragment"]["source_unit"]["key"],
                       "exact_text_sha256": claim["source_fragment"]["source_unit"]["text_sha256"],
                       "exact_html_sha256": claim["source_fragment"]["html_sha256"],
                       "statement_in_prose": claim["statement_in_prose"],
                       "lean_declarations": claim["lean_declarations"],
                       "actual_hypotheses": [hypotheses], "correspondence": correspondence,
                       "remaining_gaps": []})
    source_units, unit_nodes = [], []
    for unit in packet["source_units"]:
        row, key = unit["source_unit"], unit["source_unit"]["key"]
        assert row == units_by_key[key]
        assert digest(row["source_text"].encode()) == row["text_sha256"]
        start, end = unit["start_byte"], unit["end_byte"]
        assert fragment["start_byte"] <= start < end <= fragment["end_byte"]
        assert digest(raw[start:end]) == unit["html_sha256"]
        node = nodes[(start, end)]
        assert node.tag == row["tag"]
        assert "".join(node.text).strip() == row["source_text"]
        n = int(key.rsplit("-", 1)[1])
        support = UNIT_SUPPORT[n]
        assert all(d in declarations for d in support)
        unit_nodes.append(node)
        source_units.append({"key": key, "material_unit_key": key, "verdict": "approved",
                             "status": "proved_whole_direct_leaf_source_correspondence_reviewed",
                             "start_byte": start, "end_byte": end, "line": unit["line"],
                             "exact_html_sha256": unit["html_sha256"],
                             "exact_text_sha256": row["text_sha256"], "exact_text": row["source_text"],
                             "lean_declarations": support, "correspondence": UNIT_NOTES[n],
                             "full_leaf_mathematical_scope_reviewed": True,
                             "remaining_gaps": []})
    parent = unit_nodes[0].parent
    assert all(n.parent is parent for n in unit_nodes)
    direct_in_part = [n for n in parent.children if n.end is not None and
                      fragment["start_byte"] <= len(source[:n.start].encode()) and
                      len(source[:n.end].encode()) <= fragment["end_byte"]]
    assert direct_in_part == unit_nodes
    ancestors = []
    node = parent
    while node:
        assert node not in unit_nodes
        if node.end is not None:
            start, end = len(source[:node.start].encode()), len(source[:node.end].encode())
            ancestors.append({"tag": node.tag, "start_byte": start, "end_byte": end,
                              "sha256": digest(raw[start:end]), "status": "not_completed_by_this_piece"})
        node = node.parent
    part_ii = raw.index(b"<p><strong>(ii) Add the marginal failure probabilities.", fragment["end_byte"])
    part_iii = raw.index(b"<p><strong>(iii) Substitute and sum the specified forty steps.", part_ii)
    assert part_ii == fragment["end_byte"]
    answer_end = len(source[:parent.end].encode())
    pending = [
        {"id": "landscape-1.5-part-ii", "status": "pending", "start_byte": part_ii,
         "end_byte": part_iii, "sha256": digest(raw[part_ii:part_iii]),
         "remaining_scope": "Standardized Gaussian tails, indicator expected count, dependence-free expectation summation, time-zero and sigma-zero handling, erfc identity and numerical-cancellation/underflow discussion, and positive-tail/zero-budget assertions."},
        {"id": "landscape-1.5-part-iii", "status": "pending", "start_byte": part_iii,
         "end_byte": answer_end, "sha256": digest(raw[part_iii:answer_end]),
         "remaining_scope": "All exact substitutions and table decimals, forty-term count, stationary approximation/comparison, vacuous Markov bound, temporal covariance/joint law, and explicitly non-certified illustrative simulation statement."},
    ]
    native_receipts = []
    for path in ("reports/full-coverage/source91-piece01/root-wrapper-standalone-v1.json",
                 "reports/full-coverage/source91-piece01/four-candidates-named-build-v1.json",
                 "reports/full-coverage/source91-piece01/four-candidates-named-build-v2.json"):
        if (ROOT / path).exists():
            receipt = read(path)
            assert ref(receipt["log"])["sha256"] == receipt["log_sha256"]
            native_receipts.append({**ref(path), "actual_status": receipt["status"],
                                    "actual_exit_code": receipt["actual_exit_code"],
                                    "actual_command": receipt["actual_command"],
                                    "log": ref(receipt["log"]),
                                    "protected_input_hashes_before": receipt["helper_sha256_before"],
                                    "protected_input_hashes_after": receipt["helper_sha256_after"],
                                    "binding_errors_after": receipt["binding_errors_after"]})
    current_receipts = [r for r in native_receipts if r["file"].endswith("four-candidates-named-build-v2.json")]
    current_native_passed = bool(current_receipts and current_receipts[0]["actual_status"] == "passed" and
                                 current_receipts[0]["actual_exit_code"] == 0 and
                                 not current_receipts[0]["binding_errors_after"])
    if current_native_passed:
        receipt = current_receipts[0]
        for p in packet["proof_sources"][:4]:
            assert receipt["protected_input_hashes_before"][p["file"]] == p["sha256"]
            assert receipt["protected_input_hashes_after"][p["file"]] == p["sha256"]
    history = ref("reports/full-coverage/source91-piece01/history/wrapper-before-elaboration-fix-v1.lean.txt")
    assert history["sha256"] == "b2d81d70934570d15c24b376d3faf65950d829ed624e1d407b06e67a751c9be2"
    report = {
        "schema": "source91-piece01-independent-source-review-v1", "status": "approved",
        "errors": [], "reviewer": "/root/review_gaussian35",
        "helper": ref(str(Path(__file__).relative_to(ROOT))),
        "claim_packet": ref(PACKET), "inventory": inventory_ref,
        "source_sources": [packet["reader_source"]],
        "part_i": {k: v for k, v in fragment.items() if k != "html"},
        "exercise_key": exercise["key"], "whole_current_exercise_text_sha256": exercise["text_sha256"],
        "preparation": ref(PREPARATION), "proof_sources": proof_sources,
        "declaration_count": len(declarations), "declarations": list(declarations.values()),
        "claims": claims, "source_units": source_units,
        "counts": {"approved_mathematical_clauses": 12, "approved_whole_direct_leaf_units": 7,
                   "candidate_addition_declarations_reviewed": 36, "selected_dependency_declarations_reviewed": 32,
                   "whole_exercises_completed": 0},
        "scope": "Independent manually read mathematical proof/source-correspondence review of exactly current Source91 part(i). The raw parser independently checks all seven full direct sibling leaves. No question, parent/ancestor, part(ii), part(iii), other exercise, or global Source91 count is promoted.",
        "whole_exercise_status_after_success": "partial", "parts_ii_and_iii": pending,
        "uncompleted_ancestor_scopes": ancestors,
        "native_compilation_evidence": native_receipts,
        "current_named_build_passed_at_review": current_native_passed,
        "native_gate": "Source-correspondence approval is separate from native selection/axiom auditing. Root must retain a passing current hash-bound native build and fresh selected audit before integrating/selecting these declarations. This reviewer did not run or fabricate a compiler or axiom audit.",
        "retained_failure_history": history,
        "historical_source90_formal_coverage": "Unchanged historical identity; no automatic transfer or count promotion. The old owner corrected44-pending-whole record remains historical. Current Source91 completion is only this bounded reviewed part.",
        "canonical_or_ledger_changes": False,
    }
    target.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps({"report": ref(REPORT), "status": report["status"], "errors": [],
                      "counts": report["counts"], "current_named_build_passed_at_review": current_native_passed}))


if __name__ == "__main__":
    main()
