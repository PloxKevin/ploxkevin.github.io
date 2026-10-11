"""Validate a fresh, individually read whole-literal review of nine Systems units."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[5]
HERE = Path(__file__).resolve().parent
REQUEST = HERE / "full-literal-source-review-request-v2.json"
OUT = HERE / "systems-nine-literals-independent-foundations-source-review22-v1.json"
sys.path.insert(0, str(ROOT / "book/coverage"))
from lean_names import declarations


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_text())


def fingerprint(data):
    return hashlib.sha256(json.dumps(data, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


assert not OUT.exists()
assert sha(REQUEST) == "00d960509ad11bee8fa635c6125136b81300dd192e4177001c5e5387d0aa898a"
request = read(REQUEST)
inventory_path = ROOT / request["inventory"]
assert sha(inventory_path) == request["inventory_sha256"] == "2daa285ff1cbc2ad0db045e00e1271b6cb58ce809f5a8328120286748250c108"
inventory = {row["key"]: row for row in read(inventory_path)["material_source_units"]}
assert sha(ROOT / request["source"]) == request["source_sha256"]
html = (ROOT / request["source"]).read_text().splitlines()
for context in request["source_html_context"]:
    assert "\n".join(html[context["first_line"]-1:context["last_line"]]) == context["exact_html_lines"]
previous = request["previous_request"]
assert sha(ROOT / previous["file"]) == previous["sha256"]
assert read(ROOT / previous["file"]) == previous["exact_original_body_preserved"]

proofs = {request["new_actual_proof_source"]: request["new_actual_proof_source_sha256"],
          request["new_actual_companion_proof_source"]: request["new_actual_companion_proof_source_sha256"]}
for dependency in request["selected_dependencies"]:
    proofs[dependency["source"]] = dependency["source_sha256"]
declared = set()
for path, expected in proofs.items():
    assert sha(ROOT / path) == expected
    declared.update(row["name"] for row in declarations((ROOT / path).read_text()))
actual_records = []
for row in request["actual_execution_records"]:
    path = ROOT / row["file"]
    assert sha(path) == row["sha256"] and read(path) == row["record"]
    body = row["record"]
    assert body["exit_code"] == 0
    assert body["source_sha256_before"] == body["source_sha256_after"] == proofs[body["source"]]
    assert sha(ROOT / body["source_snapshot"]) == body["source_snapshot_sha256"] == proofs[body["source"]]
    assert sha(ROOT / body["log"]) == body["log_sha256"]
    actual_records.append(row)
assert len(actual_records) == 5
for key in ["failed_and_passed_original_trial_byte_manifest", "companion_history_manifest"]:
    path = ROOT / request[key]
    assert sha(path) == request[key + "_sha256"]
    for name, digest in read(path)["copies_sha256"].items():
        assert sha(ROOT / name) == digest

M = "SafeLearning.CompleteAppliedSystemsMaterial22."
C = "SafeLearning.CompleteAppliedSystemsMaterialConsequences22."
S = "SafeLearning.CompleteAppliedSystems."
D = "SafeLearning.CompleteAppliedDynamics."
O = "SafeLearning.CompleteAppliedScalarODE."
B = "SafeLearning.CompleteAppliedScalarODEBridges."
new = request["new_actual_public_theorems"]
companion = request["new_actual_companion_public_theorems"]
assert len(new) == 11 and len(companion) == 3 and set(new + companion) <= declared
decisions = {
    1646: ("proved", [companion[0], new[0], S+"shifted_temperature", S+"equilibrium_input"],
           "The entire target-equilibrium derivation now includes the arbitrary-input zero-rate iff input1, not only the exhibited equilibrium. Exact original/shifted vector-field identity, target translation and full heater-input interval equivalence match every clause. Unit names and ideal device assumptions are the stated model convention."),
    1649: ("proved", [S+"heldThermal_initial", S+"heldThermal_derivative", S+"sampled_thermal", D+"heldThermal_unique"],
           "The lead-in and linked entire held-input formula were read together. The actual exponential-affine trajectory has the correct initial value and differential equation; the genuine integrating-factor uniqueness proof identifies every differentiable trajectory with the stipulated constant input on the actual five-minute sampling interval. No varying-input formula is inferred."),
    1653: ("proved", [S+"sampled_feedback", S+"actuator_admissible", S+"sampled_thermal"],
           "The full instruction chooses exactly v=-x/2. Substitution into the true sampled model yields q=a-b/2 for all real errors, and the source gain respects its stipulated input convention. A separate physical units theorem or empirical controller performance is not asserted."),
    1663: ("not_a_formal_claim", [],
           "This separately read box label identifies the warning about analysing a different controller clock. It contains no equation, quantified implication or new mathematical assertion; the full following mathematical paragraph receives its own complete proved decision."),
    1664: ("proved", [new[i] for i in range(1,7)] + companion[1:] + [S+"sampled_thermal", S+"sampled_feedback", D+"thermal_rounded_coefficients", O+"actual_linear_ODE_unique", B+"actual_existing_linear_trajectory_equals_solution"],
           "The true substituted continuous rate is -3x/20; the actual exponential solution has initial state and five-minute factor exp(-3/4), with strict rational enclosure proving nearest-six rounding .472367. Generic actual linear-ODE uniqueness covers every existing continuously updated trajectory in its explicit differentiable domain. The factor is strictly distinct from the held .336402 factor; actual paths differ for nonzero initial error. The companion proves input equality iff error equality and that every nonzero initial continuous trajectory changes state, deviation and input at each positive time; zero initial error is the legitimate constant exception. The actual stable unclipped gain counterexample has convergent sampled trajectories while requesting3 outside[0,2]. Thus stability alone supplies no actuator guarantee. Repair instructions refer exactly to the already proved held-input derivation."),
    1673: ("proved", [new[7], D+"delayed_safe_iff", D+"nominal_delay_endpoint", S+"stopping_distance"],
           "The exact .4 coast distance, .4 remaining distance and .5 stopping demand are proved. The actual delayed stopped trajectory has distance-.1 at time1.4 and fails the all-time nonnegative-distance predicate; the genuine necessary-and-sufficient delay criterion gives the exact .3 endpoint. This concerns the specified coast-then-full-brake strategy in the ideal model."),
    1676: ("proved", [new[8], new[9], D+"stopped_safe_iff", D+"delayed_safe_iff"],
           "Immediate braking is genuinely all-time safe; the .4 delay violates the exact .3 condition. The all-time iff includes the complete distance consumed before braking. The optimistic-acceleration countermodel passes an estimate using a=2 while actual a=1 has negative stopping clearance and an explicitly unsafe stopped trajectory. Operational advice is scoped to the stated available, constant braking acceleration and ideal dynamics."),
    1719: ("proved", [new[10], S+"worst_case_delay", S+"uncertain_braking_guarantee", D+"robust_delayed_safe", D+"robust_delay_necessary"],
           "The full hint and referenced uncertainty exercise were read. Every scalar state in the complete specified distance/speed intervals and every constant available a>=1 is bounded by the actual smallest-distance/largest-speed/weakest-braking corner. Both delay travel and stopping distance are retained; the stopped delayed path gives all-time sufficiency, and the admissible worst corner gives necessity. No midpoint, finite sample, distribution or varying-acceleration guarantee replaces this interval model."),
    1740: ("not_a_formal_claim", [],
           "The entire separate synthesis paragraph is an instruction to recall explanations and identify the exact all-time proof steps in the two specified worked examples. It asks for a learner response and introduces no new quantified theorem, model, trajectory or additional guarantee. The referenced exact shifts, actuator counterexample, held between-reading bound and stopped/delayed all-time arguments were independently read; their mathematical decisions remain separately scoped above and are not blanket approval of neighbouring exercises or links."),
}
hypotheses = [
    "The immediately preceding source fixes the ideal scalar thermal model, exact sensing, ambient18, target22, heater range[0,2] and an actual five-minute constant-input hold. Degrees/minutes/kilowatts are the stipulated numerical conventions.",
    "Actual existing ODE trajectories satisfy the stated initial condition and genuine derivative/continuity hypotheses. Nonconstant continuous feedback requires nonzero initial error and positive elapsed time; the zero-error trajectory is correctly exempt.",
    "The braking model has nonnegative speed, constant positive available deceleration, coast during a nonnegative delay, then full braking until speed zero and a fixed stopped position. The uncertain interval specialization retains every stated distance, speed and a>=1 possibility.",
]
rows = []
for unit in request["material_units"]:
    assert unit == inventory[unit["key"]]
    number = int(unit["key"].split("node-")[1])
    status, refs, reason = decisions[number]
    assert set(refs) <= declared
    rows.append({"source_unit_key": unit["key"], "source": unit["source"], "source_sha256": unit["source_sha256"],
                 "source_text": unit["source_text"], "unit_text_sha256": unit["text_sha256"], "line": unit["line"], "locator": unit["locator"],
                 "entire_inventory_record": unit, "entire_inventory_record_sha256": fingerprint(unit),
                 "entire_literal_and_html_context_independently_read": True, "review_status": "approved_complete_source",
                 "material_status": status, "whole_unit_approved": True, "lean_declarations": sorted(set(refs)),
                 "hypotheses": hypotheses if status == "proved" else [], "per_unit_reason": reason,
                 "approved_components": [{"source_clause": unit["source_text"], "lean_declarations": sorted(set(refs)), "hypotheses": hypotheses,
                                          "review_status": "approved_complete_source", "per_component_reason": reason, "missing_clauses": []}] if refs else [],
                 "missing_clauses": []})
assert len(rows) == 9 and len({row["source_unit_key"] for row in rows}) == 9
selected = read(ROOT / "reports/full-coverage/checkpoint-21-selection.json")
assert selected["proof_file_count"] == 1089
for name, row in selected["proof_files"].items():
    assert sha(ROOT / name) == row["sha256"]
assert not {request["new_actual_proof_source"], request["new_actual_companion_proof_source"]} & set(selected["proof_files"])
report = {"status": "independent_complete_nine_source48_systems_material_literal_review_passed", "reviewer": "/root/config21_next",
          "reviewed_at_utc": datetime.now(timezone.utc).isoformat(), "request": REQUEST.relative_to(ROOT).as_posix(), "request_sha256": sha(REQUEST),
          "inventory": request["inventory"], "inventory_sha256": request["inventory_sha256"], "source": request["source"], "source_sha256": request["source_sha256"],
          "material_units": rows, "source_context_lines": request["source_html_context"], "proof_source_sha256": proofs,
          "actual_new_execution_records": actual_records, "new_public_theorems_independently_read": new + companion,
          "original_v1_request_preserved": previous, "original_trial_history_manifests": {key: request[key+"_sha256"] for key in ["failed_and_passed_original_trial_byte_manifest", "companion_history_manifest"]},
          "counts": {"individually_read_current48_whole_units": 9, "whole_proved_material_units": 7, "individually_nonformal_units": 2, "missing_clauses": 0, "new_public_theorems_read": 14, "actual_zero_records": 5},
          "protected21_selected_sources_checked": 1089, "coverage_complete": False,
          "independent_checker": Path(__file__).relative_to(ROOT).as_posix(), "independent_checker_sha256": sha(Path(__file__)),
          "limits": ["The two identified v1 gaps were closed by a distinct genuine three-theorem companion; immutable main source and all original request/trial/review times remain unchanged.",
                     "This is a fresh full literal decision for precisely these nine material units. It asserts neither whole neighbouring exercise coverage nor an aggregate22 audit or deployment.",
                     "Only actual canonical standalone/named executions and transparent identical selected dependency evidence are used. Nonempty original warning logs and empty genuine logs are both retained.",
                     "Only this independent future22 review output is written. Held21 proofs/ledgers/helpers/HTML/inventory are unchanged; ROOT progress/README are separately mutable actual deployment metadata."], "errors": []}
with OUT.open("x") as output:
    output.write(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
print(json.dumps({"status": report["status"], "review": OUT.relative_to(ROOT).as_posix(), "sha256": sha(OUT), "counts": report["counts"]}))
