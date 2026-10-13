"""Recompute selected arithmetic and matrix identities in the five authored drafts.

These checks supplement the displayed derivations; they do not automatically
approve pedagogy or turn floating-point values into validated certificates.
"""
import argparse
from fractions import Fraction as F
import hashlib
import json
import math
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "book/solutions"))
from solution_review import json_put

SELECTED = {
    "primer-optimization.html": ("primer-optimization-detailed-v1", "primer-optimization-detailed-v1"),
    "toolkit-lmi.html": ("toolkit-lmi-thorough-solutions-v2", "toolkit-lmi-thorough-solutions-v2"),
    "landscape.html": ("landscape-thorough-solutions-v1", "landscape-thorough-solutions-v1"),
    "lipsdp.html": ("lipsdp-thorough-solutions-v1", "lipsdp-thorough-solutions-v1"),
    "lipschitz-by-design.html": ("lipschitz-by-design-thorough-solutions-v1", "lipschitz-by-design-thorough-solutions-v1"),
}


def ref(name):
    p = ROOT / name
    return {"file": name, "sha256": hashlib.sha256(p.read_bytes()).hexdigest()}


def plain(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {k: plain(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [plain(v) for v in value]
    return value


def mm(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(len(b)))
             for j in range(len(b[0]))] for i in range(len(a))]


def transpose(a):
    return [list(row) for row in zip(*a)]


def sub(a, b):
    return [[x - y for x, y in zip(r, s)] for r, s in zip(a, b)]


def det2(a):
    return a[0][0] * a[1][1] - a[0][1] * a[1][0]


def eq(actual, expected, *, tolerance=None):
    if tolerance is None:
        assert actual == expected, (actual, expected)
    else:
        assert abs(actual - expected) <= tolerance, (actual, expected, tolerance)
    return actual


def cvar(points, alpha):
    # Convex finite-distribution hinge objective: checking every breakpoint
    # locates its minimum, since the outer interval slopes have opposite signs.
    return min(nu + sum(p * max(z - nu, 0) for z, p in points) / (1 - alpha)
               for nu in sorted({z for z, p in points}))


def run_cases():
    result = []

    def case(name, page, ordinals, function):
        try:
            value = function()
            result.append({"case": name, "page": page, "ordinals": ordinals,
                           "status": "passed", "computed": plain(value)})
        except Exception as error:
            result.append({"case": name, "page": page, "ordinals": ordinals,
                           "status": "failed", "error": repr(error)})

    opt = "primer-optimization.html"
    case("inverse_directional_derivative", opt, [5],
         lambda: eq(mm(mm([[F(1, 2), 0], [0, F(1, 3)]],
                         [[1, 1], [1, 0]]),
                     [[F(1, 2), 0], [0, F(1, 3)]]),
                    [[F(1, 4), F(1, 6)], [F(1, 6), 0]]))
    case("linear_solve_prediction_error", opt, [6],
         lambda: eq(F(2) / F("1.01") - F("1.98"), F(1, 5050)))
    case("accumulated_error_bounds", opt, [9],
         lambda: eq([F("0.05") * (F("1.2") ** t - 1) for t in [5, 6]],
                    [F("0.074416"), F("0.0992992")]))
    case("safety_qp_cost_and_stationarity", opt, [21],
         lambda: {"cost": eq((F(1) ** 2 + F("1.5") ** 2) / 2, F(13, 8)),
                  "stationarity": eq([1 - 1, F("1.5") - 2 + F("0.5")], [0, 0])})
    case("flow_transfer_minimum", opt, [25],
         lambda: eq(F("0.5") - F("0.2") + F("2.5") * F("0.2") ** 2, F("0.4")))
    case("flow_shadow_price_change", opt, [26],
         lambda: eq([F("0.4") * (4 - b) ** 2 for b in [F("2.5"), F("2.6")]],
                    [F("0.9"), F("0.784")]))
    case("flow_repair_cost", opt, [27],
         lambda: eq(((F("2.205") - 3) ** 2 + 4 * (F("0.795") - 1) ** 2) / 2,
                    F("0.4000625")))
    case("robust_clearance_boundary", opt, [28],
         lambda: eq(F("0.3") - F("0.2") * 0 - F("0.03"), F("0.27")))
    case("parseval_gradient_step_objective", opt, [30],
         lambda: eq(sum(x*x for row in sub(mm([[F("0.9"), F("0.8")],
                                                [F("-0.1"), F("0.9")]],
                                               [[F("0.9"), F("-0.1")],
                                                [F("0.8"), F("0.9")]]),
                                            [[1, 0], [0, 1]]) for x in row) / 4,
                    F("0.257175")))

    def iteration_thresholds():
        first = 1
        while 50 * 0.9 ** (2 * first) > 1e-6:
            first += 1
        faster = 0
        while 55 * (81 / 121) ** faster > 1e-6:
            faster += 1
        eq([first, faster], [85, 45])
        return {"first": first, "balanced": faster,
                "first_previous": 50 * 0.9 ** 168, "first_at": 50 * 0.9 ** 170,
                "balanced_previous": 55 * (81 / 121) ** 44,
                "balanced_at": 55 * (81 / 121) ** 45}
    case("gradient_iteration_thresholds", opt, [33], iteration_thresholds)
    case("boxed_safety_filter", opt, [34],
         lambda: {"cost": eq(((F("1.5") - 2) ** 2 + (F("1.35") - 1) ** 2) / 2,
                            F("0.18625")),
                  "stationarity": eq([F("-0.5") - F("0.175") + F("0.675"),
                                      F("0.35") - 2 * F("0.175")], [0, 0])})

    lmi = "toolkit-lmi.html"
    q = (13 + math.sqrt(5)) / 20
    case("startup_radius_and_disturbance_radius", lmi, [1, 2],
         lambda: {"startup_after": eq(q * math.sqrt(0.98), 0.7541468889856515,
                                       tolerance=1e-14),
                  "disturbance_radius": eq(0.05 / (1 - q), (7 + math.sqrt(5)) / 44,
                                            tolerance=1e-14),
                  "unit_disk_successor": q + 0.05})
    case("explicit_psd_eigenvectors", lmi, [4],
         lambda: eq(mm([[2, 1], [1, 2]], [[1, 1], [1, -1]]),
                    [[3, 1], [3, -1]]))

    def stein():
        a = [[F(1, 2), 2], [0, F(1, 2)]]
        p = [[F(4, 3), F(16, 9)], [F(16, 9), F(356, 27)]]
        residual = sub(mm(mm(transpose(a), p), a), p)
        eq(residual, [[-1, 0], [0, -1]])
        eq(det2(p), F(1168, 81))
        return {"residual": residual, "determinant": det2(p)}
    case("exact_stein_residual", lmi, [14], stein)
    case("lp_primal_dual_values", lmi, [16],
         lambda: eq([2*3 + 3*1, 4*F(3, 2) + 6*F(1, 2)], [9, 9]))
    case("scalar_gain_gap_identity", lmi, [20],
         lambda: [eq(p + p*p/(3*p-4) - 4, 4*(p-2)**2/(3*p-4))
                  for p in [F(7, 5), F(3, 2), F(2), F(3), F(100)]])

    landscape = "landscape.html"
    case("fleet_risk_product", landscape, [1],
         lambda: eq(0.9975**20, 0.9511698752531668, tolerance=1e-14))
    case("rare_spike_mean_and_cvar", landscape, [2],
         lambda: {"mean": eq(F("0.98")*59 + F("0.02")*109, 60),
                  "cvar": eq(cvar([(F(59), F("0.98")), (F(109), F("0.02"))],
                                   F("0.95")), 79)})
    case("three_atom_cvar", landscape, [8],
         lambda: eq(cvar([(F(0), F("0.8")), (F(2), F("0.15")),
                           (F(10), F("0.05"))], F("0.9")), 6))
    case("two_signed_excursion_cvar_levels", landscape, [16],
         lambda: eq([cvar([(F(str(z)), F(1, 10)) for z in
                           [-.6, -.5, -.4, -.3, -.2, -.1, 0, .2, .5, 1.5]], a)
                     for a in [F("0.75"), F("0.9")]], [F("0.84"), F("1.5")]))

    def gaussian():
        entries = []
        m, v = F(0), F(0)
        for t in range(1, 41):
            m, v = F(1, 2)*m + F(2, 5), F(1, 4)*v + F(1, 100)
            eq(m, F(4, 5)*(1-F(1, 2)**t))
            eq(v, F(1, 75)*(1-F(1, 4)**t))
            tail = .5*math.erfc(float((1-m))/math.sqrt(2*float(v)))
            entries.append({"t": t, "mean": str(m), "variance": str(v), "tail": tail})
        total = sum(e["tail"] for e in entries)
        eq(total, 1.4842304541271834, tolerance=2e-14)
        return {"terms": entries, "total": total, "markov_clipped": min(1, total)}
    case("gaussian_recursion_and_all40_marginals", landscape, [19], gaussian)

    lipsdp = "lipsdp.html"
    case("physical_sensor_box_and_scale", lipsdp, [1],
         lambda: {"sdp": eq(2*math.sqrt(4/3)*math.sqrt(2)*.02,
                            .06531972647421809, tolerance=1e-14),
                  "exact_box": eq(F("0.02") + 2*F("0.02"), F("0.06"))})
    case("coupled_relu_counterexample", lipsdp, [2],
         lambda: eq(mm(mm([[2, 0]], [[1, -1], [-1, 1]]), [[0], [1]])[0][0], -2))

    def tanh_maximum():
        r = math.tanh(1)
        p = r*r
        z = (-3*(1-p) + math.sqrt(9*(1-p)**2 + 4*p))/(2*p)
        u = math.sqrt(z)
        x = .5*math.log((1+u)/(1-u))
        rational = 4*r*(1-p)*u*(1-u*u)/(1-p*u*u)**2
        direct = abs(1/math.cosh(x+1)**2 - 1/math.cosh(x-1)**2)
        eq(rational, direct, tolerance=2e-14)
        eq(rational, .933492585138041, tolerance=2e-14)
        eq(1-3*(1-p)*z-p*z*z, 0, tolerance=1e-14)
        return {"x": x, "magnitude": direct, "stationary_polynomial": 1-3*(1-p)*z-p*z*z}
    case("globally_characterized_tanh_maximum", lipsdp, [17], tanh_maximum)

    def scalar_identity():
        rows = []
        for alpha, beta, w1 in [(F(0), F(1), F("-0.7")),
                                (F(1, 10), F(1), F(2)),
                                (F(1), F(2), F(-3))]:
            threshold = w1*w1/2
            tstar = beta*w1*w1/(beta-alpha)
            for t in [threshold+F(1, 100), tstar, tstar+2]:
                g = (alpha+beta)**2*t*t/(2*t-w1*w1)-2*alpha*beta*t
                gap = ((beta-alpha)*t-beta*w1*w1)**2/(2*t-w1*w1)
                eq(g-beta*beta*w1*w1, gap)
                assert gap >= 0
                if t == tstar:
                    eq(gap, 0)
            rows.append({"alpha": alpha, "beta": beta, "w1": w1, "tstar": tstar})
        return rows
    case("one_neuron_exact_square_identity", lipsdp, [19], scalar_identity)

    design = "lipschitz-by-design.html"
    case("target_gradient_and_six_stage_scale", design, [1, 2],
         lambda: {"target_norm": eq(math.hypot(.4, .002), .4000049999687504,
                                     tolerance=1e-14),
                  "stage_product": 1.002**6, "scale": .3/(1.002**6)})
    case("scalar_sandwich_multiplier_residuals", design, [9],
         lambda: eq([2*lam-F(72, 25)-lam*lam*F(8, 25) for lam in [F(4), F(2)]],
                    [0, F(-4, 25)]))
    case("implemented_truncation_and_depth", design, [13],
         lambda: {"single": math.sqrt(1.0004), "exact_depth": 1.0004**5,
                  "remainder_depth": (1+1/750)**10})
    case("sll_scaled_row_residuals", design, [16],
         lambda: eq([det2([[F(1), F(-1)], [F(-1), F(1)]]),
                     det2([[F(2), F(-1)], [F(-1), F(1, 2)]])], [0, 0]))
    case("two_tap_fir_peak_gain", design, [18],
         lambda: eq((math.sqrt(6)+math.sqrt(2))/4, .9659258262890682,
                    tolerance=1e-14))
    case("all_requested_raw_and_normalized_radii", design, [19],
         lambda: {"global": .9/math.sqrt(2), "pairwise": min(.9/1.2, 3.4/1.35),
                  "global_pixel": .9/(4*math.sqrt(2)), "pairwise_pixel": 3/16,
                  "levels": [36/255, 72/255]})
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--report", required=True)
    args = parser.parse_args()
    files = [Path(__file__).relative_to(ROOT).as_posix(),
             "book/solutions/solution_review.py",
             "book/solutions/baseline-source90/manifest.json"]
    for page, (draft, preservation) in SELECTED.items():
        files.extend(["book/solutions/drafts/" + draft + ".json",
                      "reports/solution-review/" + preservation + "-preservation.json",
                      "book/solutions/baseline-source90/pages/" + page + ".json"])
    before = [ref(f) for f in files]
    cases = run_cases()
    after = [ref(f) for f in files]
    errors = [c["case"] for c in cases if c["status"] != "passed"]
    if before != after:
        errors.append("protected_input_changed")
    report = {"status": "passed_selected_arithmetic_checks" if not errors else "failed_selected_arithmetic_checks",
              "command": [sys.executable, "-B", str(Path(__file__).relative_to(ROOT)),
                          "--report", args.report],
              "cwd": str(ROOT), "cases": cases, "passed": len(cases)-len([c for c in cases if c["status"] != "passed"]),
              "input_sha256_before": before, "input_sha256_after": after,
              "errors": errors,
              "scope": "Selected exact-fraction identities and recomputed numerical examples. Does not replace independent mathematical/pedagogical review or validated arithmetic for numerical certificates.",
              "canonical_or_authoring_sources_written": False}
    json_put(args.report, report)
    print(json.dumps({"status": report["status"], "passed": report["passed"], "cases": len(cases),
                      "errors": errors, "report": ref(args.report)}))
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())

