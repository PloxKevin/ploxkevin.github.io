#!/usr/bin/env python3
"""Independent exact/numerical recomputation of the three connected projects.

These checks establish the listed calculations, not the model's empirical
validity or a distribution-free theorem. General deterministic claims have
separate, explicitly scoped Lean proofs.
"""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import math

ROOT = Path(__file__).resolve().parents[2]
checks = []


def equal(name, actual, expected):
    assert actual == expected, (name, actual, expected)
    checks.append(dict(name=name, actual=str(actual), expected=str(expected)))


def near(name, actual, expected):
    assert math.isclose(actual, expected, abs_tol=1e-12, rel_tol=1e-12), (name, actual, expected)
    checks.append(dict(name=name, actual=actual, expected=expected))


def safe_input(y, sensor=F(1, 10), disturbance=F(1, 5)):
    return max(-1, sensor + disturbance - y), min(1, 10 - sensor - disturbance - y)


# Project 1: derive extrema from the independent current-state and disturbance
# boxes, then compute the projection without reusing the authored formulas.
for label, y, nominal, selected, next_lo, next_hi in [
    ('worked', F(2, 5), -1, F(-1, 10), 0, F(3, 5)),
    ('B1', F(49, 5), F(7, 10), F(-1, 10), F(47, 5), 10),
]:
    lo, hi = safe_input(y)
    u = min(hi, max(lo, nominal))
    equal('tank ' + label + ' projected action', u, selected)
    extremes = [x + u + w for x in [y - F(1, 10), y + F(1, 10)]
                for w in [F(-1, 5), F(1, 5)]]
    equal('tank ' + label + ' lower next volume', min(extremes), next_lo)
    equal('tank ' + label + ' upper next volume', max(extremes), next_hi)
equal('tank worked correction', abs(F(-1, 10) - (-1)), F(9, 10))
for y in [F(-1, 10), F(101, 10)]:
    lo, hi = safe_input(y)
    equal('tank feasible at extreme reading ' + str(y), lo <= hi, True)
equal('tank B2 lower required action', F(1, 10) + F(6, 5) - F(-1, 10), F(7, 5))
equal('tank B2 exact empty tank required action', F(6, 5), F(6, 5))
equal('tank B3 lower-bound fixed input', -F(-1, 5), F(1, 5))
equal('tank B3 upper-bound fixed input', 10 - 10 - F(1, 5), F(-1, 5))
equal('tank B3 no single constant input', F(1, 5) <= F(-1, 5), False)


# Project 2: evaluate the lower envelope at endpoints and proposed queries.
def lower(x, anchor, observed, error, l=F(1, 2)):
    return observed - error - l * abs(x - anchor)


anchors = [(F(1, 5), F(9, 50)), (F(1, 2), F(7, 50))]
intervals = []
for (x, y), expected_r, expected_left, expected_right in zip(
        anchors, [F(8, 25), F(6, 25)], [0, F(13, 50)], [F(13, 25), F(37, 50)]):
    r = (y - F(1, 50)) / F(1, 2)
    equal('tuning radius at ' + str(x), r, expected_r)
    intervals.append((max(0, x-r), min(1, x+r)))
    equal('tuning clipped left at ' + str(x), intervals[-1][0], expected_left)
    equal('tuning clipped right at ' + str(x), intervals[-1][1], expected_right)
equal('tuning first bound at 0.6', lower(F(3, 5), *anchors[0], F(1, 50)), F(-1, 25))
equal('tuning first bound at 0.5', lower(F(1, 2), *anchors[0], F(1, 50)), F(1, 100))
equal('tuning intervals overlap', intervals[1][0] <= intervals[0][1], True)
equal('tuning union right endpoint', max(i[1] for i in intervals), F(37, 50))
noisy_r = (F(9, 50) - F(1, 20)) / F(1, 2)
equal('tuning B1 radius', noisy_r, F(13, 50))
equal('tuning B1 right endpoint', F(1, 5) + noisy_r, F(23, 50))
equal('tuning B1 bound at 0.5', lower(F(1, 2), *anchors[0], F(1, 20)), F(-1, 50))
equal('tuning B3 zero-L constant transfer', lower(F(99, 100), *anchors[0], F(1, 50), l=0), F(4, 25))


# Project 3: exact box support extrema, Euclidean norm and finite-sample rank.
a = (F(2), F(-1)); r = F(1, 5); gap = F(3, 5)
box_values = [gap + a[0]*d1 + a[1]*d2 for d1 in [-r, r] for d2 in [-r, r]]
equal('score box minimum', min(box_values), 0)
equal('score box minimizer value', gap + 2*(-r) - r, 0)
norm = math.hypot(*map(float, a))
near('score Euclidean minimum', float(gap) - float(r)*norm, 0.152786404500042)
near('score strict-radius supremum', float(gap)/norm, 0.2683281572999747)
equal('score B1 normalized first error', F(1, 10)/F(1, 2), r)
equal('score B1 normalized second error', F(2, 5)/2, r)


def ceil_fraction(x):
    return -(-x.numerator // x.denominator)


for alpha, expected in [(F(1, 10), 18), (F(1, 100), 20)]:
    equal('score conformal rank at alpha=' + str(alpha), ceil_fraction(20*(1-alpha)), expected)
scores = [F(i, 10) for i in range(1, 20)]
equal('score worked eighteenth score', scores[17], F(9, 5))
equal('score B2 rank unavailable', 20 > len(scores), True)
equal('score B3 union success lower bound', 1-4*F(1, 10), F(3, 5))
equal('score B3 independence product', F(9, 10)**4, F(6561, 10000))
equal('score B3 allocated failure', F(1, 10)/4, F(1, 40))

source = ROOT/'book/case-studies.html'
report = dict(status='passed', checks=checks, check_count=len(checks),
              source_sha256={str(source.relative_to(ROOT)): hashlib.sha256(source.read_bytes()).hexdigest()},
              limits=['Exact rational arithmetic and floating-point recomputations of constructed examples.',
                      'No empirical validation, browser rendering check or proof of exchangeability/coverage.'])
out = ROOT/'book/review/projects.json'
out.write_text(json.dumps(report, indent=2)+'\n')
print(f'Projects: {len(checks)} independent exact/numerical checks passed.')
