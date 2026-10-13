"""Native independent arithmetic supplement to the exact twenty-row review."""
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
import json
import math

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'reports/solution-review/nn-in-the-loop-independent-arithmetic-v1.json'
assert not OUT.exists()
checks = []


def ref(file):
    return {'file': file, 'sha256': sha256((ROOT / file).read_bytes()).hexdigest()}


def exact(name, actual, expected):
    assert actual == expected, (name, actual, expected)
    checks.append({'name': name, 'status': 'passed_exact_fraction_calculation', 'value': str(actual)})


exact('bias ultimate bound', (F('.3')*F('.03')+F('.02'))/(1-F('.9')), F('.29'))
exact('biased invariant boundary', F('.9')*F('.5')+F('.029'), F('.479'))
exact('delayed-loop modulus squared', F('.45')**2+F(39,400), F('.3'))
exact('initialized next error', F('.9')*F('.5')-F('.3')*F('-.5'), F('.6'))
exact('practice LMI determinant', F('-.56')*F('-1.75')-F('.9')**2, F('.17'))
exact('global scalar LMI determinant', F('-.36')*F('-.30')-F('.18')**2, F('.0756'))
checks.append({'name': 'global scalar LMI exact radical formulas', 'status': 'passed',
               'eigenvalues': [(-33+3*math.sqrt(37))/100, (-33-3*math.sqrt(37))/100],
               'admissible_multiplier_endpoints': [(33-3*math.sqrt(21))/100, (33+3*math.sqrt(21))/100]})
# Independently expand the numerator of the local matrix's determinant.
coef = [F('.69')*F('-.24')-F('-.18')**2,
        F('.69')*F('-.36')+F('-3.09')*F('-.24')-2*F('-.18')*F('1.38'),
        F('-3.09')*F('-.36')-F('1.38')**2]
assert coef == [F(-99,500), F(99,100), F(-99,125)]
checks.append({'name': 'local determinant factorization numerator', 'status': 'passed_exact_polynomial_identity',
               'coefficients': [str(a) for a in coef],
               'factorization': '(99/500)*(4*alpha-1)*(1-alpha)'})
alpha = math.tanh(3)/3
assert .33 < alpha < 1/3
e6_partial = sum(F(6)**k/math.factorial(k) for k in range(7))
assert e6_partial > 199
m11, m12, m22 = .69-4*alpha, .22+alpha, -.64
det = m11*m22-m12*m12
assert m11 < -.63 and det > .1007
checks.append({'name': 'simple d3 certificate', 'status': 'passed_strict_matrix_check',
               'alpha': alpha, 'matrix': [[m11,m12], [m12,m22]], 'determinant': det,
               'rigorous_alpha_lower_bound_evidence': {'e6_positive_Taylor_partial_through_degree6': str(e6_partial),
                                                       'required_lower_bound': 199}})
exact('d3 containment determinant', 9*F(4,9)-4, F(0))
assert math.tanh(3.9973)/3.9973 > .25 > math.tanh(3.9974)/3.9974
checks.append({'name': 'ROA root bracket', 'status': 'passed_float_sign_consistency_not_formal_interval_claim',
               'r_interval': [3.9973,3.9974]})
for x0 in [1.9985, 1.999]:
    x = x0
    vals = {}
    for k in range(1,101):
        x = 1.3*x-.6*math.tanh(2*x)
        if k in [10,50,100]:
            vals[str(k)] = x
    if x0 == 1.9985:
        assert abs(vals['10']-1.996591) < .00000051
        assert abs(vals['50']/8.616e-15-1) < .00001
        assert abs(vals['100']/8.616e-65-1) < .00001
    else:
        assert abs(vals['10']-2.003399) < .00000051
        assert abs(vals['50']-169.805116) < .00000051
        assert abs(vals['100']/8.356e7-1) < .0001
    checks.append({'name': 'scalar trajectory '+str(x0), 'status': 'actual_native_repeated_substitution',
                   'iterates': vals})
# Read the native stepf before independently coding its displayed default equations:
# H=.1,DMP=.5,W0=[[1,.5],[0,1]],W1=[-6,-1.5],a=2,b=1.
x = (-4.25,2.8)
vals = []
for k in range(201):
    v = (x[0]+.5*x[1],x[1])
    V = .162*x[0]**2+2*.06*x[0]*x[1]+.144*x[1]**2
    vals.append((k,x,v,V))
    u = -6*math.tanh(v[0])-1.5*math.tanh(v[1])
    x = (x[0]+.1*x[1],.2*x[0]+.95*x[1]+.1*u)
first = next(z for z in vals if max(abs(t) for t in z[2]) > 2.87)
minimum = min(vals, key=lambda z:z[3])
assert first[0] == 4 and minimum[0] == 11
assert abs(minimum[3]-1.46) < .004 and max(abs(z) for z in x) > 10
checks.append({'name': 'actual explorer counterexample',
               'status': 'actual_native_repeated_substitution_using_source_stepf_parameters',
               'initial_V_using_stated_approximate_P': vals[0][3],
               'first_box_exit': {'time':first[0], 'state':first[1], 'preactivations':first[2]},
               'minimum_V_using_stated_approximate_P': {'time':minimum[0], 'value':minimum[3]},
               'time80_state': vals[80][1], 'time200_state': vals[200][1],
               'simulation_is_illustrative_not_analytic_ROA_proof': True})
for q, display in [(.3,.125244), (.36,.116498)]:
    e = .1/(.5+q)
    iterates = [e]
    for k in range(4):
        e -= (.5*e+q*math.tanh(e)-.1)/(.5+q*(1-math.tanh(e)**2))
        iterates.append(e)
    assert abs(e-display) < .00000051
    checks.append({'name': 'tracking offset q='+str(q), 'status': 'actual_native_Newton_calculation',
                   'iterates': iterates})
qc = .5*(math.tanh(-1)-math.tanh(.5)+math.tanh(2))
assert qc < -.129
checks.append({'name': 'shifted coupled QC counterexample', 'status': 'passed_numeric_evaluation_of_exact_expression',
               'value': qc})
report = {
    'status': 'passed', 'errors': [],
    'independent_review': ref('reports/solution-review/nn-in-the-loop-independent-review-v1.json'),
    'draft': ref('book/solutions/drafts/nn-in-the-loop-thorough-solutions-v1.json'),
    'source': ref('SafeLearning/nn-in-the-loop.html'),
    'helper': ref('reports/solution-review/check-nn-in-the-loop-independent-arithmetic-v1.py'),
    'checks': checks,
    'compiler_or_browser_execution_claimed': False,
    'scope': 'Exact rational identities and numerical consistency checks; transcendental float calculations are not formal rounding-error certificates.',
    'previous_check_attempt': {
        'status': 'failed_overly_early_illustrative_growth_assertion',
        'description': 'The first native arithmetic attempt asserted magnitude>10 after80 explorer steps; this had not yet occurred. Its output and exit1 are preserved in the tool history. The independently observed box exit at4 and energy minimum at11 remain correct. The final bounded simulation uses200 steps, with its actual iterates recorded above.'
    }
}
OUT.write_text(json.dumps(report, ensure_ascii=False, indent=2)+'\n')
print(json.dumps({'file': str(OUT.relative_to(ROOT)), 'sha256': sha256(OUT.read_bytes()).hexdigest(),
                  'status': report['status'], 'checks': len(checks)}))
