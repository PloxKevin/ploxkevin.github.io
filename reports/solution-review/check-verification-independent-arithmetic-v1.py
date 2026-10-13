"""Independent rational, rank, branch and quantile checks for both drafts."""
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
from statistics import NormalDist
import json
import math

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'reports/solution-review/verification-independent-arithmetic-v1.json'
assert not OUT.exists()
checks = []


def ref(file):
    return {'file': file, 'sha256': sha256((ROOT/file).read_bytes()).hexdigest()}


def exact(name, actual, expected):
    assert actual == expected, (name, actual, expected)
    checks.append({'name': name, 'status': 'passed_exact_fraction_calculation', 'value': str(actual)})


exact('new-domain worst temperature', F('59.7')+F('.3'), F(60))
exact('whole-trajectory temperature', F('59.35')+F('.3')+F('.32'), F('59.97'))
assert math.ceil(F('.99')*100) == 99 and math.ceil(F('.99')*99) == 99 > 98
checks.append({'name': 'minimal finite trajectory calibration size', 'status': 'passed_exact_ceiling_check',
               'n':99, 'rank':99, 'previous_n':98, 'previous_rank':99})
exact('class tie', 1-3*F(1,3), F(0))
exact('upper-line counterexample', 1-2*F(2,3)*(F(-1,2)+1), F(1,3))
exact('Euclidean affine attaining perturbation', 3*F('-.12')-4*F('.16'), F(-1))
exact('infinity affine attaining perturbation', 3*F('-.2')-4*F('.2'), F('-1.4'))
exact('conditional planner risk', F('.04')/F('.5'), F('.08'))
exact('unconditional planner safety lower bound', 1-F('.5')-F('.04'), F('.46'))
for n, expected in [(39,39), (19,20)]:
    actual = math.ceil((n+1)*F('.975'))
    assert actual == expected
    checks.append({'name':'per-time conformal rank n='+str(n), 'status':'passed_exact_ceiling_check', 'rank':actual})
Nhoeffding = math.log(100)/.02
assert math.ceil(Nhoeffding) == 231
checks.append({'name':'one-sided Hoeffding count', 'status':'passed_numeric_log_ceiling_check',
               'unrounded':Nhoeffding, 'integer':231})


def tail(n, dimension, probability):
    return sum(F(math.comb(n,i))*probability**i*(1-probability)**(n-i)
               for i in range(dimension))


for n, expected in [(60,False), (61,True)]:
    t = tail(n,3,F(1,10))
    assert (t <= F('.05')) == expected
    checks.append({'name':'scenario d3 exact tail n='+str(n), 'status':'passed_exact_rational_threshold_comparison',
                   'tail_float':float(t), 'meets_beta':expected})
for n, expected in [(642,False), (643,True)]:
    t = tail(n,10,F(1,20))
    assert (t <= F(1,1000000)) == expected
    checks.append({'name':'scenario d10 exact tail n='+str(n), 'status':'passed_exact_rational_threshold_comparison',
                   'tail_float':float(t), 'meets_beta':expected})
for n, expected in [(1395,False), (1396,True)]:
    t = F(math.comb(n,10))*F(19,20)**(n-10)
    assert (t <= F(1,1000000)) == expected
    checks.append({'name':'old scenario bound n='+str(n), 'status':'passed_exact_rational_threshold_comparison',
                   'bound_float':float(t), 'meets_beta':expected})
for n, expected in [(1137,False), (1138,True)]:
    t = tail(n,36,F(1,20))
    assert (t <= F('.001')) == expected
    checks.append({'name':'scenario d36 exact tail n='+str(n), 'status':'passed_exact_rational_threshold_comparison',
                   'tail_float':float(t), 'meets_beta':expected})
for name, raw, integer in [('d3 explicit count',20*(math.log(20)+3),120),
                           ('d10 explicit count',40*(math.log(1e6)+10),953),
                           ('paper count36 explicit',40*(math.log(1e3)+36),1717)]:
    assert math.ceil(raw) == integer
    checks.append({'name':name, 'status':'passed_numeric_log_ceiling_check', 'unrounded':raw, 'integer':integer})

# Independently enumerate exact vertices of the input box and its ReLU phase line.
# A continuous affine function on either closed polygon attains an extremum at a vertex.
def network(x,y):
    return -2*max(F(0),x+y+1)+2*max(F(0),-x+2*y+1)


for radius, expected in [(F(1,2),(F(-5),F(1))), (F(3,2),(F(-17,2),F(7)))]:
    lo,hi = 1-radius,1+radius
    candidates = {(x,y) for x in [lo,hi] for y in [lo,hi]}
    for x in [lo,hi]:
        y = (x-1)/2
        if lo <= y <= hi:
            candidates.add((x,y))
    for y in [lo,hi]:
        x = 2*y+1
        if lo <= x <= hi:
            candidates.add((x,y))
    values = [network(x,y) for x,y in candidates]
    assert (min(values),max(values)) == expected
    checks.append({'name':'exact CROWN-example phase vertices radius='+str(radius),
                   'status':'passed_exact_polygon_vertex_calculation',
                   'vertices':[{'input':[str(x),str(y)],'value':str(network(x,y))}
                               for x,y in sorted(candidates)], 'range':[str(z) for z in expected]})
for alpha, expected in [(F(0),F(-12)),(F(1,2),F(-17,2)),(F(1),F(-11))]:
    exact('alpha lower bound '+str(alpha), -9+alpha-F(3,2)*abs(4*alpha-2), expected)
exact('CROWN upper center', -F(31,9)+F(8,9)+F(55,18), F(1,2))
exact('CROWN upper extreme', F(1,2)+F(3,2)*F(13,3), F(7))
normal = NormalDist()
radius_a = .5*normal.inv_cdf(.95)
radius_b = .25*(normal.inv_cdf(.95)-normal.inv_cdf(.03))
pmax = math.exp(math.log(.001)/10000)
cap = .5*normal.inv_cdf(pmax)
assert .82 < radius_a < .8225 and .88 < radius_b < .8815
assert 1.59 < cap < 1.60
checks.append({'name':'smoothing exact-formula numeric comparison',
               'status':'passed_float_consistency_and_rounding_direction_check_not_formal_interval_certificate',
               'radius_a':radius_a, 'radius_b':radius_b, 'best_probability_lower_bound':pmax,
               'finite_sample_cap':cap,
               'displayed_rounded_quantile_results_are_approximations':True,
               'conservative_returned_choices':[.82,.88]})
report = {'status':'passed', 'errors':[], 'checks':checks,
          'source':ref('SafeLearning/verification.html'),
          'drafts':[ref('book/solutions/drafts/verification-thorough-solutions-v1.json'),
                    ref('book/solutions/drafts/verification-thorough-solutions-v2.json')],
          'helper':ref('reports/solution-review/check-verification-independent-arithmetic-v1.py'),
          'scope':'Exact rational threshold/branch checks and consistency of the supplied approximate transcendental values. No new empirical benchmark replication, formal rounding certificate, compiler or browser success is claimed.'}
OUT.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
notes_file = ROOT / 'reports/solution-review/verification-independent-notes-v1.json'
notes = json.loads(notes_file.read_text())
notes['independent_checks'] = [{'arithmetic_report':ref(str(OUT.relative_to(ROOT))), 'status':'passed', 'checks':len(checks)}]
notes_file.write_text(json.dumps(notes,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'file':str(OUT.relative_to(ROOT)), 'sha256':sha256(OUT.read_bytes()).hexdigest(),
                  'status':report['status'], 'checks':len(checks)}))
