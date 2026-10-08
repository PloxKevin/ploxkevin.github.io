#!/usr/bin/env python3
"""Independent checks for the eleven module decision labs.

Run with the Python standard library: python3 book/checks/modules.py.
The checks use finite enumeration, exact rational matrix arithmetic, direct
piecewise optimization, and independent Bellman iteration where appropriate.
They are checks of the hypothetical models, not evidence about real hardware.
"""
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path
import json
import math
import re

ROOT = Path(__file__).resolve().parents[1]
REVIEW = json.loads((ROOT / 'review/modules.json').read_text())['chapters']
RESULTS = {}


def close(actual, expected, tolerance=1e-10):
    if isinstance(expected, list):
        assert len(actual) == len(expected), (actual, expected)
        for a, e in zip(actual, expected):
            close(a, e, tolerance)
    else:
        assert abs(actual - expected) <= tolerance * max(1, abs(expected)), (actual, expected)


def record(slug, computed, checks):
    expected = REVIEW[slug]['expected_results']
    assert computed.keys() == expected.keys(), (slug, computed.keys(), expected.keys())
    for name, value in computed.items():
        close(value, expected[name])
    RESULTS[slug] = {'checks': checks, 'expected_results': computed}


def transpose(a):
    return list(map(list, zip(*a)))


def mm(a, b):
    return [[sum(x*y for x, y in zip(row, col)) for col in zip(*b)] for row in a]


def mv(a, x):
    return [sum(u*v for u, v in zip(row, x)) for row in a]


def determinant(a):
    if len(a) == 1:
        return a[0][0]
    return sum((-1)**j * a[0][j] * determinant(
        [row[:j]+row[j+1:] for row in a[1:]]) for j in range(len(a)))


def principal_minors(a):
    return [determinant([[a[i][j] for j in ids] for i in ids])
            for n in range(1, len(a)+1) for ids in combinations(range(len(a)), n)]


# Module 1: Enumerate disturbance/input/state endpoints, and tail atoms.
means = [sum(p*t for p, t in law) for law in
         [[(.9, 58), (.1, 68)], [(1, 59)]]]
failure = [sum(p for p, t in law if t > 60) for law in
           [[(.9, 58), (.1, 68)], [(1, 59)]]]
thermal_endpoints = [.8*t+4+.5*u+w
                     for t, u, w in product([15, 60], [0, 12], [-1, 1])]
assert min(thermal_endpoints) >= 15 and max(thermal_endpoints) <= 60
fleet_budget = .05/20
close((1-fleet_budget)**20, .9511698752531668)
rare_law = [(F(98,100),59),(F(2,100),109)]
rare_mean = sum(p*t for p, t in rare_law)
# Check the RU objective at all atom breakpoints, not only a hand-picked tail.
cvar = min(F(nu) + sum(p*max(t-nu,0) for p,t in rare_law)/F(5,100)
           for nu in [59,109])
record('landscape', {'schedule_means':means,
    'schedule_failure_probabilities':failure,'six_independent_success':.99**6,
    'robust_next_interval':[min(thermal_endpoints),max(thermal_endpoints)],
    'fleet_budget':fleet_budget,'rare_mean':float(rare_mean),'rare_cvar':float(cvar)},
    ['exact atomic mean and RU tail minimization','monotone endpoint robust invariance',
     'six-batch and twenty-robot probability arithmetic'])

# Module 2: Construct Q from A, test PSD by exact principal minors.
A = [[F(6,10),F(1,10)],[F(1,10),F(7,10)]]
AtA = mm(transpose(A), A)
Q = [[F(i==j)-AtA[i][j] for j in range(2)] for i in range(2)]
assert all(m > 0 for m in principal_minors(Q))
trace = float(Q[0][0]+Q[1][1])
disc = math.sqrt(float((Q[0][0]-Q[1][1])**2+4*Q[0][1]**2))
eigen_Q = [(trace-disc)/2,(trace+disc)/2]
q = math.sqrt(1-eigen_Q[0])
xnext = mv(A,[F(6,10),F(-8,10)])
energy = sum(x*x for x in xnext)
startup_energy = max(a*a+b*b for a,b in product([-.7,.7],repeat=2))
close(q*math.sqrt(startup_energy), .7541468889856515)
R = .05/(1-q)
close(q*R+.05,R)
assert q+.05 < 1
# Persistent worst-case direction realizes R: derive the eigenvector separately.
v = [1.0,(q-.6)/.1]
nv = math.hypot(*v)
v = [a/nv for a in v]
close(mv(A,[R*a for a in v]),[q*R*a for a in v])
bad = [[.6,.6],[.6,.7]]
assert (1.3+math.sqrt(.1**2+4*.6**2))/2 > 1
record('toolkit-lmi',{'Q_eigenvalues':eigen_Q,'contraction':q,
    'next_state':list(map(float,xnext)),'next_energy':float(energy),
    'startup_max_energy':startup_energy,'disturbance_radius':R},
    ['exact matrix residual and positive principal minors','physical startup/next temperatures',
     'uniform rectangular startup bound','disturbance invariant radius and attaining direction',
     'off-diagonal coupling counterexample'])

# Module 3: GP calculations independently obtained by small Gaussian elimination.
def solve(a,b):
    a = [[F(v) for v in row]+[F(y)] for row,y in zip(a,b)]
    for i in range(len(a)):
        pivot = a[i][i]
        assert pivot != 0
        a[i] = [v/pivot for v in a[i]]
        for j in range(len(a)):
            if j != i:
                scale = a[j][i]
                a[j] = [x-scale*y for x,y in zip(a[j],a[i])]
    return [row[-1] for row in a]

kernel = [[4,2,3],[2,4,3],[3,3,4]]
assert all(m > 0 for m in principal_minors(kernel))
alpha = solve([[5,2],[2,5]],[2,0])
kv = [3,3]
mu = sum(a*b for a,b in zip(kv,alpha))
v = solve([[5,2],[2,5]],kv)
variance = 4-sum(a*b for a,b in zip(kv,v))
upper = float(mu)+2*math.sqrt(variance)
assert 57+upper > 60 and 56.5+upper < 60
repeated_alpha = solve([[5,4,4],[4,5,4],[4,4,5]],[2,2,2])
repeated_v = solve([[5,4,4],[4,5,4],[4,4,5]],[4,4,4])
repeated_mu = sum(4*a for a in repeated_alpha)
repeated_variance = 4-sum(4*a for a in repeated_v)
repeated_upper = float(repeated_mu)+2*math.sqrt(repeated_variance)
assert 57+repeated_upper < 60 < 56.5+upper+.4
record('toolkit-gp',{'alpha':list(map(float,alpha)),
    'midpoint_mean':float(mu),'midpoint_variance':float(variance),
    'midpoint_upper':upper,'nominal_with_bias_max':60-upper-.4,
    'repeated_upper':repeated_upper},
    ['augmented kernel PSD','posterior via exact elimination','latent variance and decision thresholds',
     'three-observation repeated-data solve','bounded discrepancy decision reversal'])

# Module 4: Set operations from their definitions, including optimistic witnesses.
D = [0,.5,1,1.5,2]
lower = dict(zip(D,[1.1,.7,.2,-.4,.1]))
upper_grid = dict(zip(D,[1.5,1.8,2.2,1.4,2.6]))
previous = [0,.5]
safe = [x for x in D if any(lower[z]-abs(x-z)>=-1e-12 for z in previous)]
maximizers = [x for x in safe if upper_grid[x] >= max(lower[z] for z in safe)]
expanders = [x for x in safe if any(upper_grid[x]-abs(x-z)>=0
                                  for z in D if z not in safe)]
assert maximizers == expanders == safe
widths = [upper_grid[x]-lower[x] for x in safe]
selected = max(set(maximizers+expanders),key=lambda x:upper_grid[x]-lower[x])
assert max(.2,.8)==.8 and min(2.2,1)==1
lower[1] = .8
next_safe = [x for x in D if any(lower[z]-abs(x-z)>=-1e-12 for z in safe)]
radius = min(.8/1,.12/.4)
close(.8-.4,.4); close(.12-.4*.4,-.04)
close(.12-.4*(.28+.04),-.008)
record('safe-bo',{'safe_grid':safe,'widths':widths,'selected_gain':selected,
    'next_safe_grid':next_safe,'multi_constraint_radius':radius,'command_radius':radius-.04},
    ['safe-set witness enumeration','maximizer and expander enumeration','acquisition widths',
     'interval intersection and following update','distinct-constraint units and actuator uncertainty'])

# Module 5: Cone geometry and finite-run probability budget.
r0 = (.95-.15)/.8
r1 = (.75-.15)/.8
intervals = [(-r0,r0),(.8-r1,.8+r1)]
assert intervals[0][1] >= intervals[1][0]
union = [intervals[0][0],max(b for a,b in intervals)]
candidate_margins = [max(y-.15-.8*abs(a-z) for z,y in [(0,.95),(.8,.75)])
                     for a in [1.4,1.7]]
E = .15*math.sqrt(2*math.log(2*100/.01))
close(100*2*math.exp(-E*E/(2*.15**2)),.01)
record('safe-bo-theory',{'first_radius':r0,'second_radius':r1,
    'safe_union':union,'candidate_margins':candidate_margins,
    'command_interval':[union[0]+.1,union[1]-.1],
    'gaussian_error_envelope':E,'gaussian_first_radius':(.95-E)/.8},
    ['two cone radii and union geometry','candidate witnesses','robust realized-gain containment',
     'conditional Gaussian-tail union budget and finite-run radius'])

# Module 6: Weighted distances retain velocity and timing units.
distance = lambda z,b:abs(z[0]-b[0])+.5*abs(z[1]-b[1])
center = (.8,.3)
reserve = .02+.8*.1
d = distance((.6,.4),center)
close(.6-.02-.08,.5)
assert d+reserve < .4 and distance((.5,.5),center)+reserve > .4
low = [distance((.4,.1),b) for b in [center,(.45,0)]]
high = [distance((.4,1),b) for b in [center,(.45,0)]]
assert low[0]+reserve > .4 and low[1]+reserve < .25
assert high[0]+reserve > .4 and high[1]+reserve > .25
record('gosafe',{'latency_reserve':reserve,'first_distance':d,
    'first_margin':.4-d-reserve,'late_state_distance':distance((.5,.5),center),
    'maximum_latency':(.4-d-.02)/.8,'library_distances_low_speed':low,
    'library_distances_high_speed':high},
    ['weighted state-space recovery tests','intersample clearance reserve',
     'maximum total latency','union of two backup certificates'])

# Module 7: Kernel fixed-point elimination and independent Bellman optimization.
def transitions(t):
    return [('R',t+2)]+([('C',t-4)] if t<60 else [])

def kernel(states):
    current = set(states)
    rounds = []
    while True:
        reduced = {t for t in current if any(n in current for a,n in transitions(t))}
        rounds.append(sorted(reduced))
        if reduced == current:
            return sorted(current),rounds
        current = reduced

viable, rounds = kernel([52,54,56,58,60])
relaxed, relaxed_rounds = kernel([52,54,56,58,60,62])
assert len(rounds)==2 and len(relaxed_rounds)==3
counts = [sum(n in viable for a,n in transitions(t)) for t in viable]

def reward(t,a):
    return 0 if a=='C' else (25 if t==58 else 3)

def bellman(gamma, penalty, safe_only):
    states = viable if safe_only else [52,54,56,58,60]
    v = {t:0.0 for t in states}
    for _ in range(10000):
        w = {t:max(reward(t,a)+(gamma*v[n] if n in states else -penalty)
                     for a,n in transitions(t) if not safe_only or n in states)
             for t in states}
        if max(abs(w[t]-v[t]) for t in states)<1e-12:
            return w
        v = w
    raise AssertionError('Bellman contraction did not converge')

vs09 = bellman(.9,0,True)[58]
vs08 = bellman(.8,0,True)[58]
close(vs09,5.13/.271)
close(vs08,4.32/.488)
close(bellman(.9,5,False)[58],23.2)
threshold = (27.4-vs08)/.8
close(bellman(.8,24,False)[58],vs08)
close(25+.8*(3-threshold),vs08)
assert 25+.8*(3-24) < vs08
record('viability',{'viability_kernel':viable,'viable_action_counts':counts,
    'safe_value_09':vs09,'unsafe_p5':25+.9*(3-5),'relaxed_kernel':relaxed,
    'safe_value_08':vs08,'strict_penalty_threshold_08':threshold},
    ['iterated viability kernel including relaxed cap','viable-action counts',
     'independent safe/full Bellman value iteration','strict penalty threshold and unsafe tie'])

# Module 12: Exact rational certificate plus independent pattern optimization.
W0 = [[F(1),F(2)],[F(1),F(-2)]]
W1 = [[F(1,2),F(1,2)]]
T = [[F(1,3),F(0)],[F(0),F(1,3)]]
cross = mm(transpose(W0),T)
out = mm(transpose(W1),W1)
M = [[F(-4,3),F(0)]+cross[0], [F(0),F(-4,3)]+cross[1]]
M += [list(cross[j][i] for j in range(2)) +
       [out[i][j]-2*T[i][j] for j in range(2)] for i in range(2)]
minus_M = [[-v for v in row] for row in M]
assert all(m>=0 for m in principal_minors(minus_M))
# Characteristic polynomial at the claimed eigenvalues and rank certify spectrum.
for eigen in [F(-2),F(-3,2),F(0)]:
    assert determinant([[M[i][j]-eigen*F(i==j) for j in range(4)]
                        for i in range(4)])==0
assert sum(M[i][i] for i in range(4))==F(-7,2)
pattern_norms = []
for d1,d2 in product([0,1],repeat=2):
    gradient = [F(d1+d2,2),F(d1-d2)]
    pattern_norms.append(math.hypot(*gradient))
exact_L = max(pattern_norms)
# Every pattern has an explicit strictly feasible input witness.
for point,pattern in [((-1,0),(0,0)),((0,1),(1,0)),((0,-1),(0,1)),((1,0),(1,1))]:
    assert tuple(int(v>0) for v in mv(W0,point))==pattern
physical = 2*math.sqrt(F(4,3))*.04
hardware = 2*math.sqrt(F(4,3))*math.hypot(.02,.02)
assert physical < .1 < .16 and hardware > .06
physical_gradients = [[2*a for a in [F(d1+d2,2),F(d1-d2)]]
                      for d1,d2 in product([0,1],repeat=2)]
exact_box_error = .02*max(sum(abs(a) for a in grad) for grad in physical_gradients)
close(exact_box_error,.06)
# A one-active-region witness attains the box bound without crossing a kink.
correction = lambda x,y:max(x+2*y,0)+max(x-2*y,0)
close(correction(.02,1.02)-correction(0,1),exact_box_error)
close(.06/hardware,.9185586535436918)
coupled = [[1,-1],[-1,1]]
dv = [1,1]; dz = [1,0]
qc = 2*sum(a*b for a,b in zip(dz,mv(coupled,[a-b for a,b in zip(dv,dz)])))
record('lipsdp',{'product_bound':2,'rho':4/3,'certificate_eigenvalues':[-2,-1.5,0,0],
    'exact_lipschitz':exact_L,'physical_error_bound':physical,
    'hardware_error_bound':hardware,'invalid_coupled_qc':qc,
    'exact_hardware_box_error':float(exact_box_error)},
    ['all exact principal minors of negative SDP residual','certificate characteristic roots',
     'all activation gradients and region witnesses','preprocessing and physical error budgets',
     'exact hardware-box support and attaining witness',
     'coupled incremental-QC counterexample'])

# Module 13: Orthogonality, physical target direction, and numerical gain reserve.
Cayley = [[F(3,5),F(-4,5)],[F(4,5),F(3,5)]]
assert mm(transpose(Cayley),Cayley)==[[1,0],[0,1]]
radius = math.hypot(.2/10,.003/.1)
gain = .3
underestimate = (2/1.9)**4
assert gain*radius < .012 < gain*radius*underestimate
target_grad = math.hypot(.04*10,.02*.1)
assert target_grad > gain
scale = gain/1.002**6
close(scale*1.002**6,gain)
record('lipschitz-by-design',{'normalized_error_radius':radius,'velocity_error':gain*radius,
    'underestimate_stack_gain':underestimate,'target_gradient_norm':target_grad,
    'six_stage_scale':scale},
    ['exact Cayley instance orthogonality','sensor-box radius and output scale',
     'spectral-underestimate budget violation','target gradient incompatibility',
     'six-stage operator-error allowance'])

# Module 14: Analytic derivative interval, direct boundary and state-history tests.
Floop = lambda e:.9*e-.3*math.tanh(e)
next_error = Floop(.4)
close(next_error**2,.060523533405565426)
assert .9*.5+.02 <= .5
close(.02/(1-.9),.2)
actuator = 1.5*math.tanh(.5)
assert actuator < .8
assert .9*.5+.029 < .5 and 1.5*math.tanh(.53) < .8
complex_root = complex(.45,math.sqrt(.3-.45**2))
close(abs(complex_root),math.sqrt(.3))
close(complex_root**2-.9*complex_root+.3,0)
delayed_next = .9*.5-.3*(-.5)
assert delayed_next > .5 and 1.5*.5 < .8
record('nn-in-the-loop',{'closed_loop_derivative_interval':[.6,.9],
    'invariant_boundary_bound':.9*.5+.02,'ultimate_error':.02/(1-.9),
    'actuator_bound':actuator,'nominal_next_error':next_error,
    'biased_ultimate_error':.029/(1-.9),'delayed_eigenvalue_magnitude':abs(complex_root),
    'delayed_counterexample_next_error':delayed_next},
    ['analytic tanh derivative interval','disturbance/state/input containment',
     'starting temperature and storage change','sensor-bias bound',
     'delay characteristic roots and physically admissible noninvariance witness'])

# Module 15: A piecewise-affine function reaches extrema at endpoints/breakpoints.
network = lambda z:max(z+.2,0)-2*max(z-.1,0)
def exact_range(lo,hi):
    points = [lo,hi]+[z for z in [-.2,.1] if lo<=z<=hi]
    values = [network(z) for z in points]
    return [min(values),max(values)]
exact = exact_range(-.3,.4)
close([network(-.3),network(.4)],[0,0])
assert network(.1) > network(-.3)
scores = [i/100 for i in range(1,17)]+[.22,.24,.30]
order = math.ceil(20*.9)
quantile = sorted(scores)[order-1]
assert len(scores)==19 and quantile==.24
minimum = next(n for n in range(1,1000) if math.ceil(F(99,100)*(n+1))<=n)
close(.99*(minimum+1),minimum)
assert 59.65+exact[1]+quantile > 60
record('verification',{'ibp_range':[-2*.3,.6],'exact_range':exact,
    'deterministic_temperature_upper':59.65+exact[1],'conformal_order':order,
    'conformal_quantile':quantile,'revised_nominal_max':60-exact[1]-quantile,
    'revised_domain_range':exact_range(-.1,.5),'trajectory_calibration_minimum':minimum,
    'trajectory_temperature_upper':59.35+exact[1]+.32},
    ['exact piecewise-linear extrema at all breakpoints','interval-relaxation comparison',
     'endpoint-only counterexample','calibration order and quantile',
     'minimum finite trajectory calibration size and joint margin'])

# Structural checks ensure each independently checked calculation has its fragment.
assert len(RESULTS)==11
for slug,review in REVIEW.items():
    html = (ROOT/review['fragment']).read_text()
    assert html.startswith('<section class="book-chapter" id="book-lab">')
    assert html.count('<li>')==3
    assert '<script' not in html and '<html' not in html
    assert html.count('Show hint')==html.count('Show worked solution')==2
    for exercise_id in review['exercise_ids']:
        assert html.count(f'id="{exercise_id}"')==1
    words = len(re.findall(r'\S+',re.sub(r'<[^>]+>',' ',html)))
    assert words==review['words'] and 700<=words<=1100,(slug,words)
    assert html.count('$')%2==0
    RESULTS[slug]['words']=words

print(json.dumps({'status':'PASS','chapters_checked':len(RESULTS),
                  'verification':RESULTS},indent=2))
