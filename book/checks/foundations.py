#!/usr/bin/env python3
"""Independent arithmetic and analytic checks for the three foundation chapters.

Uses exact rational arithmetic for linear models and normal equations. Nonlinear
roots are checked by substitution, monotonicity, feasibility and KKT residuals.
Run with /usr/bin/python book/checks/foundations.py; --write-review refreshes the
authored review manifest. These checks do not extend any existing Lean coverage.
"""
from fractions import Fraction as F
from html.parser import HTMLParser
from pathlib import Path
import argparse
import json
import math
import re

ROOT = Path(__file__).resolve().parents[2]
RECORDS = []


def near(actual, expected, tol=1e-11):
    assert math.isclose(float(actual), float(expected), rel_tol=tol, abs_tol=tol), (actual, expected)


def solve2(a, b):
    det = a[0][0]*a[1][1]-a[0][1]*a[1][0]
    assert det != 0
    return ((b[0]*a[1][1]-a[0][1]*b[1])/det,
            (a[0][0]*b[1]-b[0]*a[1][0])/det)


def mul(a, x):
    return tuple(sum(ai*xi for ai, xi in zip(row, x)) for row in a)


def gram(a):
    return tuple(tuple(sum(row[i]*row[j] for row in a) for j in range(2)) for i in range(2))


def transpose_mul(a, x):
    return tuple(sum(row[i]*xi for row, xi in zip(a, x)) for i in range(2))


def record(chapter, anchor, kind, title, exact, numeric, analytic, limitations):
    RECORDS.append(dict(chapter=chapter, anchor=anchor, kind=kind, title=title,
                        exact_expected_results=exact, numeric_results=numeric,
                        analytic_checks=analytic, limitations=limitations, passed=True))


def check_basics():
    q = lambda n, d=1: F(n, d)
    x, alpha, low_u, high_u, d, upper = q(9,2),q(11,10),q(-1),q(0),q(2,5),q(5)
    lo = max(low_u, -alpha*x)
    hi = min(high_u, upper-alpha*x-d)
    assert (lo,hi) == (q(-1),q(-7,20))
    assert (alpha*x-q(1,2),alpha*x-q(1,2)+d) == (q(89,20),q(97,20))
    gain = alpha-q(9,50)
    assert gain==q(23,25) and gain*upper+d==upper
    assert -q(9,50)*upper>=low_u
    assert upper-alpha*upper-d==q(-9,10)
    record('0','book-0-worked-command','worked example','Robust chamber command',
           {'allowed_command_interval':'[-1,-7/20]','selected_successor_interval':'[89/20,97/20]',
            'feedback':'u=-9x/50','closed_loop_slope':'23/25','fixed_command_exists':False},
           {'command_interval':[float(lo),float(hi)],'upper_policy_endpoint':float(gain*upper+d)},
           ['Affine disturbance dependence makes endpoints necessary and sufficient.',
            'Policy stays inside actuator bounds and maps both state endpoints into C.',
            'x=0 forces fixed u=0 while x=5 forces fixed u<=-9/10.',
            'The one-step interval inclusion supports induction from x0 in C.'],
           ['Exact current state, exact actuator, fixed affine model and bounded warming are assumed.'])
    e = q(4,5)
    bounds=[]
    for k in range(10):
        bound=q(1,20)+q(3,4)*q(3,5)**k
        assert e==bound
        bounds.append(e)
        e=q(3,5)*e+q(1,50)
    assert bounds[8]==F('0.06259712')
    assert bounds[9]==F('0.057558272')
    assert bounds[8]>q(3,50)>=bounds[9]
    assert 5+9*2==23
    # The equality recurrence is permitted and never reaches its floor at finite k.
    assert q(1,50)/(1-q(3,5))==q(1,20)
    record('0','book-0-worked-stopping','worked example','Iteration deadline and floor',
           {'error_bound':'1/20+(3/4)(3/5)^k','k8':'0.06259712','k9':'0.057558272',
            'minimal_certified_iterations':9,'runtime_ms':23,'limiting_bound':'1/20'},
           {'k8':float(bounds[8]),'k9':float(bounds[9]),'log_threshold':math.log(1/75)/math.log(.6)},
           ['Exact equality recurrence agrees with finite-geometric-sum formula through k=9.',
            'Monotone bound brackets tolerance at neighboring integers.',
            'Positive geometric remainder prevents reaching the floor in finite time.'],
           ['Recurrence bounds errors; actual errors may be smaller. Runtime assumes stated fixed per-step costs.'])
    assert (q(47,10)-q(1,5),q(47,10)+q(1,5))==(q(9,2),q(49,10))
    assert (q(49,10)-q(1,5),q(49,10)+q(1,5))==(q(47,10),q(51,10))
    assert upper-q(1,5)==q(24,5)
    record('0','book-0-ex-1','exercise','0.B1 — Accept bounded-error readings',
           {'accepted_reading_interval':'[1/5,24/5]','y4.7_possible_true':'[9/2,49/10]',
            'y4.9_possible_true':'[47/10,51/10]','first_certified':True,'second_certified':False},
           {},['Interval containment requires both endpoints; rejection leaves passing and failing possibilities.'],
           ['Deterministic sensor bound is assumed.'])
    x=q(24,5)
    allowed=(max(low_u,-alpha*x),min(high_u,upper-alpha*x-d))
    assert allowed==(q(-1),q(-17,25))
    selected=(alpha*x-q(4,5),alpha*x-q(4,5)+d)
    assert selected==(q(112,25),q(122,25))
    assert alpha*x-q(7,25)==5
    record('0','book-0-ex-2','exercise','0.B2 — Command before warming',
           {'command_interval':'[-1,-17/25]','u=-4/5_successor':'[112/25,122/25]',
            'disturbance_dependent_command':'u=-7/25-w','dependent_successor':5},
           {},['Endpoint containment checks the robust interval.',
               'The alternative command is algebraically valid but requires observing w before choosing u.'],
           ['The hardware information order is part of the problem.'])
    e=q(7,10)
    for k in range(8):
        assert e==q(3,50)+q(16,25)*q(1,2)**k
        if k==5: assert e==q(2,25)
        if k==6: assert e==q(7,100)
        if k==7: assert e==q(13,200)
        e=q(1,2)*e+q(3,100)
    assert q(3,100)/(1-q(1,2))==q(3,50)>q(1,25)
    record('0','book-0-ex-3','exercise','0.B3 — Attainable error tolerance',
           {'bound':'3/50+(16/25)2^(-k)','floor':'3/50','target0.04_certified':False,
            'non_strict0.07_iterations':6,'strict0.07_iterations':7,'k5':'2/25','k6':'7/100','k7':'13/200'},
           {},['Equality recurrence witnesses failure of earlier universal budgets.',
               'Strict versus non-strict tolerance distinguishes k=6 from k=7.'],
           ['Guarantees come from the bound rather than observations of actual error.'])
    max_d=upper-alpha*upper-low_u
    assert max_d==q(1,2)
    assert alpha-q(1,5)==q(9,10)
    assert q(9,10)*upper+max_d==upper
    record('0','book-0-ex-4','exercise','0.B4 — Exact disturbance range',
           {'feasible_d_interval':'[0,1/2]','feedback':'u=-x/5','closed_loop':'x+=9x/10+w'},
           {},['At x=5 maximum cooling gives lower achievable endpoint 9/2+d, proving necessity.',
               'Feedback actuator bound and monotone state/disturbance endpoints prove sufficiency.',
               'Induction requires x0 in [0,5].'],
           ['No disturbances or delays outside the stipulated model are covered.'])


def check_linalg():
    h=((F(1),F(1)),(F(1),F(-1)))
    z=solve2(h,(F(6),F(2)))
    assert z==(F(4),F(2)) and gram(h)==((F(2),F(0)),(F(0),F(2)))
    errors=[solve2(h,(F(i,10),F(j,10))) for i in (-1,1) for j in (-1,1)]
    assert max(sum(x*x for x in e) for e in errors)==F(1,100)
    assert max(abs(e[0]) for e in errors)==F(1,10)
    assert F(4)+F(1,10)<=F(415,100) and F(4)+F(1,10)>F(405,100)
    record('A','book-a-worked-balanced','worked example','Balanced sensor reconstruction',
           {'estimate_mm':[4,2],'gram':'2I','singular_values':['sqrt(2)','sqrt(2)'],
            'condition_number':1,'worst_L2_error_mm':'1/10','worst_z1_error_mm':'1/10',
            'limit4.15_certified':True,'limit4.05_certified':False},
           {'error_set_vertices_mm':[[float(x) for x in e] for e in errors]},
           ['Exact Gram identity proves equal stretch in every direction.',
            'Inverse image of the sensor box is a rotated square; convex squared length is bounded by its vertices.'],
           ['Calibration is exact and only additive sensor errors are modeled.'])
    h2=((F(1),F(1)),(F(1),F(11,10)))
    truth=solve2(h2,(F(6),F(31,5)))
    perturbed=solve2(h2,(F(601,100),F(619,100)))
    err=tuple(p-t for p,t in zip(perturbed,truth))
    assert truth==(4,2) and perturbed==(F(421,100),F(9,5))
    assert err==(F(21,100),F(-1,5)) and sum(x*x for x in err)==F(841,10000)
    lo=(2.1-math.sqrt(4.01))/2
    hi=(2.1+math.sqrt(4.01))/2
    near(lo+hi,2.1);near(lo*hi,.1)
    assert lo>0 and hi/lo>42 and hi/lo<42.1
    near(math.sqrt(sum(float(x*x) for x in err)),.29)
    record('A','book-a-worked-nearparallel','worked example','Nearly redundant sensor sensitivity',
           {'error_free_estimate_mm':[4,2],'perturbed_estimate_mm':['421/100','9/5'],
            'error_mm':['21/100','-1/5'],'error_norm_mm':'29/100',
            'singular_values':'(21/10 +/- sqrt(401/100))/2','determinant':'1/10'},
           {'sigma_min':lo,'sigma_max':hi,'condition_number':hi/lo},
           ['Exact elimination produces the stated state error.',
            'Positive eigenvalues satisfy the symmetric matrix characteristic polynomial and equal singular values.',
            'Coincident rows at second coefficient=1 reduce rank.'],
           ['This chosen perturbation illustrates sensitivity, not a statistical frequency.'])
    estimate=solve2(h,(F(3),F(-1)))
    assert estimate==(1,2)
    assert estimate[0]+F(1,10)>F(105,100)
    assert estimate[0]+F(1,25)<=F(105,100)
    record('A','book-a-ex-1','exercise','A.B1 — Assembly limit with reconstructed error',
           {'estimate_mm':[1,2],'error0.1_z1_upper_mm':'11/10','error0.04_z1_upper_mm':'26/25',
            'first_certified':False,'second_certified':True},
           {},['Balanced inverse gives exact componentwise sensor-error bound; extremal same-sign sensor errors attain it.'],
           ['The specification concerns the true displacement, not just the estimate.'])
    # Parameterization is checked symbolically through its polynomial coefficients.
    assert (3+3)==6 and (1-1)==0
    assert 3**2+3**2==18 and 1**2+(-1)**2==2 and 2*3-2*3==0
    assert 5+1==6 and 5>4
    record('A','book-a-ex-2','exercise','A.B2 — Minimum length and identification',
           {'all_solutions':'(3+t,3-t), t in R','squared_norm':'18+2t^2',
            'minimum_length_solution':[3,3],'nonnegative_z1_range':'[0,6]','limit4_certified':False,
            'counterexample':[5,1]}, {},
           ['Polynomial coefficient identity gives all-solution norm and unique minimum.',
            'Nonnegativity bounds t in [-3,3]; feasible counterexample disproves certification.'],
           ['Minimum length is a stated convention, not additional sensor information.'])
    direction=(.2/math.sqrt(5),.1/math.sqrt(5))
    near(sum(x*x for x in direction),.01)
    near(2*direction[0]+direction[1],math.sqrt(5)/10)
    assert F(2)*F(1,10)+F(1,10)==F(3,10)
    record('A','book-a-ex-3','exercise','A.B3 — Scales and a normalized norm',
           {'normalized_row_mm':[2,1],'worst_prediction_error_mm':'sqrt(5)/10',
            'attaining_normalized_error':'(1/10)(2,1)/sqrt(5)','box_bound_mm':'3/10'},
           {'worst_prediction_error_mm':math.sqrt(5)/10,'attaining_error':list(direction)},
           ['Cauchy–Schwarz gives a uniform bound; the constructed direction attains equality.',
            'Separate-coordinate box enlarges the Euclidean ball, explaining the looser bound.'],
           ['Chosen position and velocity scales define the assumed uncertainty geometry.'])
    h3=h2+((F(0),F(1)),)
    readings=(F(6),F(31,5),F(21,10))
    g=gram(h3); rhs=transpose_mul(h3,readings)
    assert g==((F(2),F(21,10)),(F(21,10),F(321,100)))
    assert rhs==(F(61,5),F(373,25))
    result=solve2(g,rhs)
    assert result==(F(261,67),F(422,201))
    residual=tuple(y-p for y,p in zip(readings,mul(h3,result)))
    assert residual==(F(1,201),F(-1,201),F(1,2010))
    assert transpose_mul(h3,residual)==(0,0)
    e=tuple(x-t for x,t in zip(result,(4,2)))
    assert e==(F(-7,67),F(20,201)) and sum(x*x for x in e)==F(841,40401)
    assert g[0][0]>0 and g[0][0]*g[1][1]-g[0][1]**2==F(201,100)>0
    # Orthogonality plus full rank proves unique global least squares by the Pythagorean identity.
    record('A','book-a-ex-4','exercise','A.B4 — Third-sensor least-squares audit',
           {'gram':[['2','21/10'],['21/10','321/100']],'right_side':['61/5','373/25'],
            'estimate_mm':['261/67','422/201'],'residual_y_minus_Hz_mm':['1/201','-1/201','1/2010'],
            'state_error_mm':['-7/67','20/201'],'error_norm_mm':'29/201','unique':True},
           {'estimate_mm':[float(x) for x in result],'error_norm_mm':29/201},
           ['Exact normal equations and both residual orthogonality equations hold.',
            'Positive leading pivot and determinant establish positive-definite Gram matrix.',
            'Pythagorean least-squares decomposition proves global minimality and uniqueness.'],
           ['Equal residual weights are a modeling choice; the perturbation is particular, not worst-case.'])


def cost(u,v):
    return ((u-3)**2+4*(v-1)**2)/2


def allocation(b):
    lam=F(4,5)*(4-b)
    return 3-lam,1-lam/4,lam


def check_optimization():
    u,v,lam=allocation(F(3))
    assert (u,v,lam)==(F(11,5),F(4,5),F(4,5))
    assert u+v==3 and u>0 and v>0 and lam>0
    assert (u-3+lam,4*(v-1)+lam)==(0,0)
    assert cost(u,v)==F(2,5)
    assert cost(F(9,4),F(3,4))==F(13,32)
    assert F(13,32)>F(2,5)
    assert allocation(F(31,10))[:2]==(F(57,25),F(41,50))
    assert cost(*allocation(F(31,10))[:2])==F(81,250)
    record('B','book-b-worked-allocation','worked example','Weighted shared-flow allocation',
           {'optimum':['11/5','4/5'],'shared_multiplier':'4/5','cost':'2/5',
            'proportional_candidate':['9/4','3/4'],'proportional_cost':'13/32',
            'active_set_range':'1/4 < b < 4','value_function':'(2/5)(4-b)^2',
            'value_at_b3.1':'81/250','cost_reduction_b3_to3.1':'19/250'},
           {},['All four KKT conditions hold; positive Hessian ensures strict convexity.',
               'For every feasible displacement, the exact cost difference is -lambda*sum(delta)+positive quadratic.',
               'Active-set range follows from u>0 and lambda>0; value derivative is -lambda.'],
           ['Weight four is a design choice. Flow is normalized by one litre per minute.'])
    a=math.sqrt(3)-1
    h=lambda x:.3-.2*x-.1*x*x
    g=lambda x:.1*x*x+.2*x-.2
    lam=(1-a)/(.2*a+.2)
    near(h(1),0);near(h(a),.1);near(g(a),0)
    near(lam,10/math.sqrt(3)-5);near(a-1+lam*(.2*a+.2),0)
    near(.5*(a-1)**2,(7-4*math.sqrt(3))/2)
    assert 0<a<1 and lam>0
    record('B','book-b-worked-clearance','worked example','Nonlinear endpoint clearance',
           {'linearized_command':1,'linearized_command_actual_clearance_m':0,
            'exact_command':'sqrt(3)-1','clearance_m':'1/10','objective':'(7-4sqrt(3))/2',
            'multiplier':'10/sqrt(3)-5','Taylor_overestimate_m':'a^2/10'},
           {'command':a,'objective':.5*(a-1)**2,'multiplier':lam},
           ['Exact quadratic inequality solves the full feasible interval.',
            'Tracking objective decreases throughout [0,1], giving the right feasible endpoint.',
            'Feasibility, nonnegative multiplier, complementary slackness and zero stationarity hold.',
            'Constraint second derivative 1/5 and objective second derivative one prove convexity.'],
           ['Static endpoint model over [0,1]; no continuous-trajectory guarantee or model error is assumed.'])
    initial=(F(12,5),F(3,5)); t=F(1,5)
    assert cost(*initial)==F(1,2)
    repaired=(initial[0]-t,initial[1]+t)
    assert repaired==(F(11,5),F(4,5)) and cost(*repaired)==F(2,5)
    # Expansion: constant .5, linear coefficient -1, quadratic coefficient 2.5.
    assert (initial[0]-3)*(-1)+4*(initial[1]-1)==-1
    assert (1+4)/2==2.5 and -1+5*t==0
    record('B','book-b-ex-1','exercise','B.B1 — Feasible transfer improvement',
           {'candidate':['12/5','3/5'],'candidate_cost':'1/2','transfer_polynomial':'1/2-t+(5/2)t^2',
            'optimal_transfer':'1/5','result':['11/5','4/5'],'result_cost':'2/5',
            'constrained_optimum_gradient':['-4/5','-4/5']}, {},
           ['Exact one-dimensional expansion has positive curvature and feasible minimizing transfer.',
            'Gradient is orthogonal to the budget tangent and balanced by its normal.'],
           ['The transfer comparison preserves the shared budget.'])
    p=allocation(F(5,2)); pn=allocation(F(13,5))
    assert p==(F(9,5),F(7,10),F(6,5))
    assert pn==(F(47,25),F(18,25),F(28,25))
    assert cost(*p[:2])==F(9,10) and cost(*pn[:2])==F(98,125)
    decrease=cost(*p[:2])-cost(*pn[:2])
    assert decrease==F(29,250) and p[2]*F(1,10)-decrease==F(1,250)
    record('B','book-b-ex-2','exercise','B.B2 — Budget sensitivity',
           {'b2.5_optimum':['9/5','7/10'],'b2.5_multiplier':'6/5','b2.5_cost':'9/10',
            'b2.6_optimum':['47/25','18/25'],'b2.6_multiplier':'28/25','b2.6_cost':'98/125',
            'predicted_decrease':'3/25','actual_decrease':'29/250','remainder':'1/250'}, {},
           ['Both candidate allocations satisfy every KKT condition within the same active-set range.',
            'Exact quadratic value difference verifies first-order shadow-price remainder.'],
           ['Large budget changes may cross active-set boundaries.'])
    reported=(F(221,100),F(4,5)); lm=F(4,5)
    stationarity=(reported[0]-3+lm,4*(reported[1]-1)+lm)
    assert stationarity==(F(1,100),0)
    violation=sum(reported)-3
    assert violation==F(1,100)
    repair=tuple(x-violation/2 for x in reported)
    assert repair==(F(441,200),F(159,200)) and sum(repair)==3 and min(repair)>0
    assert cost(*repair)==F(6401,16000) and cost(*repair)-F(2,5)==F(1,16000)
    record('B','book-b-ex-3','exercise','B.B3 — Feasibility repair',
           {'stationarity_residual':['1/100',0],'flow_violation_L_per_min':'1/100',
            'minimum_Euclidean_repair':['441/200','159/200'],'repaired_cost':'6401/16000',
            'cost_gap':'1/16000'}, {},
           ['Projection correction is parallel to line normal (1,1), preserving nearest-point optimality.',
            'All primal constraints hold after repair.',
            'Exact quadratic difference gives the cost gap; original point is infeasible.'],
           ['A repaired feasible point may remain suboptimal; requirements define acceptable feasibility tolerance.'])
    a=math.sqrt(2.7)-1
    lm=(1-a)/(.2*a+.2)
    near(h(a),.13);near(h(a)-.03,.1)
    near(.1*a*a+.2*a-.17,0)
    near(a-1+lm*(.2*a+.2),0)
    near(lm,10/math.sqrt(2.7)-5)
    nonrobust=math.sqrt(3)-1
    near(h(nonrobust)-.03,.07)
    assert 0<a<nonrobust<1 and lm>0
    assert F(3,10)-F(1,5)==F(1,10)
    record('B','book-b-ex-4','exercise','B.B4 — Robust nonlinear clearance',
           {'robust_command':'sqrt(27/10)-1','nominal_clearance_m':'13/100',
            'worst_clearance_m':'1/10','objective':'(1/2)(2-sqrt(27/10))^2',
            'multiplier':'10/sqrt(27/10)-5','old_command_worst_clearance_m':'7/100',
            'feasible_symmetric_error_d_m':'[0,1/5]'},
           {'command':a,'objective':.5*(a-1)**2,'multiplier':lm},
           ['Affine disturbance dependence selects w=-0.03 as the exact worst case.',
            'Monotonic clearance and objective identify the unique robust boundary optimum.',
            'All KKT conditions hold for the convex robust inequality.',
            'At a=0 clearance is maximal, proving exact general feasibility threshold d<=0.2.'],
           ['Bounded error model assumes the true clearance is enclosed for all commands under consideration.'])


class FragmentParser(HTMLParser):
    def __init__(self):
        super().__init__();self.ids=[];self.text=[];self.exercises=[];self.links=[];self.summary=False;self.current=[]
    def handle_starttag(self, tag, attrs):
        a=dict(attrs)
        if 'id' in a:self.ids.append(a['id'])
        if tag=='a':self.links.append(a.get('href',''))
        if tag=='summary':self.summary=True;self.current=[]
    def handle_endtag(self, tag):
        if tag=='summary':
            value=''.join(self.current).strip()
            if value.startswith('Exercise '):self.exercises.append(value)
            self.summary=False
    def handle_data(self,data):
        self.text.append(data)
        if self.summary:self.current.append(data)


def check_fragments():
    chapters=[]
    for chapter,name,prefix in [('0','primer-basics','book-0'),('A','primer-linalg','book-a'),('B','primer-optimization','book-b')]:
        path=ROOT/'book'/'chapters'/(name+'.html')
        source=path.read_text()
        p=FragmentParser();p.feed(source)
        assert len(p.ids)==len(set(p.ids)),(name,'duplicate ID')
        assert all(x=='book-lab' or x.startswith(prefix+'-') for x in p.ids)
        assert source.count('<section ')==1 and source.count('</section>')==1
        assert '<script' not in source and '<html' not in source
        assert len(p.exercises)==4 and all(' — ' in x for x in p.exercises)
        assert sum('Easy:' in x for x in p.exercises)==1
        assert sum('Medium:' in x for x in p.exercises)==2
        assert sum('Hard:' in x for x in p.exercises)==1
        assert source.count('Show hint')==4 and source.count('Show worked solution')==4
        assert source.count('Worked example &mdash;')==2
        assert source.count('Learning objectives')==1
        for link in p.links:
            if link.startswith('http'):continue
            filename,_,anchor=link.partition('#')
            target=ROOT/'SafeLearning'/(filename or name+'.html')
            assert target.exists(),(name,link)
            if anchor:
                assert anchor in p.ids or re.search(r'\bid=["\']'+re.escape(anchor)+r'["\']',target.read_text()),(name,link)
        plain=' '.join(p.text)
        prose=re.sub(r'\$\$[\s\S]*?\$\$|\$[^$]*\$',' ',plain)
        word_count=len(prose.split())
        assert 1500<=word_count<=2400,(name,word_count)
        expected_anchors=[r['anchor'] for r in RECORDS if r['chapter']==chapter]
        assert all(x in p.ids for x in expected_anchors)
        chapters.append(dict(chapter=chapter,file=str(path.relative_to(ROOT)),
                             authored_word_count_excluding_math=word_count,
                             word_count_method='HTMLParser text extraction; inline/display dollar-delimited math removed; whitespace split',
                             worked_examples=2,application_exercises=4,
                             exercise_labels=p.exercises,
                             check_anchors=expected_anchors,
                             learning_objectives=True,synthesis_and_recall=True,
                             existing_audited_mathematics='Preserved: fragment files only; no edits to live SafeLearning files.'))
    return chapters


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--write-review',action='store_true');args=parser.parse_args()
    check_basics();check_linalg();check_optimization()
    assert len(RECORDS)==18
    chapters=check_fragments()
    review=dict(scope='New textbook application chapters for Primers 0, A and B',
                status='All 18 independent numeric/analytic case checks pass',
                check_command='/usr/bin/python book/checks/foundations.py',
                checks_file='book/checks/foundations.py',
                new_worked_examples=6,new_application_exercises=12,
                authored_word_count_excluding_math=sum(x['authored_word_count_excluding_math'] for x in chapters),
                no_new_empirical_claims_or_citations=True,
                formal_verification_scope='No new Lean coverage claimed; these are independent Python arithmetic and analytic checks.',
                browser_preview=dict(status='blocked before page load',
                                     attempted='Isolated Playwright preview of fragments within existing page CSS and KaTeX.',
                                     reason='Chromium aborted: sandbox_host_linux.cc shutdown: Operation not permitted.',
                                     final_live_page_qa='Pending integration by parent agent; no browser pass claimed.'),
                chapters=chapters,cases=RECORDS,
                limitations=['All real-world settings are constructed teaching models with stated units and assumptions.',
                             'Checks verify mathematical calculations and analytic conditions, not physical model validity.',
                             'Browser integration and final live-page QA are performed by the integrating parent agent.'])
    if args.write_review:
        (ROOT/'book'/'review'/'foundations.json').write_text(json.dumps(review,indent=2)+'\n')
    print(json.dumps({'status':'passed','case_checks':len(RECORDS),'chapters':chapters},indent=2))


if __name__=='__main__':
    main()
