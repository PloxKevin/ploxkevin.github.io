"""Record Root's independent reading and recomputed checks of all34 selections."""
import hashlib
import json
import math
from datetime import datetime,timezone
from fractions import Fraction as F
from pathlib import Path

ROOT=Path(__file__).resolve().parents[3]
def ref(p):return {'file':p,'sha256':hashlib.sha256((ROOT/p).read_bytes()).hexdigest()}
draft='book/solutions/drafts/primer-optimization-detailed-v1.json'
baseline='book/solutions/baseline-source90/pages/primer-optimization.html.json'
d=json.loads((ROOT/draft).read_bytes());b=json.loads((ROOT/baseline).read_bytes())
selected={e['inventory_key']:e for e in d['exercises']}
notes=[
'Coordinate partials, Hessian and directional dot product are correct; each derivative and the local interpretation is explicit.',
'Both differentiation routes give -2t-4t^3; the answer evaluates the state margin as well as its slope and limits the claim to the local change.',
'The Taylor factors and numerical model are correct, with a positive scalar third-derivative remainder and actual error inside its bound.',
'The least-squares gradient and diagonal Hessian agree with the scalar expansion; zero residual plus invertibility establishes unique global optimality.',
'The local determinant bound establishes the differentiation domain; trace and scalar determinant slopes agree, and the inverse derivative preserves multiplication order.',
'The differentiated system, explicit rational solution and exact positive 1/5050 finite prediction error agree.',
'The interval bound is attained in the limit of chords, the global chord slope is unbounded, and the derivative has exact Lipschitz constant2.',
'The grid covering radii and dimension factor correctly transfer the sample margins; the integer endpoint-compatible spacing and non-certification distinction are sound.',
'The geometric recurrence, both requested values and both Lipschitz margin transfers are correct; scalar dynamics attain the state-error bound.',
'The interval and disc proofs cover every pair and convex weight, while the isolated set has an explicit missing midpoint.',
'Both Hessian eigenvalues establish the convexity range and strong-convexity boundary; the subgradient proof checks both signs and sufficiency.',
'The constrained conjugate handles negative slopes separately and verifies both requested Fenchel–Young equalities at their proper maximizers.',
'Every gradient factor and iterate is correct; the strict step-size convergence interval explains zero, alternating and divergent cases.',
'The Newton solve reaches the unique PD quadratic optimum; the scalar gradient step and remaining first-coordinate error are computed explicitly.',
'The Newton slope is negative, the first two trials violate the domain, and the quarter-step satisfies the explicitly evaluated Armijo inequality.',
'Both inequality conventions, endpoint versus interior minimizers and all four KKT conditions are correctly verified; convexity supports global uniqueness.',
'The guessed active set is independently checked; multipliers cancel the gradient, and the exact quadratic displacement proof verifies unique global optimality.',
'The penalty branches are compared at their actual minima and junction; feasibility is separated from exact primal/dual and approximate KKT residuals.',
'The QP factors, omitted constant and signed constraint rows are correct; the zero-error point is feasible and unique.',
'All polygon vertices and objective values agree; the whole-set inequality proves the optimum and its uniqueness.',
'The half-space projection violates the box, the coupled candidate satisfies all bounds and correct-sign multipliers, and the larger requirement is proved infeasible.',
'The open-domain supremum is not attained, the approximate point is admissible, and the closed quadratic has precisely two maximizers.',
'The two-constraint minima correctly distinguish safe controllers and the max-min choice; the largest-single-margin rule fails a hard constraint.',
'Both optimization orders and every saddle inequality are explicit; the maximizing player cannot be replaced by separate minimization.',
'The transfer expansion, allowed interval, optimum and cost are correct; a checked multiplier establishes optimality over the entire triangle.',
'The full active-set formula, endpoints of its strict validity range, values at both budgets and exact quadratic price correction are correct.',
'The reported point has exact primal violation despite its small stationarity residual; the minimum-Euclidean repair and weighted cost gap are computed correctly.',
'Taking the minimum disturbance before solving produces the correct robust interval and multiplier; the old command fails and existence is equivalent to d<=0.2.',
'Every partial derivative, indefinite-Hessian witness and Taylor model is correct; the exact omitted cubic/exponential terms explain the reported errors.',
'The differential includes both W factors and the Frobenius-gradient orientation; direct multiplication verifies the finite-step objective decrease.',
'All cone radii/endpoints and interval unions are correct; the compatible maximum-cone functions justify why the gaps cannot be certified for either modulus.',
'The quadratic conjugate square completion and the restricted scalar branches attain their suprema; both Fenchel–Young gaps are correct.',
'Both coordinate recurrences, integer step counts and adjacent objective checks agree; the divergent steep coordinate and one-step Newton result are explained.',
'The sequential projection is infeasible, whereas the active-set solution has valid positive multipliers and a direct whole-feasible-set optimality proof.'
]
assert len(notes)==len(b['exercises'])==len(selected)==34
checks=[]
def check(label,actual,expected,tol=1e-12):
    assert abs(float(actual)-float(expected))<=tol,label
    checks.append({'calculation':label,'computed':str(actual),'expected':str(expected),'passed':True})
check('System sensitivity prediction error',F(2,1)/F(101,100)-F(198,100),F(1,5050))
check('Recurrence step5',F(1,20)*(F(6,5)**5-1),F('0.074416'))
check('Recurrence step6',F(1,20)*(F(6,5)**6-1),F('0.0992992'))
check('Step6 margin',F(1,5)-2*F('0.0992992'),F('0.0014016'))
check('Penalty objective at5/4',F(-3,4)**2+3*F(1,4)**2,F(3,4))
check('Approximate KKT complementarity',F('2.2')*F('0.1'),F('0.22'))
check('Allocation price correction',F('0.9')-F('0.784'),F('0.116'))
check('Repaired allocation gap',F(1,2)*(F('0.005')**2+4*F('0.005')**2),F('0.0000625'))
check('Robust command',math.sqrt(2.7)-1,0.6431676725,1e-9)
check('Robust cost',0.5*(2-math.sqrt(2.7))**2,0.063664655,1e-9)
check('Robust multiplier',(2-math.sqrt(2.7))/(0.2*math.sqrt(2.7)),1.085806195,1e-9)
check('Orthogonal regularizer after step',F(1,4)*(F('0.45')**2+2*F('0.63')**2+F('0.18')**2),F('0.257175'))
assert 50*0.81**84>1e-6>=50*0.81**85
assert 55*(81/121)**44>1e-6>=55*(81/121)**45
checks.append({'calculation':'Both gradient iteration counts check the preceding integer and first acceptable integer','steps':[85,45],'passed':True})
rows=[]
for e,n in zip(b['exercises'],notes):
    s=selected[e['inventory_key']]
    assert s['original_solution_sha256']==e['solution']['sha256']
    body=s['replacement_html'] if s['decision']=='replace' else e['solution']['html']
    rows.append({'inventory_key':e['inventory_key'],'ordinal':e['ordinal'],'decision':s['decision'],
                 'original_solution_sha256':e['solution']['sha256'],
                 'selected_solution_sha256':hashlib.sha256(body.encode()).hexdigest(),
                 'verdict':'approved','reasoning':n,'all_requested_parts_addressed':True,
                 'mathematics_and_assumptions_checked':True,'reader_depth_checked':True,'issues':[]})
report={'schema_version':1,'status':'approved_all34_selected_solutions','reviewer':'/root independent of recovery_runner35 author',
        'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'draft':ref(draft),'baseline':ref(baseline),
        'page_contract':ref('page_contract.md'),'criteria':ref('book/solutions/README.md'),
        'method':'Independent full reading of every question and selected answer, relevant optimization definitions and the authored lab; algebra, conditions, every requested subpart and pedagogical reasons checked. Preservation is supported by the separate exact-byte adapter report.',
        'preservation':ref('reports/solution-review/primer-optimization-detailed-v1-preservation.json'),
        'candidate_files':[ref('book/solutions/candidates/primer-optimization-detailed-v1/'+p) for p in ['SafeLearning/primer-optimization.html','book/chapters/primer-optimization.html']],
        'counts':{'exercises':34,'approved':34,'replace':19,'retain':15},'exercises':rows,
        'independent_numerical_checks':checks,'issues':[],
        'scope':'Pedagogical and mathematical review of these selected HTML solutions, not a new kernel-verification or physical-model claim.'}
out=ROOT/'reports/solution-review/primer-optimization-independent-review-v1.json'
assert not out.exists();out.write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'report':ref(str(out.relative_to(ROOT))),'approved':34,'independent_calculations':len(checks)}))
