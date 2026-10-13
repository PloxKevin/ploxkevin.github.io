"""Independent bounded review: preserve canonical files; bind all fifty verdicts."""
from collections import Counter
from datetime import datetime, timezone
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
import json
import math
import re

ROOT = Path(__file__).resolve().parents[2]
DRAFT = 'book/solutions/drafts/primer-basics-thorough-solutions-v1.json'
BASELINE = 'book/solutions/baseline-source90/pages/primer-basics.html.json'
OUT = 'reports/solution-review/primer-basics-independent-review-v1.json'


def digest(data):
    return sha256(data).hexdigest()


def ref(file):
    p = ROOT / file
    return {'file': file, 'sha256': digest(p.read_bytes()), 'bytes': p.stat().st_size}


# These are independent assessments after reading the full question, hint,
# original solution and proposed solution for every row. They are deliberately
# separate from the author's rationale and are not inferred from text length.
NOTES = {
    1: ('The six squares are 4,1,0,1,4,9; A excludes only 3, B contains the positive inputs, and 3 disproves B subset A.', 'The retained answer supplies both complete sets, the equality-endpoint membership test, and the exact counterexample to inclusion.'),
    2: ('Union 0,2,3,4; intersection 2,4; difference 0; complement 1,3,5 in the stated finite universe.', 'The retained answer explains each selection operation and why the universe restricts the complement.'),
    3: ('Nonnegative real squares make the first claim true and the second false; y=x+2 witnesses the third, and choosing x=y defeats any shared witness in the fourth.', 'Every truth value has the appropriate universal reasoning, dependent witness or contradiction; quantifier order is explained.'),
    4: ('Negations are exists x with x squared below 1, and for every x exists y with x<=y; x=0 and y=x verify the falsity of both originals.', 'The retained solution keeps both domains, swaps every quantifier, handles strictness correctly and supplies the needed witnesses.'),
    5: ('The original implication is true on x>3; x=-4 refutes the converse; x squared<=9 implies x<=3 for the contrapositive.', 'The implication, converse and contrapositive are individually assessed, and the necessity/sufficiency classification follows from those assessments.'),
    6: ('The largest interval is A1, yielding union [-1,1]; zero lies in every Ak and any nonzero x is excluded when k>1/abs(x).', 'Both set equalities have inclusion reasoning and the nonzero exclusion is a genuine arbitrary-input argument.'),
    7: ('The complement of [-1,2] is the two open exterior intervals; negating the conjunction is equivalent to either strict endpoint failure.', 'The retained membership equivalence proves both inclusions at once and explicitly accounts for excluded endpoints.'),
    8: ('Allowed inputs are {L},{R},{L,R}; dependent choices exist, neither fixed input works, and the negation of the first statement is false.', 'Each state and each possible fixed input is checked, and the fully quantified negation is explained rather than merely asserted.'),
    9: ('Cancellation forces u=-x. The endpoint x=1 makes a>=1 necessary; this condition also suffices for all x. The two endpoints prohibit a shared input for any a.', 'The retained proof separates necessity, sufficiency and the fixed-input contradiction with legal witness bounds.'),
    10: ('The image is {0,1,4}; -1 and 1 collide, and the declared codomain element 9 is not reached.', 'All input evaluations are present and each failed mapping property has an explicit witness tied to its definition.'),
    11: ('Composition gives 7 versus 9 at input 2, and formulas 2x squared-1 versus 4x squared-4x+1.', 'The retained solution displays the intermediate outputs in each order and the general polynomial expansion.'),
    12: ('The fixed point is 1; iterates 1/2,7/8,31/32 have errors 1/2,1/8,1/32 from an initial error of 2.', 'Each substitution and the identity g(x)-1=(x-1)/4 explain the exact quarter-error ratio.'),
    13: ('The image is [0,9], the [1,4] preimage has both signed branches [-2,-1] and [1,2], and the negative singleton preimage is empty.', 'The replacement proves both image inclusions with a square-root witness, solves both sign branches and explains preimage versus inverse.'),
    14: ('The four classifications are neither, surjective only, injective only, and bijective. The last inverse is the nonnegative square root.', 'The replacement states the tests, proves nonnegative-input uniqueness by factorization and checks both inverse identities with their domain condition.'),
    15: ('The fixed point is 2; the first iterates are 3,3/2,9/4; exact error is 2/2^k and first target index is 8.', 'The replacement shows the signed recurrence, contraction for an arbitrary pair, power-of-two target and the neighbouring failed budget.'),
    16: ('In the example the image of the empty intersection is empty while both images contain 4; injectivity supplies the reverse inclusion generally.', 'The retained solution provides the numerical failure and full arbitrary-output proofs of both inclusions, identifying the exact use of injectivity.'),
    17: ('The iterates are {0,1}, {0,1,2}, then unchanged. Monotonicity follows from image inclusion; the separate 3-4 cycle is unreachable from the seed.', 'Every iteration displays its source and image, stabilization implies later equality, and the general inclusion proof is complete.'),
    18: ('The cases respectively fail closedness, the self-map condition, and strict contraction. Fixed points are absent in the first two domains and zero exists in the third.', 'The retained answer audits each assumption, solves each fixed-point equation separately and describes the 1,-1 cycle without overreading theorem failure.'),
    19: ('Completing the square yields (x+1) squared+1>=1, with equality only at x=-1.', 'The retained answer explains the algebraic identity, square nonnegativity and arbitrary-real scope.'),
    20: ('An odd integer 2m+1 has square 2(2m squared+2m)+1 and therefore cannot have an even square.', 'The retained solution states the contrapositive, expands every algebraic step and checks integrality of the odd-form coefficient.'),
    21: ('The counterexamples x=1/2, (x,y)=(0,1), and (-1,1) respectively refute the three universal claims.', 'Every counterexample checks the true premise and false conclusion; the universal/existential proof distinction is explained.'),
    22: ('The empty-sum base case and adding n+1 give the sum formula at every nonnegative integer.', 'The retained induction labels base, hypothesis, step and conclusion and identifies the role of each equality.'),
    23: ('At a=-3,b=-2 the actual products give 9>=6>=4, while 9<=4 is false; nonnegative multipliers repair the chain.', 'The replacement demonstrates both erroneous directions and independently verifies the factorization repair, including zero multipliers.'),
    24: ('The map sends [0,1] into [1/4,3/4]. Current membership yields next membership, with the initial-state assumption supplying the base.', 'The retained solution contains the one-step bound, full induction structure and a concrete initially unsafe counterexample.'),
    25: ('For two hypothetical fixed points, d<=d/3 and d>=0 force d=0. The self-map x/3 on (0,1] has no fixed point in its domain.', 'The retained proof establishes only uniqueness, and its checked counterexample explains why existence needs an additional hypothesis.'),
    26: ('The quantitative bound implies current membership before the local map inequality is applied, so induction proves both decay and invariance.', 'The retained solution repairs the actual circularity and shows every inequality in the simultaneous bound/membership argument.'),
    27: ('The concrete states are a,b,c,b,c. A repeated state in a fixed four-state deterministic map gives identical futures, so all visited states occur by time 3.', 'The retained answer proves the general finite horizon using pigeonhole and fixed-map repetition and supplies a time-varying counterexample with failure at time 4.'),
    28: ('The first terms are 3,3/2,1,3/4 and limit zero; strict tolerance first holds at T=30, with a29 exactly 0.1.', 'The retained answer solves the strict integer inequality and verifies the every-later-index quantifier and preceding failure.'),
    29: ('The absolute return bound is 4; four constant-reward terms sum to 15/4 with tail 1/4. The least universal tail budget is 9 terms.', 'The replacement establishes absolute convergence, shows omitted-index accounting and proves minimality using an attaining allowed reward sequence.'),
    30: ('Telescoping bounds the nonnegative squared-norm sum by 6. This yields norm convergence and at most 150 excursions at threshold 0.2.', 'The replacement proves the all-time count through a finite-horizon contradiction and exhibits an arbitrarily late excursion satisfying every hypothesis.'),
    31: ('A has infimum -2 without a minimum and maximum/supremum 3; B has minimum/infimum 0 and unattained supremum 1.', 'The replacement distinguishes bounds from membership, gives approaching witnesses and explicitly produces a smaller/larger member when extrema fail.'),
    32: ('This sequence is (-1)^t+1/(t+1): its supremum is attained 2, its infimum is unattained -1, and its tail limits are 1 and -1.', 'The replacement derives parity formulas and computes tail suprema/infima, so the limsup statement is justified independently of the initial maximum.'),
    33: ('Row maxima are 2 and 1, producing min-max 1; column minima are 0 and 0, producing max-min 0.', 'The retained solution evaluates every inner choice and explains the response advantage and strict gap.'),
    34: ('The interval has interior (-1,1), closure [-1,1] and boundary {-1,1}; it is bounded but neither open nor closed nor compact. The finite two-point set is compact.', 'The replacement constructs neighbourhood radii and missing-limit witnesses, then verifies the two-point complement is open rather than merely calling the set closed.'),
    35: ('The three domains respectively have no minimizer, minimizer zero under compact-domain EVT, and minimizer zero by a direct bound on noncompact R.', 'The retained solution checks each domain, separates sufficient theorem conditions from necessity and uses a concrete approaching sequence for nonattainment.'),
    36: ('Fine-grid coverage radius 0.1 yields margin 0.05; coarse radius 0.2 yields only -0.25, and the distance-based function actually attains this negative value.', 'The replacement proves the distance function is 1-Lipschitz in both directions and verifies all samples and the unsafe midpoint, distinguishing a weak bound from a counterexample.'),
    37: ('For n>=1, 2n squared<=f(n)<=6n squared; f(n)/n squared tends to 2, ruling out little-o.', 'The retained solution supplies constants and threshold, bounds each lower-order term and explicitly checks the little-o ratio.'),
    38: ('The sufficient budgets are 1600 iterations/160000 operations for A and 80 iterations/80000 operations for B.', 'The retained answer solves both target inequalities, includes per-iteration costs and limits the comparison to the stated sufficient bounds.'),
    39: ('Average regret is at most 5 ln(T)/sqrt(T), which tends to zero and is about 0.46052 at 10000. Two sqrt(T) sequences refute the product little-o claim.', 'The replacement proves the logarithmic limit using the stated calculus background, supplies numerical substitutions and evaluates the product against the correct scale.'),
    40: ('The two reading intervals are [4.5,4.9] and [4.7,5.1]; full acceptance is [0.2,4.8] conditional on the sensor bound.', 'The replacement derives the information interval and both containment inequalities, then exhibits a compatible safe and unsafe true value for the rejected reading.'),
    41: ('At x=4.8, robust successors lie in [5.28+u,5.68+u], giving legal commands [-1,-0.68]; u=-0.8 yields [4.48,4.88].', 'The replacement solves containment before actuator intersection and substitutes the disturbance-dependent proposal to expose its changed quantifier/timing order.'),
    42: ('The shifted recurrence gives e_k<=0.06+0.64/2^k. It cannot universally guarantee 0.04; budgets 6 and 7 handle non-strict and strict 0.07.', 'The replacement gives a complete shifted induction and an allowed equality sequence establishing non-certification/minimality rather than treating the envelope as a lower bound.'),
    43: ('At x=5,w=d, any legal command gives x+>=4.5+d, so d<=0.5 is necessary. Feedback -0.2x supplies sufficiency for every 0<=d<=0.5.', 'The replacement verifies actuator legality, both successor bounds and the all-time induction with explicit initial-state and per-step disturbance assumptions.'),
    44: ('Negation swaps both quantifiers and interval membership; u=-x proves the statewise claim, and endpoints force incompatible fixed-command bounds u<=-1 and u>=1.', 'The replacement covers all four parts, checks the legal feedback witness, explains strict endpoint failure and describes the closed-loop consequence.'),
    45: ('Exact grid iteration with error 0.5 stabilizes at {0,1,2} after two increases; zero-error iteration reaches {0,...,7}. The lost 1-to-3 slack is 0.3.', 'The replacement uses only previous-round witnesses, computes each relevant radius, verifies stabilization and explains gateway loss within the certificate scope.'),
    46: ('Induction proves the finite geometric formula for gamma!=1; nonnegative double summation gives gamma/(1-gamma)^2 for 0<=gamma<1. At 0.9 the sum is 90 and normalized mean is 9.', 'The replacement labels the induction and common-denominator algebra, explains the finite-triangle/supremum justification for reordering and derives normalized probabilities.'),
    47: ('The four results are: range bounds 0 and unattained 1; signed-bracket sequence extrema 2 and -3/2 with tail limits +/-1; sine-plus-cosine supremum sqrt(2); both bilinear minimax values zero.', 'The replacement distinguishes the two similar parity exercises, checks attainment, derives the trigonometric identity and shows every sign-dependent optimizing response and saddle-point property.'),
    48: ('The exponential has unattained infimum zero; the polynomial minimum is -1/4 at 1/2; constrained norm minimum is 1/2 at (1/2,1/2); the linear maximum is unbounded; sublevel sets are compact exactly for c<1 including empty negative cases.', 'Every subpart has an approaching sequence, attaining witness or unbounded direction. The replacement shows the quadratic identity, equality conditions and sign-safe parameter rearrangement.'),
    49: ('Growth ratios establish all four eventual orders. The late regret cutoff is 246639, cubic timing estimate 3.2 seconds, and the six-axis grid has 64000000 points.', 'The replacement derives the limit and derivative, brackets adjacent integer budgets and uses monotonicity for all later times; timing is explicitly a model estimate, and grid counting is a product of independent coordinate choices.'),
    50: ('The cosine self-map/contraction has L=sin(1); the a priori target first certifies 87 iterations. Actual 32-step enclosure meets tolerance; posteriori estimate from supplied rounded steps is about 0.0681.', 'The replacement checks all Banach assumptions, handles the negative logarithm, separates a heuristic local rate from the certified numerical enclosure and derives the future-step geometric-tail estimate. All requested parts have their substantive reasoning.'),
}

assert len(NOTES) == 50
out = ROOT / OUT
assert not out.exists(), 'Preserve any earlier independent review'
draft = json.loads((ROOT / DRAFT).read_bytes())
baseline = json.loads((ROOT / BASELINE).read_bytes())
rows = {r['inventory_key']: r for r in baseline['exercises']}
decisions = draft['exercises']
assert len(rows) == len(decisions) == 50
assert len({r['inventory_key'] for r in decisions}) == 50
assert {r['inventory_key'] for r in decisions} == set(rows)
assert Counter(r['decision'] for r in decisions) == {'retain': 28, 'replace': 22}

# Independently reconstruct both actual candidate files from native source bytes.
# Exact equality to this replay protects every byte outside approved solution ranges.
ops = {}
exercise_reviews = []
for r in decisions:
    b = rows[r['inventory_key']]
    assert all(r[k] == b[k] for k in ['source_file', 'authoring_file', 'ordinal', 'anchor', 'label'])
    assert r['original_solution_sha256'] == b['solution']['sha256']
    assert r['original_question_sha256'] == b['problem']['sha256']
    assert r['original_hint_sha256'] == [h['disclosure']['sha256'] for h in b['hints']]
    assert digest(b['solution']['html'].encode()) == b['solution']['sha256']
    replacement = r['replacement_html'].encode()
    assert digest(replacement) == r['replacement_sha256']
    if r['decision'] == 'retain':
        assert replacement == b['solution']['html'].encode()
    else:
        assert replacement != b['solution']['html'].encode()
    native = (ROOT / b['source_file']).read_bytes()
    assert digest(native) == b['source_sha256'] == r['original_source_sha256']
    sr = b['solution']['range']
    assert native[sr['start_byte']:sr['end_byte']] == b['solution']['html'].encode()
    ops.setdefault(b['source_file'], []).append((sr, replacement, r['inventory_key']))
    authored = (ROOT / b['authoring_file']).read_bytes()
    assert digest(authored) == b['authoring']['source_sha256'] == r['original_authoring_source_sha256']
    if b['authoring_file'] != b['source_file']:
        ar = b['authoring']['solution_range']
        assert authored[ar['start_byte']:ar['end_byte']] == b['solution']['html'].encode()
        ops.setdefault(b['authoring_file'], []).append((ar, replacement, r['inventory_key']))
    math_note, depth_note = NOTES[r['ordinal']]
    exercise_reviews.append({
        'inventory_key': r['inventory_key'], 'ordinal': r['ordinal'], 'label': r['label'],
        'source_file': r['source_file'], 'authoring_file': r['authoring_file'],
        'anchor': r['anchor'], 'decision': r['decision'], 'decision_verdict': 'approved',
        'baseline_exercise_sha256': b['exercise']['sha256'],
        'question_sha256': b['problem']['sha256'],
        'hint_disclosure_sha256': [h['disclosure']['sha256'] for h in b['hints']],
        'original_solution_sha256': b['solution']['sha256'],
        'reviewed_solution_sha256': digest(replacement),
        'mathematics_verdict': 'passed', 'mathematics_review': math_note,
        'depth_verdict': 'adequate_for_stated_audience', 'depth_review': depth_note,
        'whole_question_hint_original_and_proposed_solution_read': True,
        'remaining_gaps': [], 'errors': [],
    })

replay_checks = []
for source, patches in sorted(ops.items()):
    original = (ROOT / source).read_bytes()
    ordered = sorted(patches, key=lambda x: x[0]['start_byte'])
    assert all(a[0]['end_byte'] <= b[0]['start_byte'] for a, b in zip(ordered, ordered[1:]))
    replay = original
    for sr, replacement, key in reversed(ordered):
        replay = replay[:sr['start_byte']] + replacement + replay[sr['end_byte']:]
    candidate = 'book/solutions/drafts/primer-basics-validation-v1/' + source
    actual = (ROOT / candidate).read_bytes()
    assert actual == replay
    replay_checks.append({'source': ref(source), 'candidate': ref(candidate),
                          'status': 'passed_exact_solution_range_replay',
                          'decision_count': len(patches),
                          'changed_ranges': sum(replacement != original[sr['start_byte']:sr['end_byte']]
                                                for sr, replacement, key in patches),
                          'all_non_solution_bytes_preserved': True})

# Recompute critical discrete/numerical conclusions rather than trusting the
# author's numerical strings. Fractions are used wherever the data are rational.
nums = []
def record(key, expressions, exact=True):
    nums.append({'inventory_key': key, 'exact_rational': exact, 'recomputed': expressions})

assert [F(3, t+1) for t in range(4)] == [F(3), F(3,2), F(1), F(3,4)]
assert F(3,30) == F(1,10) and F(3,31) < F(1,10)
record('primer-basics.html#mb-ex-sequences-1', {'a29': str(F(3,30)), 'a30': str(F(3,31)), 'first_strict_cutoff': 30})
assert sum(F(2,2**t) for t in range(4)) == F(15,4)
assert F(4,2**8) > F(1,100) >= F(4,2**9)
record('primer-basics.html#mb-ex-sequences-2', {'four_term_sum': '15/4', 'four_term_tail': '1/4', 'tail8': str(F(4,2**8)), 'tail9': str(F(4,2**9)), 'minimum_terms': 9})
assert F(2,2**7) > F(1,100) >= F(2,2**8)
record('primer-basics.html#mb-ex-f6', {'error7': str(F(2,2**7)), 'error8': str(F(2,2**8)), 'minimum_iterations': 8})
assert F(6) / F(1,5)**2 == 150
assert F(298,100)-F(3) == -F(1,2)*F(1,5)**2
record('primer-basics.html#mb-ex-sequences-3', {'energy_budget': 6, 'threshold_squared': '1/25', 'maximum_excursions': 150, 'late_example_drop': '-1/50'})
record('primer-basics.html#mb-ex-topology-3', {'fine_margin': str(F(35,100)-3*F(1,10)), 'coarse_midpoint_value': str(F(35,100)-3*F(1,5))})
assert F(64,100)/2**5 + F(6,100) == F(8,100)
assert F(64,100)/2**6 + F(6,100) == F(7,100)
assert F(64,100)/2**7 + F(6,100) == F(65,1000)
record('primer-basics.html#book-0-ex-3', {'envelope5': '0.08', 'envelope6': '0.07', 'envelope7': '0.065', 'non_strict_budget': 6, 'strict_budget': 7})
assert F(11,10)*F(48,10) == F(528,100)
assert F(528,100)-F(8,10) == F(448,100)
assert F(448,100)+F(4,10) == F(488,100)
record('primer-basics.html#book-0-ex-2', {'deterministic_term': '5.28', 'robust_u_interval': '[-1,-0.68]', 'chosen_successor_interval': '[4.48,4.88]', 'wrongly_fixed_colleague_command_successor': '5.4'})
assert F(11,10)*5-1+F(1,2) == 5
assert F(9,10)*5+F(1,2) == 5
record('primer-basics.html#book-0-ex-4', {'exact_maximum_disturbance': '1/2', 'worst_feedback_upper_endpoint': 5})

values = [F(x,10) for x in [18,23,14,24,14,24,14,4,14]]
def closure_trace(error):
    current = {0}; trace = [sorted(current)]
    while True:
        new = current | {x for x in range(9) if any(values[w]-error-abs(x-w) >= 0 for w in current)}
        trace.append(sorted(new))
        if new == current:
            return trace
        current = new
trace_half = closure_trace(F(1,2)); trace_zero = closure_trace(F(0))
assert trace_half == [[0], [0,1], [0,1,2], [0,1,2]]
assert trace_zero[-1] == list(range(8))
record('primer-basics.html::exercise-45', {'error_half_all_rounds': trace_half, 'error_zero_all_rounds': trace_zero, 'gateway_slack_zero_error': '3/10', 'gateway_margin_half_error': '-1/5'})
assert F(9,10)/(1-F(9,10))**2 == 90
assert F(9,10)/(1-F(9,10)) == 9
record('primer-basics.html::exercise-46', {'gamma': '9/10', 'weighted_sum': 90, 'normalized_mean': 9})
assert 20**6 == 64000000 and 20**10 == 10240000000000
record('primer-basics.html::exercise-49', {'cubic_seconds': '16/5', 'grid6': 20**6, 'grid10': 20**10})
regret = lambda t: 4*math.log(t)/math.sqrt(t)
assert regret(246638) > 0.1 > regret(246639)
record('primer-basics.html::exercise-49', {'regret246638': regret(246638), 'regret246639': regret(246639), 'first_permanent_integer_cutoff': 246639}, exact=False)
record('primer-basics.html#mb-ex-asymptotics-3', {'average_bound10000': 5*math.log(10000)/math.sqrt(10000)}, exact=False)

L = math.sin(1)
cutoff = math.log((1-math.cos(1))/((1-L)*1e-6))/math.log(1/L)
assert 86 < cutoff < 87
assert (1-math.cos(1))*L**86/(1-L) > 1e-6
assert (1-math.cos(1))*L**87/(1-L) < 1e-6
record('primer-basics.html::exercise-50', {'exact_sin_cos_float_cutoff': cutoff,
       'first_apriori_integer': math.ceil(cutoff),
       'apriori86': (1-math.cos(1))*L**86/(1-L),
       'apriori87': (1-math.cos(1))*L**87/(1-L),
       'apriori10': (1-math.cos(1))*L**10/(1-L),
       'posteriori_question_rounded_step': L/(1-L)*F(12833,1000000)}, exact=False)

COSINE_SOURCE = 'verification/lean/SafeLearning/CompleteFoundationsCosineIterates.lean'
cosine = (ROOT / COSINE_SOURCE).read_text()
assert digest((ROOT / COSINE_SOURCE).read_bytes()) == draft['numerical_checks']['cosine_32_certified_enclosures']['source']['sha256']
table_part = cosine.split('def sourceTable : Fin 33→ℝ×ℝ := ![', 1)[1].split('def lowerBound', 1)[0]
table = [(F(int(a),int(b)), F(int(c),int(d))) for a,b,c,d in re.findall(r'\(\((\d+)/(\d+):ℝ\),\((\d+)/(\d+):ℝ\)\)', table_part)]
assert len(table) == 33 and table[0] == (F(1),F(1))
error = F(1,80000000000)
assert F(15,1220496076800) <= error
def poly(x):
    return sum((-1)**j*x**(2*j)/math.factorial(2*j) for j in range(7))
lower_slacks = []; upper_slacks = []
for (lo,hi), (nlo,nhi) in zip(table,table[1:]):
    assert 0 <= lo <= hi <= 1
    ls = poly(hi)-error-nlo
    us = nhi-poly(lo)-error
    assert ls >= 0 and us >= 0
    lower_slacks.append(ls); upper_slacks.append(us)
fixed_low, fixed_high = F(7390851331,10000000000), F(7390851333,10000000000)
assert poly(fixed_low)-error > fixed_low
assert poly(fixed_high)+error < fixed_high
assert table[32] == (F(73908599959,100000000000), F(73908599970,100000000000))
assert table[32][0] > fixed_high
error32 = table[32][1]-fixed_low
assert error32 == F(8666,10000000000) and error32 < F(1,1000000)
record('primer-basics.html::exercise-50', {'native_table_pairs': 33,
       'exact_rational_interval_transfers_passed': 32,
       'polynomial_degree': 12, 'uniform_primary_source_error': str(error),
       'fixed_point_bracket_signs_passed': True,
       'fixed_low': str(fixed_low), 'fixed_high': str(fixed_high),
       'iterate32_low': str(table[32][0]), 'iterate32_high': str(table[32][1]),
       'error32_upper': str(error32), 'target': '1/1000000'})

def declaration_signature(name):
    match = re.search(r'theorem\s+' + re.escape(name) + r'\b[\s\S]*?(?=\s*:=)', cosine)
    assert match
    return match.group(0).strip()
declarations = ['actual_fixed_point_certified_enclosure',
                'actual_source_first_thirty_two_iterations_enclosed',
                'actual_thirty_two_iterations_meet_the_source_tolerance']
render_report = 'book/solutions/drafts/primer-basics-rendered-draft-v1.json'
rr = json.loads((ROOT / render_report).read_bytes())
assert rr['draft']['sha256'] == ref(DRAFT)['sha256']
assert rr['candidate']['sha256'] == ref(rr['candidate']['file'])['sha256']
assert not any(rr[k] for k in ['consoleErrors','pageErrors','leftoverDollar','katexErrors','missingAnchors','brokenLinks'])
assert all(not w['mobileOverflow'] and not w['clippedExpandedDisclosures'] for w in rr['widths'])

report = {
    'schema': 'independent_solution_review_v1',
    'status': 'approved', 'reviewer': '/root/review_gaussian35',
    'created_at_utc': datetime.now(timezone.utc).isoformat(),
    'page': 'primer-basics.html', 'audience': 'First-course linear algebra and single-variable calculus',
    'draft': ref(DRAFT), 'baseline': ref(BASELINE),
    'baseline_manifest': ref('book/solutions/baseline-source90/manifest.json'),
    'inventory': baseline['inventory'],
    'page_contract': ref('page_contract.md'), 'criteria': ref('book/solutions/README.md'),
    'source_refs': [r['source'] for r in replay_checks],
    'candidate_refs': [r['candidate'] for r in replay_checks],
    'counts': {'total': 50, 'retain': 28, 'replace': 22, 'mathematics_passed': 50,
               'depth_adequate': 50, 'explicit_decisions_approved': 50, 'book_lab_exercises': 4},
    'review_method': 'Independently read all50 complete questions, hints, original solutions and exact candidate solution bodies. Exercise-specific math and depth judgments below are authored by the reviewer. Exact byte replay and numerical recomputations supplement those judgments; no adequacy is inferred from length, preservation, or rendering alone.',
    'full_page_contract_read': True,
    'exact_solution_only_replay': replay_checks,
    'author_preservation_report': ref('book/solutions/drafts/primer-basics-preservation-v1.json'),
    'author_actual_render_report': ref(render_report),
    'render_evidence_review': {'scope': 'Reviewed the actual hash-bound native render report and visually inspected both supplied bounded screenshots. No independent browser execution or compiler rerun is claimed.',
                             'checked_widths': [w['width'] for w in rr['widths']],
                             'visually_inspected_screenshots': [ref('book/solutions/drafts/primer-basics-explorer-desktop-v1.png'), ref('book/solutions/drafts/primer-basics-rates-mobile-v1.png')]},
    'recomputed_numerical_and_exact_rational_checks': nums,
    'cosine_primary_source_review': {
        'proof_sources': [ref(COSINE_SOURCE), ref('verification/lean/SafeLearning/CompleteFoundationsCosineNumerics.lean'), ref('verification/lean/SafeLearning/CompleteFoundationsCosineContraction.lean')],
        'declarations': [{'name': 'SafeLearning.CompleteFoundationsCosineIterates.'+n, 'signature': declaration_signature(n)} for n in declarations],
        'review': 'Native source table has 33 rational interval pairs. All32 monotone-cosine/Taylor transfers and both fixed-point bracket polynomial signs were independently replayed with exact Fraction arithmetic using the supplied uniform remainder. The 32-step high-precision enclosures thus agree with actual named declarations, rather than rounded float comparisons. Existing convergence/fixed-point hypotheses are the nonempty closed cosine interval, its self-map property and L=sin1<1, explicitly explained in the draft.',
        'fresh_lean_compilation_claimed': False,
    },
    'exercises': exercise_reviews, 'errors': [], 'findings': [], 'remaining_gaps': [],
    'scope': 'Approval covers these exact fifty retain/replace bodies and the two exact candidates only. Questions, hints, summaries, anchors, scripts, hooks and all other bytes are unchanged. Does not install, publish, promote formal coverage or approve other pages.',
    'canonical_source_owner_selection_progress_publication_mutations': False,
    'helper': ref('reports/solution-review/prepare-primer-basics-independent-review-v1.py'),
}
# Verify all native hash references inherited from the baseline inventory too.
inv = report['inventory']
if isinstance(inv, dict) and 'file' in inv and 'sha256' in inv:
    assert ref(inv['file'])['sha256'] == inv['sha256']
out.write_text(json.dumps(report, ensure_ascii=False, indent=2, default=str)+'\n')
print(json.dumps({'report': ref(OUT), 'status': report['status'], 'counts': report['counts'],
                  'replayed_candidate_files': len(replay_checks),
                  'numerical_records': len(nums), 'errors': report['errors']}, ensure_ascii=False))
