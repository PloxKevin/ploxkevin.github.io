#!/usr/bin/env python3
"""Recompute the new C–E book examples with independent deterministic methods.

Uses only the standard library. Run from any directory:
    /usr/bin/python book/checks/applied.py
Checks are numerical evidence, not formal proofs or empirical validation.
"""

from html.parser import HTMLParser
import json
import math
from pathlib import Path
import re
from statistics import NormalDist


ROOT = Path(__file__).resolve().parents[2]
CHECKS = []
RESULTS = {}
NORMAL = NormalDist()


def close(name, actual, expected, tolerance=1e-10):
    assert math.isfinite(actual), (name, actual)
    assert abs(actual - expected) <= tolerance, (name, actual, expected)
    CHECKS.append(name)
    return actual


def require(name, condition):
    assert condition, name
    CHECKS.append(name)


def solve2(matrix, rhs):
    """Solve a two-variable system directly by elimination."""
    a, b = matrix[0]
    c, d = matrix[1]
    det = a * d - b * c
    return ((d * rhs[0] - b * rhs[1]) / det,
            (a * rhs[1] - c * rhs[0]) / det)


def probability_chapter():
    # Enumerate the four joint outcomes, then optimise all four sensor rules.
    joint = {(1, 1): 0.036, (1, 0): 0.004,
             (0, 1): 0.0768, (0, 0): 0.8832}
    alarm = sum(prob for (fault, signal), prob in joint.items() if signal)
    posterior_alarm = joint[1, 1] / alarm
    posterior_quiet = joint[1, 0] / (1 - alarm)
    policy_costs = {}
    for inspect_alarm in (False, True):
        for inspect_quiet in (False, True):
            cost = 0
            for (fault, signal), prob in joint.items():
                inspect = inspect_alarm if signal else inspect_quiet
                cost += prob * (6 if inspect else 30 * fault)
            policy_costs[inspect_alarm, inspect_quiet] = cost
    close('C.W1 alarm probability', alarm, 0.1128)
    close('C.W1 posterior after alarm', posterior_alarm, 15 / 47)
    close('C.W1 posterior after quiet', posterior_quiet, 5 / 1109)
    close('C.W1 alarm release loss', 30 * posterior_alarm, 450 / 47)
    close('C.W1 quiet release loss', 30 * posterior_quiet, 150 / 1109)
    close('C.W1 optimal rule cost', policy_costs[True, False], 0.7968)
    close('C.W1 always release cost', policy_costs[False, False], 1.2)
    close('C.W1 always inspect cost', policy_costs[True, True], 6)
    require('C.W1 optimal among all sensor rules',
            min(policy_costs, key=policy_costs.get) == (True, False))
    RESULTS['book-c-example-alarm'] = {
        'alarm_probability': alarm, 'posterior_fault_alarm': posterior_alarm,
        'posterior_fault_quiet': posterior_quiet,
        'optimal_rule': 'inspect on alarm; release on quiet',
        'expected_cost_units': policy_costs[True, False]}

    # Independent route: condition the joint Gaussian using measurement covariance.
    # Var(y1)=5, Var(y2)=8, Cov(y1,y2)=4; Cov(theta,yi)=4.
    coefficients = solve2(((5, 4), (4, 8)), (4, 4))
    mean = coefficients[0] * 2 + coefficients[1] * -1
    variance = 4 - 4 * sum(coefficients)
    coverage = 2 * NORMAL.cdf(2 / math.sqrt(variance)) - 1
    close('C.W2 posterior mean from joint covariance', mean, 7 / 6)
    close('C.W2 posterior variance from joint covariance', variance, 2 / 3)
    close('C.W2 posterior standard deviation', math.sqrt(variance),
          0.816496580927726)
    close('C.W2 tolerance probability', coverage, 0.9856941215645703)
    require('C.W2 posterior offset requirement met', coverage >= 0.98)
    for theta in (-3, 0, 1, 7 / 6, 5):
        original = theta**2 / 4 + (2 - theta)**2 + (-1 - theta)**2 / 4
        completed = 1.5 * (theta - 7 / 6)**2 + 53 / 24
        close(f'C.W2 square completion at {theta}', original, completed)
    RESULTS['book-c-example-calibration'] = {
        'posterior_mean_mm': mean, 'posterior_variance_mm2': variance,
        'offset_2mm_probability': coverage, 'measurement_covariance_mm2': 4}

    # B1 is checked through a second enumeration with a changed base rate.
    new_joint = {(1, 1): 0.009, (1, 0): 0.001,
                 (0, 1): 0.0792, (0, 0): 0.9108}
    new_alarm = sum(prob for (_, signal), prob in new_joint.items() if signal)
    new_posterior = new_joint[1, 1] / new_alarm
    old_rule_cost = sum(prob * (6 if signal else 30 * fault)
                        for (fault, signal), prob in new_joint.items())
    release_cost = sum(prob * 30 * fault
                       for (fault, signal), prob in new_joint.items())
    close('C.B1 new alarm probability', new_alarm, 0.0882)
    close('C.B1 new posterior', new_posterior, 5 / 49)
    close('C.B1 new quiet posterior', 0.001 / (1 - new_alarm),
          5 / 4559)
    require('C.B1 release preferred after alarm', 30 * new_posterior < 6)
    close('C.B1 old rule cost', old_rule_cost, 0.5592)
    close('C.B1 new optimal rule cost', release_cost, 0.3)
    RESULTS['book-c-b1'] = {'posterior_fault_alarm': new_posterior,
        'decision': 'release after either signal',
        'always_release_cost_units': release_cost,
        'old_rule_cost_units': old_rule_cost}

    prediction_variance = variance + 1
    predictive_coverage = 2 * NORMAL.cdf(2 / math.sqrt(prediction_variance)) - 1
    close('C.B2 predictive variance', prediction_variance, 5 / 3)
    close('C.B2 predictive standard deviation', math.sqrt(prediction_variance),
          1.2909944487358056)
    close('C.B2 reading tolerance probability', predictive_coverage,
          0.8786647496415179)
    require('C.B2 predictive requirement fails', predictive_coverage < 0.98)
    RESULTS['book-c-b2'] = {'predictive_variance_mm2': prediction_variance,
        'reading_2mm_probability': predictive_coverage, 'meets_0_98': False}

    # Sum all n^2 covariances; only diagonal terms contain fresh noise variance.
    n = 100
    average_variance = sum(variance + (1 if i == j else 0)
                           for i in range(n) for j in range(n)) / n**2
    close('C.B3 full covariance average variance', average_variance, 203 / 300)
    close('C.B3 variance floor', variance, 2 / 3)
    require('C.B3 independent-errors shortcut underestimates',
            prediction_variance / n < average_variance)
    RESULTS['book-c-b3'] = {'average_variance_mm2': average_variance,
                           'limiting_variance_mm2': variance}

    q_union = 0.02 / 50
    q_exact = 1 - 0.98**(1 / 50)
    # Sum the binomial tail explicitly rather than use the complement formula.
    batch_probability = sum(math.comb(50, k) * 0.004**k * 0.996**(50 - k)
                            for k in range(1, 51))
    close('C.B4 union-bound allowance', q_union, 0.0004)
    close('C.B4 independent exact allowance', q_exact, 0.0004039725274669337)
    close('C.B4 exact allowance reaches batch budget',
          1 - (1 - q_exact)**50, 0.02)
    close('C.B4 original rule batch probability', batch_probability,
          0.18159754932390026)
    require('C.B4 original escape rate exceeds both allowances',
            0.004 > q_exact > q_union)
    RESULTS['book-c-b4'] = {'q_union_bound': q_union,
        'q_independent_exact': q_exact,
        'batch_escape_probability_original_rule': batch_probability}


def rk4_held(x, v, duration=5, steps=1000):
    dt = duration / steps
    def f(state):
        return -0.05 * state + 0.2 * v
    for _ in range(steps):
        k1 = f(x)
        k2 = f(x + dt * k1 / 2)
        k3 = f(x + dt * k2 / 2)
        k4 = f(x + dt * k3)
        x += dt * (k1 + 2 * k2 + 2 * k3 + k4) / 6
    return x


def systems_chapter():
    a = math.exp(-0.25)
    b = 4 * (1 - a)
    q = a - 0.5 * b
    close('D.W1 exact sampled a', a, 0.7788007830714049)
    close('D.W1 exact sampled b', b, 0.8847968677143805)
    close('D.W1 sampled closed-loop multiplier', q, 0.33640234921421464)
    close('D.W1 Lyapunov ratio', q**2, 0.11316654055684242)
    x0 = -2
    x1 = rk4_held(x0, -0.5 * x0)
    x2 = rk4_held(x1, -0.5 * x1)
    close('D.W1 first state independently integrated', x1, -0.6728046984284293)
    close('D.W1 second state independently integrated', x2, -0.22633308111368483)
    for x in (-2, -1, 0, 1, 2):
        for s in (0, 1, 2.5, 5):
            exact = (3 * math.exp(-0.05 * s) - 2) * x
            close(f'D.W1 held trajectory x={x},s={s}',
                  rk4_held(x, -0.5 * x, duration=s), exact)
            require(f'D.W1 trajectory inside interval x={x},s={s}',
                    -2 <= exact <= 2)
    continuous_q = math.exp(-0.75)
    close('D.W1 continuously updated multiplier', continuous_q, 0.4723665527410147)
    require('D.W1 sampling and continuous feedback differ', abs(q - continuous_q) > .1)
    RESULTS['book-d-example-thermal'] = {'a': a, 'b_C_per_kW': b,
        'sampled_multiplier': q, 'first_temperature_C': 22 + x1,
        'second_temperature_C': 22 + x2, 'lyapunov_ratio': q**2}

    # Trapezoidal integration is exact for the linearly decreasing braking speed.
    braking_distance = sum(((1 - i / 1000) + (1 - (i + 1) / 1000)) / 2 / 1000
                           for i in range(1000))
    clearance = .8 - braking_distance
    delayed_travel = .4 + braking_distance
    close('D.W2 brake distance by integration', braking_distance, .5)
    close('D.W2 immediate clearance', clearance, .3)
    close('D.W2 delayed required distance', delayed_travel, .9)
    require('D.W2 delayed strategy fails', delayed_travel > .8)
    for t in (0, .2, .5, 1):
        d = .8 - (t - t**2 / 2)
        speed = 1 - t
        close(f'D.W2 invariant stopping margin t={t}', d - speed**2 / 2, .3)
    RESULTS['book-d-example-braking'] = {'braking_distance_m': braking_distance,
        'clearance_m': clearance, 'travel_with_0_4s_delay_m': delayed_travel,
        'largest_delay_s': clearance}

    readings = [abs(x0), abs(x1), abs(x2)]
    first_reading = next(i for i, magnitude in enumerate(readings) if magnitude <= .3)
    require('D.B1 first comfort reading', first_reading == 2)
    close('D.B1 second input', 1 - .5 * x1, 1.3364023492142146)
    RESULTS['book-d-b1'] = {'first_qualifying_reading': first_reading,
        'elapsed_minutes': 5 * first_reading, 'second_input_kW': 1 - .5 * x1}

    k_min = (a - .5) / b
    close('D.B2 lower feasible gain', k_min, .31510145802347483)
    for k in (k_min, .4, .5):
        multiplier = a - b * k
        for x in (-.2, .2):
            for w in (-.1, .1):
                require(f'D.B2 invariant corners k={k},x={x},w={w}',
                        abs(multiplier * x + w) <= .2 + 1e-14)
        require(f'D.B2 heater limits k={k}', 1 - 2 * k >= 0 and 1 + 2 * k <= 2)
    require('D.B2 gain below lower boundary fails',
            .2 * (a - b * (k_min - .001)) + .1 > .2)
    RESULTS['book-d-b2'] = {'gain_min_kW_per_C': k_min, 'gain_max_kW_per_C': .5,
                           'claim': 'sampled invariance for initial |x| <= 0.2'}

    maximum_delay = (.72 - 1.1**2 / 2) / 1.1
    close('D.B3 worst travel', 1.1 * .2 + 1.1**2 / 2, .825)
    close('D.B3 maximum robust delay', maximum_delay, .10454545454545444)
    close('D.B3 boundary stopping distance', 1.1 * maximum_delay + 1.1**2 / 2, .72)
    require('D.B3 midpoint passes but worst case fails',
            1 * .2 + 1**2 / 2 <= .75 and 1.1 * .2 + 1.1**2 / 2 > .72)
    RESULTS['book-d-b3'] = {'worst_travel_m': .825,
        'maximum_certified_delay_s': maximum_delay, 'proposed_delay_certified': False}

    unclipped = -2 * (a - b)
    actual = rk4_held(-2, 1)
    close('D.B4 unclipped first prediction', unclipped, .21199216928595122)
    close('D.B4 clipped first trajectory', actual, -.6728046984284293)
    boundary_images = [a * -2 + b, a * -1 + b,
                       (a - b) * -1, (a - b) * 1,
                       a * 1 - b, a * 2 - b]
    close('D.B4 largest image magnitude', max(map(abs, boundary_images)),
          .6728046984284293)
    require('D.B4 all affine-piece endpoints satisfy invariance',
            all(abs(value) <= 2 for value in boundary_images))
    RESULTS['book-d-b4'] = {'unclipped_prediction_C': unclipped,
        'clipped_first_error_C': actual,
        'maximum_sampled_image_magnitude_C': max(map(abs, boundary_images))}


def evaluate_policy(p, rho=.25, gamma=.8):
    # Solve Bellman equations directly; do not use the chapter's closed form.
    transition = ((1 - rho * p, rho * p), (1, 0))
    bellman = ((1 - gamma * transition[0][0], -gamma * transition[0][1]),
               (-gamma, 1))
    rewards = solve2(bellman, (2 + 2 * p, 0))
    costs = solve2(bellman, (0, 1))
    # Independent forward propagation of exact probability mass and signals.
    mass_r, mass_w = 1., 0.
    reward_sum = cost_sum = 0.
    discount = 1.
    for _ in range(1000):
        reward_sum += discount * mass_r * (2 + 2 * p)
        cost_sum += discount * mass_w
        mass_r, mass_w = (mass_r * (1 - rho * p) + mass_w,
                          mass_r * rho * p)
        discount *= gamma
    close(f'E Bellman versus forward production p={p},rho={rho}', rewards[0], reward_sum)
    close(f'E Bellman versus forward maintenance p={p},rho={rho}', costs[0], cost_sum)
    return rewards[0], costs[0]


def score(z):
    return 1.2 - .6 * max(0, z + .5) - .4 * max(0, z - .5)


def learning_chapter():
    p_star = 5 / 9
    reward, cost = evaluate_policy(p_star)
    close('E.W1 constrained reward', reward, 14)
    close('E.W1 constrained maintenance', cost, .5)
    gentle_reward, gentle_cost = evaluate_policy(0)
    fast_reward, fast_cost = evaluate_policy(1)
    close('E.W1 gentle production', gentle_reward, 10)
    close('E.W1 gentle cost', gentle_cost, 0)
    close('E.W1 fast production', fast_reward, 50 / 3)
    close('E.W1 fast cost', fast_cost, 5 / 6)
    # Directly evaluate a nearby feasible and infeasible policy.
    below_reward, below_cost = evaluate_policy(p_star - .001)
    above_reward, above_cost = evaluate_policy(p_star + .001)
    require('E.W1 budget boundary and increasing reward',
            below_cost < .5 < above_cost and below_reward < reward < above_reward)
    RESULTS['book-e-example-policy'] = {'optimal_p_in_family': p_star,
        'expected_discounted_items': reward, 'discounted_maintenance_units': cost}

    close('E.W2 nominal network score', score(0), .9)
    close('E.W2 exact interval minimum', min(score(-.2), score(.2)), .78)
    close('E.W2 conservative interval minimum', score(0) - .2, .7)
    slopes = [(score(b) - score(a)) / (b - a)
              for a, b in ((-2, -1), (-.4, .4), (1, 2))]
    for i, (actual, expected) in enumerate(zip(slopes, (0, -.6, -1))):
        close(f'E.W2 exact piece slope {i}', actual, expected)
    require('E.W2 global slope bound', max(map(abs, slopes)) <= 1 + 1e-14)
    reward_a, cost_a = evaluate_policy(.4)
    reward_b, cost_b = evaluate_policy(.8)
    close('E.W2 fallback production', reward_a, 350 / 27)
    close('E.W2 fallback cost', cost_a, 10 / 27)
    close('E.W2 rejected mode cost', cost_b, 20 / 29)
    require('E.W2 fixed-mode feasibility gate', cost_a <= .5 < cost_b)
    RESULTS['book-e-example-network'] = {'nominal_score': score(0),
        'score_lower_bound': .7, 'exact_score_minimum': .78,
        'selected_mode': 'A after budget gate', 'selected_cost_units': cost_a,
        'selected_production_items': reward_a}

    tight_p = 5 / 19
    tight_reward, tight_cost = evaluate_policy(tight_p)
    close('E.B1 tightened-budget production', tight_reward, 12)
    close('E.B1 tightened-budget maintenance', tight_cost, .25)
    RESULTS['book-e-b1'] = {'optimal_p': tight_p,
                           'discounted_items': tight_reward, 'maintenance_units': tight_cost}

    robust_p = 25 / 54
    robust_reward, robust_cost = evaluate_policy(robust_p, rho=.3)
    close('E.B2 robust boundary cost', robust_cost, .5)
    close('E.B2 robust boundary production', robust_reward, 79 / 6)
    for rho in (.2, .25, .3):
        _, candidate_cost = evaluate_policy(robust_p, rho=rho)
        require(f'E.B2 all wear endpoints feasible rho={rho}', candidate_cost <= .5 + 1e-14)
    _, original_cost = evaluate_policy(.5, rho=.3)
    close('E.B2 p=0.5 worst maintenance', original_cost, 15 / 28)
    require('E.B2 p=0.5 rejected', original_cost > .5)
    RESULTS['book-e-b2'] = {'robust_p_max': robust_p,
        'p_0_5_worst_cost': original_cost, 'boundary_worst_cost': robust_cost}

    nominal = score(.8)
    worst = score(1.15)
    close('E.B3 nominal score', nominal, .3)
    close('E.B3 worst score', worst, -.05)
    close('E.B3 score at tie', score(1.1), 0)
    close('E.B3 positive-direction tie distance', 1.1 - .8, .3)
    require('E.B3 allowed perturbation flips nomination', nominal > 0 and worst < 0)
    RESULTS['book-e-b3'] = {'nominal_score': nominal, 'allowed_negative_score': worst,
        'tie_vibration_mm_per_s': 3.1, 'tie_distance_mm_per_s': .3}

    # Find the stationary law by deterministic distribution propagation.
    mass_r, mass_w = 1., 0.
    for _ in range(1000):
        mass_r, mass_w = (mass_r * (1 - .25 * p_star) + mass_w,
                          mass_r * .25 * p_star)
    close('E.B4 stationary ready fraction', mass_r, 36 / 41)
    close('E.B4 stationary worn fraction', mass_w, 5 / 41)
    mean_production = mass_r * (2 + 2 * p_star)
    close('E.B4 mean production', mean_production, 112 / 41)
    close('E.B4 twenty-shift repair expectation', 20 * mass_w, 100 / 41)
    RESULTS['book-e-b4'] = {'stationary_repair_fraction': mass_w,
        'stationary_production_items_per_shift': mean_production,
        'repairs_in_20_stationary_shifts': 20 * mass_w}


class FragmentParser(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.ids = []
        self.links = []
        self.words = []
        self.tags = []
        self.errors = []
        self.summaries = []
        self.summary_parts = None
        self.details_count = 0

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if 'id' in attrs:
            self.ids.append(attrs['id'])
        if tag == 'a':
            self.links.append(attrs.get('href', ''))
        if tag == 'details':
            self.details_count += 1
        if tag == 'summary':
            self.summary_parts = []
        if tag not in {'br', 'hr', 'img', 'input', 'meta', 'link'}:
            self.tags.append(tag)

    def handle_endtag(self, tag):
        if tag == 'summary' and self.summary_parts is not None:
            self.summaries.append(' '.join(''.join(self.summary_parts).split()))
            self.summary_parts = None
        if not self.tags or self.tags[-1] != tag:
            self.errors.append(('unbalanced', tag, list(self.tags[-3:])))
        else:
            self.tags.pop()

    def handle_data(self, data):
        self.words.append(data)
        if self.summary_parts is not None:
            self.summary_parts.append(data)


def check_fragments():
    counts = {}
    prose_counts = {}
    for stem, letter in (('primer-probability', 'C'), ('primer-systems', 'D'),
                         ('primer-rl-nn', 'E')):
        path = ROOT / 'book' / 'chapters' / (stem + '.html')
        html = path.read_text()
        parser = FragmentParser()
        parser.feed(html)
        require(stem + ' HTML nesting', not parser.errors and not parser.tags)
        require(stem + ' unique fragment IDs', len(parser.ids) == len(set(parser.ids)))
        require(stem + ' outer section', html.startswith('<section class="book-chapter" id="book-lab">'))
        require(stem + ' no skeleton or scripts', '<script' not in html and '<html' not in html)
        require(stem + ' twelve details', parser.details_count == 12)
        exercises = [summary for summary in parser.summaries if summary.startswith('Exercise ')]
        require(stem + ' four labelled applications', len(exercises) == 4)
        for i, level in enumerate(('Easy', 'Medium', 'Hard', 'Hard'), start=1):
            require(stem + f' exercise {i} level',
                    exercises[i - 1].startswith(f'Exercise {letter}.B{i} — {level}:'))
        require(stem + ' four separate hints', parser.summaries.count('Show hint') == 4)
        require(stem + ' four complete solution controls',
                parser.summaries.count('Show worked solution') == 4)
        text = ' '.join(parser.words)
        word_count = len(re.findall(r"\b[\w]+(?:['’][\w]+)?\b", text))
        require(stem + ' substantial chapter word count', 1500 <= word_count <= 2400)
        counts[stem] = word_count
        prose = re.sub(r'\$\$[\s\S]*?\$\$|\$[^$]*?\$', ' ', text)
        prose_word_count = len(re.findall(r"\b[\w]+(?:['’][\w]+)?\b", prose))
        require(stem + ' substantial prose excluding math', 1500 <= prose_word_count <= 2400)
        prose_counts[stem] = prose_word_count
        for href in parser.links:
            filename, _, anchor = href.partition('#')
            destination_path = ROOT / 'SafeLearning' / (filename or stem + '.html')
            require(stem + ' internal page link ' + href, destination_path.is_file())
            if anchor:
                destination = html if not filename and anchor.startswith('book-') else destination_path.read_text()
                require(stem + ' existing destination anchor ' + href,
                        f'id="{anchor}"' in destination or f"id='{anchor}'" in destination)
        require(stem + ' display delimiters balanced', html.count('$$') % 2 == 0)
        require(stem + ' inline delimiters balanced', html.replace('$$', '').count('$') % 2 == 0)
    return counts, prose_counts


def main():
    probability_chapter()
    systems_chapter()
    learning_chapter()
    word_counts, prose_word_counts = check_fragments()
    print(json.dumps({'passed': True, 'check_count': len(CHECKS),
                      'checks': CHECKS, 'word_counts': word_counts,
                      'prose_word_counts': prose_word_counts,
                      'results': RESULTS}, indent=2))


if __name__ == '__main__':
    main()
