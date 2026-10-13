#!/usr/bin/env python3
"""Recompute the probability draft's numerical examples; make no Lean claims."""
from fractions import Fraction as F
from math import ceil, exp, log, sqrt
from statistics import NormalDist
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[3]
normal = NormalDist()
values = {}


def put(locator, **record):
    values["primer-probability.html" + locator] = record


def kl(p, q):
    return sum(a * log(a / b) for a, b in zip(p, q) if a)


put("#pr-ready-1", complement=1-.15)
put("#pr-ready-2", weighted_mean=2/4+6*3/4)
put("#pr-ready-3", outer_product=[[1,2],[2,4]], expanded_quadratic_coefficients=[1,4,4], zero_direction=[-2,1])
put("#pr-extra-1", total_mass=.5+.25+.25, tail_mass=.25+.25, mean=2/4+4/4)
mean=F(3,2);var=5-mean*mean
put("#pr-extra-2", second_moment=5, variance=float(var), std=sqrt(float(var)), transformed_mean=float(3*mean+1), transformed_variance=float(9*var))
put("#pr-extra-3", mean_X=0, mean_Y=2/3, covariance=0, variance_X=2/3, variance_Y=float(F(2,3)-F(2,3)**2), conditional_zero_X_given_zero_Y=1)
put("#pr-extra-4", probability_even=3/6, probability_above_three=3/6, conditional_even=(2/6)/(3/6))
put("#pr-extra-5", alarm=.8*.1+.2*.9, fault_given_alarm=(.8*.1)/(.8*.1+.2*.9), counts=[[80,20],[180,720]])
put("#pr-extra-6", mean=(0+4)/2, within_variance=1, between_variance=(4+4)/2, second_moment=(1+17)/2, variance=(1+17)/2-2**2)
put("#pr-extra-7", step_one=[.8,.2], step_two=[.8*.8+.2*.3,.8*.2+.2*.7])
put("#pr-extra-8", stationary=[.3/(1-.5),.4], second_coordinate=.6*.2+.4*.7)
put("#pr-extra-9", independent_mean_variance=.2*.8/100, copied_mean_variance=.2*.8/50, standard_deviations=[sqrt(.16/100),sqrt(.16/50)])
put("#pr-extra-10", std=2, exact_left_probability=normal.cdf(1), exact_central_probability=2*normal.cdf(1)-1, result_from_supplied_Phi=2*.8413-1)
put("#pr-extra-11", precision=5/4, posterior_variance=4/5, posterior_mean=12/5, square_completion_constant=9/5, predictive_variance=4/5+1)
q95=normal.inv_cdf(.95)
put("#pr-extra-12", mean=3, variance=1+4+2*.5, exact_quantile=q95, exact_minimum_threshold=3+sqrt(6)*q95, threshold_using_supplied_rounded_quantile=3+sqrt(6)*1.64485)
put("#pr-extra-13", Markov_at_eight=2/8, unclipped_Markov_at_one=2, clipped_bound_at_one=1)
put("#pr-extra-14", continuous_size=log(40)/.02, integer_size=ceil(log(40)/.02), bound_at_184=2*exp(-.02*184), bound_at_185=2*exp(-.02*185))
put("#pr-extra-15", uniform_mean=1, MGF_at_one_quarter=2*(exp(.5)-1), claimed_bound_at_one_quarter=exp(.125), centered_parameter=1)
put("#pr-extra-16", simultaneous_lower_bound=1-3*.01, independent_product_lower_bound=.99**3)
put("#pr-extra-17", per_mean_failure=.05/10, continuous_size=log(400)/.02, common_integer_size=ceil(log(400)/.02), total_failure=10*.005)
put("#pr-extra-18", finite_budget_examples={str(t):float(F(1,20)*(1-F(1,t+1))) for t in (1,2,100)}, total_budget_limit=.05, independent_no_failure_at_100=.95**100)
put("#pr-extra-19", next_sign_mean=(-1+1)/2, conditional_sum_equals_current_sum=True)
put("#pr-extra-20", conditional_mean_for_a_one=(-1+1)/2, conditional_mean_for_a_two=(-2+2)/2, valid_uniform_scale=2)
put("#pr-extra-21", two_outcome_products=[1*1,(-1)*(-1)], conditional_mean=1)
put("#pr-extra-22", fair_entropy=log(2), biased_entropy=-.25*log(.25)-.75*log(.75))
put("#pr-extra-23", TV=.25, KL_p_q=kl([.75,.25],[.5,.5]), KL_q_p=kl([.5,.5],[.75,.25]))
put("#pr-extra-24", KL_p_q=log(2), KL_q_p="infinite_due_to_positive_mass_at_zero_reference_mass", TV=.5, finite_Pinsker_bound=sqrt(log(2)/2))
put("#pr-extra-25", CDF_values=[.8,.95,1], VaR_levels_and_values={"0.8":0,"0.9":10,"0.95":10})
put("#pr-extra-26", CVaR=(.05*100+.05*10)/.1, mean=.15*10+.05*100, conditional_tail_mean=(.15*10+.05*100)/.2)
piecewise_checks=[]
for nu in (-5,5,50,150):
    direct=nu+10*(.8*max(-nu,0)+.15*max(10-nu,0)+.05*max(100-nu,0))
    piece=(65-9*nu if nu<0 else 65-nu if nu<10 else 50+.5*nu if nu<100 else nu)
    assert abs(direct-piece)<1e-10
    piecewise_checks.append({"nu":nu,"direct":direct,"simplified":piece})
put("#pr-extra-27", slopes=[-9,-1,.5,1], minimum_at_ten=10+10*.05*90, piecewise_checks=piecewise_checks)
put("#pr-extra-28", specified_pair=.1**2*.9**2, exactly_two=6*.1**2*.9**2, at_least_one=1-.9**4)
put("#pr-extra-29", upper_limit=1-exp(log(.05)/100))
put("#pr-extra-30", uniform_rank_coverage=18/20, subgroup_average=(.8+1)/2)
alarm=.01*.9+.99*.08
put("#book-c-b1", alarm=alarm, fault_after_alarm=.009/alarm, release_loss_after_alarm=30*.009/alarm, fault_after_silence=.001/(1-alarm), always_release_cost=.30, old_rule_cost=6*alarm+30*.001)
put("#book-c-b2", predictive_variance=5/3, predictive_std=sqrt(5/3), standardized_endpoint=2/sqrt(5/3), coverage=2*normal.cdf(2/sqrt(5/3))-1)
put("#book-c-b3", variance_at_100=float(F(2,3)+F(1,100)), exact_fraction_at_100=str(F(2,3)+F(1,100)), shared_covariance=2/3, limiting_std=sqrt(2/3))
put("#book-c-b4", union_allowance=.02/50, independent_allowance=1-.98**(1/50), example_independent_batch_failure=1-.996**50)
se=sqrt(.07*.93/200)
put("::exercise-38", estimate=.07, estimated_standard_error=se, normal_interval=[.07-1.96*se,.07+1.96*se], exact_zero_failure_upper_limit=1-exp(log(.05)/200), rule_of_three=.015)
q=normal.inv_cdf(.99995)
put("::exercise-39", posterior_change=.018/.0278, expected_false_alarm_count=5, independent_any_false_alarm=1-.99**500, per_step_level=.05/500, exact_Gaussian_threshold=q, tail_at_3_89=2*(1-normal.cdf(3.89)), tail_at_3_89060=2*(1-normal.cdf(3.89060)))
m=72/85;s=1/sqrt(17)
put("::exercise-40", average_noise_variance=.25/4, posterior_precision=17, posterior_mean=m, posterior_variance=1/17, posterior_std=s, standardized_threshold=(.5-m)/s, threshold_probability=normal.cdf((.5-m)/s), lower_bound=m-2*s, lower_bound_failure_probability=normal.cdf(-2))
put("::exercise-41", Chebyshev_N=10000, Hoeffding_continuous_N=log(200)/.005, Hoeffding_integer_N=ceil(log(200)/.005), Hoeffding_uniform_scale=.2, uniform_std=.2/sqrt(3), scale_ratio=sqrt(3), shifted_uniform_mean=.1, coefficient_recurrence_difference="(2j+2)(2j+3)-6(j+1)=4j(j+1)>=0")
k1=kl([.6,.3,.1],[.4,.4,.2]);k2=kl([.4,.4,.2],[.6,.3,.1])
put("::exercise-42", KL_p_q=k1, KL_q_p=k2, TV=.2, Pinsker_bounds=[sqrt(k1/2),sqrt(k2/2)], KL_p_q_prime="infinite", KL_q_prime_p=.5*log(5/6)+.5*log(5/3))
q90=normal.inv_cdf(.9);gauss_tail=.8+sqrt(4.96)*normal.pdf(q90)/.1
put("::exercise-43", mean=.8, positive_cost_probability=.2, VaR=2, CVaR=6, optimization_at_VaR=2+.05*8/.1, variance=5.6-.8**2, std=sqrt(4.96), gaussian_quantile=q90, gaussian_density=normal.pdf(q90), gaussian_CVaR=gauss_tail, actual_minus_Gaussian=6-gauss_tail, actual_constraint_decisions=[True,True,False])
first=F(342)*(F(1,19)-F(1,20));second=F(342)*(F(1,20)-F(1,21));v=second-first**2
assert first==F(9,10) and second==F(57,70) and v==F(3,700)
assert F(342)*(F(1,18)-F(1,19))==1
test_part=(first-second)/2000;total=v+test_part
assert total==F(303,70000) and test_part/v==F(1,100)
put("::exercise-44", threshold_rank=18, marginal_coverage=.9, beta_density_normalization=1, exact_mean=str(first), exact_second_moment=str(second), exact_variance=str(v), calibration_std=sqrt(float(v)), low_coverage_probability=19*.8**18*.2+.8**19, exact_test_contribution=str(test_part), exact_total_variance=str(total), measured_std=sqrt(float(total)), test_to_calibration_variance_ratio=float(test_part/v))

assert values["primer-probability.html#pr-extra-12"]["exact_minimum_threshold"] > values["primer-probability.html#pr-extra-12"]["threshold_using_supplied_rounded_quantile"]
assert values["primer-probability.html#pr-extra-14"]["bound_at_184"] > .05 >= values["primer-probability.html#pr-extra-14"]["bound_at_185"]
assert values["primer-probability.html#pr-extra-15"]["MGF_at_one_quarter"] > values["primer-probability.html#pr-extra-15"]["claimed_bound_at_one_quarter"]
assert values["primer-probability.html::exercise-39"]["tail_at_3_89"] > .0001 >= values["primer-probability.html::exercise-39"]["tail_at_3_89060"]
assert len(values)==44
draft_file="book/solutions/drafts/primer-probability-expanded-solutions-v1.json"
draft=json.loads((ROOT/draft_file).read_text())
assert set(values)=={row["inventory_key"] for row in draft["exercises"]}
report={
    "status":"passed_independent_numerical_recomputations_and_exact_rational_checks",
    "draft":{"file":draft_file,"sha256":hashlib.sha256((ROOT/draft_file).read_bytes()).hexdigest()},
    "helper":{"file":str(Path(__file__).relative_to(ROOT)),"sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest()},
    "exercise_count":44,
    "recomputed_quantities":values,
    "critical_rounding_directions_checked":True,
    "limits":["These are numerical and exact-rational verification of the authored examples, not new Lean proof coverage or a proof of all pedagogical claims.","Normal CDF and inverse values use Python statistics.NormalDist; exact formulas and Source90 qualifications remain in the drafts.","The algebra, probabilistic assumptions and conceptual explanations were separately read by the author and require the planned independent editorial review."]}
destination=ROOT/"reports/solution-review/probability-draft-numbers-v1.json"
with destination.open("x") as stream:
    json.dump(report,stream,indent=2)
    stream.write("\n")
print(json.dumps({"status":report["status"],"exercise_count":44,"report":str(destination.relative_to(ROOT)),"sha256":hashlib.sha256(destination.read_bytes()).hexdigest()}))
