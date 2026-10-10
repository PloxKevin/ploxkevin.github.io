import SafeLearning.CompleteModulesLandscapeARGaussianLaw
import SafeLearning.CompleteModulesLandscapeARStableMoments
import SafeLearning.CompleteModulesLandscapeARStationaryGaussian

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2500000
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace SafeLearning.CompleteModulesLandscapeARLawLimit
open CompleteModulesLandscapeARGaussianAlgebra CompleteModulesLandscapeARGaussianLaw
open CompleteModulesLandscapeARStableMoments CompleteModulesLandscapeARStationaryGaussian

def actualTimeLaw (k goal sigma : ℝ) (t : ℕ) : Measure ℝ :=
  (noiseLaw t).map (fun w : Fin t → ℝ => trajectory k goal sigma w t)

theorem actual_state_at_its_finite_noise_horizon_is_measurable
    (k goal sigma : ℝ) (t : ℕ) :
    Measurable (fun w : Fin t → ℝ => trajectory k goal sigma w t) :=
  (measurable_pi_apply (⟨t, by omega⟩ : Fin (t+1))).comp
    (actual_finite_trajectory_is_measurable k goal sigma t)

theorem actual_state_at_each_time_has_its_internally_derived_gaussian_law
    (k goal sigma : ℝ) (t : ℕ) :
    actualTimeLaw k goal sigma t =
      gaussianReal (trueMean k goal t) (trueVariance k sigma t).toNNReal :=
  actual_every_state_has_the_true_scalar_gaussian_marginal k goal sigma t ⟨t, by omega⟩

instance (k goal sigma : ℝ) (t : ℕ) : IsProbabilityMeasure (actualTimeLaw k goal sigma t) := by
  rw [actual_state_at_each_time_has_its_internally_derived_gaussian_law]
  infer_instance

def actualTimeProbabilityLaw (k goal sigma : ℝ) (t : ℕ) : ProbabilityMeasure ℝ :=
  (actualTimeLaw k goal sigma t).toProbabilityMeasure
def stationaryProbabilityLaw (k goal sigma : ℝ) : ProbabilityMeasure ℝ :=
  ⟨stationaryLaw k goal sigma, by unfold stationaryLaw; infer_instance⟩

theorem actual_gaussian_probability_measures_converge_weakly_with_their_parameters
    (mean : ℕ → ℝ) (variance : ℕ → NNReal) (limitMean : ℝ) (limitVariance : NNReal)
    (hm : Tendsto mean atTop (𝓝 limitMean))
    (hv : Tendsto (fun t => (variance t : ℝ)) atTop (𝓝 (limitVariance : ℝ))) :
    Tendsto (fun t => (gaussianReal (mean t) (variance t)).toProbabilityMeasure) atTop
      (𝓝 (gaussianReal limitMean limitVariance).toProbabilityMeasure) := by
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro z
  simp only [Measure.toProbabilityMeasure, ProbabilityMeasure.coe_mk, charFun_gaussianReal]
  have hmean : Tendsto (fun t => (mean t : ℂ)) atTop (𝓝 (limitMean : ℂ)) := hm.ofReal
  have hvariance : Tendsto (fun t => ((variance t : ℝ) : ℂ)) atTop
      (𝓝 ((limitVariance : ℝ) : ℂ)) := hv.ofReal
  exact (Complex.continuous_exp.tendsto _).comp
    (((hmean.const_mul (z : ℂ)).mul_const Complex.I).sub
      ((hvariance.mul_const ((z : ℂ)^2)).div_const (2 : ℂ)))

theorem actual_recursive_state_laws_converge_weakly_to_the_actual_stationary_gaussian_law
    (k goal sigma : ℝ) (hk : 0 < k) (hk2 : k < 2) :
    Tendsto (actualTimeProbabilityLaw k goal sigma) atTop
      (𝓝 (stationaryProbabilityLaw k goal sigma)) := by
  have hm := actual_state_mean_converges_to_the_goal_for_every_stable_source_gain k goal hk hk2
  have hv := actual_state_variance_converges_to_the_printed_stationary_variance k sigma hk hk2
  have hv' : Tendsto (fun t => ((trueVariance k sigma t).toNNReal : ℝ)) atTop
      (𝓝 (stationaryVariance k sigma : ℝ)) := by
    simpa only [Real.coe_toNNReal _ (actual_state_variance_is_nonnegative k sigma _),
      actual_stationary_variance_is_the_printed_nonnegative_real_variance k sigma hk hk2] using hv
  have h := actual_gaussian_probability_measures_converge_weakly_with_their_parameters
    (trueMean k goal) (fun t => (trueVariance k sigma t).toNNReal)
    goal (stationaryVariance k sigma) hm hv'
  simpa only [actualTimeProbabilityLaw, actual_state_at_each_time_has_its_internally_derived_gaussian_law,
    stationaryProbabilityLaw, stationaryLaw, Measure.toProbabilityMeasure] using h

theorem actual_recursive_states_converge_in_the_official_distribution_sense
    (k goal sigma : ℝ) (hk : 0 < k) (hk2 : k < 2) :
    TendstoInDistribution (fun t => fun w : Fin t → ℝ => trajectory k goal sigma w t) atTop
      (fun x : ℝ => x) (fun t => noiseLaw t)
      (gaussianReal goal (stationaryVariance k sigma)) := by
  apply TendstoInDistribution.of_tendsto_charFun
    (fun t => (actual_state_at_its_finite_noise_horizon_is_measurable k goal sigma t).aemeasurable)
    measurable_id.aemeasurable
  intro z
  have h := ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp
    (actual_recursive_state_laws_converge_weakly_to_the_actual_stationary_gaussian_law
      k goal sigma hk hk2) z
  change Tendsto (fun t => charFun (actualTimeLaw k goal sigma t) z) atTop
      (𝓝 (charFun (stationaryLaw k goal sigma) z)) at h
  change Tendsto (fun t => charFun (actualTimeLaw k goal sigma t) z) atTop
      (𝓝 (charFun ((gaussianReal goal (stationaryVariance k sigma)).map id) z))
  rw [Measure.map_id]
  exact h

theorem actual_recursive_marginals_converge_against_every_bounded_continuous_observable
    (k goal sigma : ℝ) (hk : 0 < k) (hk2 : k < 2) (f : ℝ →ᵇ ℝ) :
    Tendsto (fun t => ∫x, f x ∂actualTimeLaw k goal sigma t) atTop
      (𝓝 (∫x, f x ∂stationaryLaw k goal sigma)) :=
  ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    (actual_recursive_state_laws_converge_weakly_to_the_actual_stationary_gaussian_law
      k goal sigma hk hk2) f

theorem actual_zero_noise_marginal_law_is_deterministic_at_every_time
    (k goal : ℝ) (t : ℕ) : actualTimeLaw k goal 0 t = Measure.dirac (trueMean k goal t) := by
  rw [actual_state_at_each_time_has_its_internally_derived_gaussian_law]
  simp [trueVariance]

theorem actual_zero_noise_laws_converge_weakly_to_the_deterministic_goal
    (k goal : ℝ) (hk : 0 < k) (hk2 : k < 2) :
    Tendsto (actualTimeProbabilityLaw k goal 0) atTop
      (𝓝 (Measure.dirac goal).toProbabilityMeasure) := by
  simpa [stationaryProbabilityLaw, stationaryLaw, stationaryVariance, Measure.toProbabilityMeasure] using
    actual_recursive_state_laws_converge_weakly_to_the_actual_stationary_gaussian_law k goal 0 hk hk2

end SafeLearning.CompleteModulesLandscapeARLawLimit
