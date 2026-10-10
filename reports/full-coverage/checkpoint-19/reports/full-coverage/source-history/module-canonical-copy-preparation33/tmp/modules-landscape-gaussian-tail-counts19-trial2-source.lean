import SafeLearning.CompleteAppliedGaussianCDF
import SafeLearning.CompleteModulesLandscapeFiniteCounts

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SafeLearning.CompleteModulesLandscapeGaussianTailCounts
open CompleteAppliedGaussianCDF CompleteModulesLandscapeFiniteCounts

theorem actual_gaussian_upper_tail_is_the_standard_cdf_complement
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ)
    (mean threshold : ℝ) (sigma : NNReal) (hsigma : sigma ≠ 0)
    (hX : HasLaw X (gaussianReal mean (sigma^2)) P) :
    P.real {ω | threshold < X ω} =
      1-standardCDF ((threshold-mean)/(sigma : ℝ)) := by
  have hsig : 0 < (sigma : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hsigma)
  have hz := gaussianReal_div_const (gaussianReal_sub_const hX mean) (sigma : ℝ)
  have hvar : NNReal.mk ((sigma : ℝ)^2) (sq_nonneg (sigma : ℝ)) = sigma^2 := by
    ext
    rfl
  rw [hvar, div_self (pow_ne_zero 2 hsigma)] at hz
  norm_num only [sub_self, zero_div] at hz
  have hevent := hz.measureReal_eq
    (p := fun z : ℝ => (threshold-mean)/(sigma : ℝ) < z) measurableSet_Ioi
  have he : {ω | (threshold-mean)/(sigma : ℝ) < (X ω-mean)/(sigma : ℝ)} =
      {ω | threshold < X ω} := by
    ext ω
    simp only [mem_setOf_eq, div_lt_div_iff_of_pos_right hsig, sub_lt_sub_iff_right]
  rw [he] at hevent
  have hc := measureReal_compl (μ := gaussianReal 0 1)
    (s := Iic ((threshold-mean)/(sigma : ℝ))) measurableSet_Iic
  have huniv : (gaussianReal 0 1).real univ = 1 := by simp
  rw [compl_Iic, huniv] at hc
  exact hevent.trans hc

theorem actual_nondegenerate_gaussian_upper_tail_is_strictly_positive
    (mean threshold : ℝ) (variance : NNReal) (hvariance : variance ≠ 0) :
    0 < (gaussianReal mean variance).real (Ioi threshold) := by
  have hn : (gaussianReal mean variance) (Ioi threshold) ≠ 0 := by
    intro hzero
    have hv := gaussianReal_absolutelyContinuous' mean hvariance hzero
    simp only [Real.volume_Ioi] at hv
    exact ENNReal.top_ne_zero hv
  exact ENNReal.toReal_pos hn (measure_ne_top _ _)

theorem actual_zero_variance_gaussian_tail_is_the_deterministic_strict_indicator
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ)
    (mean threshold : ℝ) (hX : HasLaw X (gaussianReal mean 0) P) :
    P.real {ω | threshold < X ω} = if threshold < mean then 1 else 0 := by
  have he := hX.measureReal_eq (p := fun x : ℝ => threshold < x) measurableSet_Ioi
  rw [gaussianReal_zero_var] at he
  by_cases h : threshold < mean
  · simpa [Measure.real, Measure.dirac_apply' mean measurableSet_Ioi, h] using he
  · simpa [Measure.real, Measure.dirac_apply' mean measurableSet_Ioi, h] using he

theorem actual_expected_gaussian_violation_count_is_the_sum_of_true_marginal_tails
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N : ℕ) (X : Fin (N+1) → Ω → ℝ)
    (mean : Fin (N+1) → ℝ) (sigma : Fin (N+1) → NNReal) (threshold : ℝ)
    (hmeas : ∀ t, Measurable (X t)) (hpos : ∀ t, sigma t ≠ 0)
    (hlaw : ∀ t, HasLaw (X t) (gaussianReal (mean t) ((sigma t)^2)) P) :
    (∫ ω, unsafeCount (fun t => {ω | threshold < X t ω}) ω ∂P) =
      ∑ t, (1-standardCDF ((threshold-mean t)/(sigma t : ℝ))) := by
  rw [actual_expected_indicator_count_is_sum_of_marginal_probabilities P
    (fun t => {ω | threshold < X t ω})
    (fun t => measurableSet_Ioi.preimage (hmeas t))]
  apply Finset.sum_congr rfl
  intro t _
  exact actual_gaussian_upper_tail_is_the_standard_cdf_complement
    P (X t) (mean t) threshold (sigma t) (hpos t) (hlaw t)

theorem actual_gaussian_marginal_sum_bounds_the_joint_violation_event_without_independence
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N : ℕ) (X : Fin (N+1) → Ω → ℝ)
    (mean : Fin (N+1) → ℝ) (sigma : Fin (N+1) → NNReal) (threshold : ℝ)
    (hmeas : ∀ t, Measurable (X t)) (hpos : ∀ t, sigma t ≠ 0)
    (hlaw : ∀ t, HasLaw (X t) (gaussianReal (mean t) ((sigma t)^2)) P) :
    P.real {ω | ∃ t, threshold < X t ω} ≤
      ∑ t, (1-standardCDF ((threshold-mean t)/(sigma t : ℝ))) := by
  rw [←actual_expected_gaussian_violation_count_is_the_sum_of_true_marginal_tails
    P N X mean sigma threshold hmeas hpos hlaw]
  have h := (actual_failure_probability_and_expected_count_control_each_other_only_up_to_horizon
    P (fun t => {ω | threshold < X t ω})
    (fun t => measurableSet_Ioi.preimage (hmeas t))).1
  simpa only [everUnsafe, mem_iUnion, mem_setOf_eq] using h

end SafeLearning.CompleteModulesLandscapeGaussianTailCounts
