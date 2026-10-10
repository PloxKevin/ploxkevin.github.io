import SafeLearning.CompleteModulesLandscapeVectorSelfNormalized
import SafeLearning.CompleteFoundationsTelescopingModels

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace SafeLearning.CompleteModulesLandscapeScheduledPrior
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped ENNReal NNReal Topology BigOperators
open CompleteAppliedAzuma CompleteAppliedExponentialMartingale
open CompleteModulesLandscapeVectorMixture CompleteModulesLandscapeVectorMixtureJoint
open CompleteModulesLandscapeQuadraticWeights
open CompleteModulesLandscapeContinuousMixture CompleteModulesLandscapeMixtureVille
open CompleteModulesLandscapeVectorSelfNormalized CompleteFoundationsTelescopingModels

variable {feature : Type*} [Fintype feature] [DecidableEq feature]

/-- A fixed Gaussian prior's actual all-time crossing set is measurable,
derived from primitive predictable queries and next-noise measurability. -/
theorem actual_fixed_gaussian_prior_crossing_set_is_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (F : Filtration ℕ mΩ)
    (phi : ℕ → Ω → feature → ℝ) (Y : ℕ → Ω → ℝ)
    (hphi : ∀ i j, StronglyMeasurable[F i] (fun omega => phi i omega j))
    (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i)) (R a : ℝ≥0) (delta : ℝ) :
    MeasurableSet {omega | ∃ n, 1 / delta ≤
      mixture (Measure.pi (fun _ : feature => gaussianReal 0 a))
        (vectorTiltProcess phi Y R) n omega} := by
  have he : {omega | ∃ n, 1 / delta ≤
      mixture (Measure.pi (fun _ : feature => gaussianReal 0 a))
        (vectorTiltProcess phi Y R) n omega} =
      ⋃ n, {omega | 1 / delta ≤
        mixture (Measure.pi (fun _ : feature => gaussianReal 0 a))
          (vectorTiltProcess phi Y R) n omega} := by
    ext omega
    simp
  rw [he]
  apply MeasurableSet.iUnion
  intro n
  exact measurableSet_le measurable_const
    (((mixture_stronglyAdapted _ F _
      (actual_vector_tilt_family_is_jointly_adapted F phi Y hphi hY R)) n).mono (F.le n)).measurable

/-- Every member of a predetermined countable sequence of Gaussian priors
has its own genuine Ville budget; one common event controls every prior and
every sample count. No prior depends on the realized noise or queries. -/
theorem actual_predetermined_gaussian_prior_schedule_has_one_common_alltime_event
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (phi : ℕ → Ω → feature → ℝ) (Y : ℕ → Ω → ℝ)
    (hphi : ∀ i j, StronglyMeasurable[F i] (fun omega => phi i omega j))
    (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i)) (K R : ℝ≥0)
    (a : ℕ → ℝ≥0) (hb : ∀ i j, ∀ᵐ omega ∂μ, |phi i omega j| ≤ K)
    (hYb : ∀ i, ∀ᵐ omega ∂μ, Y i omega ∈ Icc (-(R : ℝ)) R)
    (hz : ∀ i, μ[Y i | F i] =ᵐ[μ] 0) (delta : ℝ) (hd : 0 < delta) :
    1 - delta ≤ μ.real {omega | ∀ m n,
      mixture (Measure.pi (fun _ : feature => gaussianReal 0 (a m)))
        (vectorTiltProcess phi Y R) n omega < 1 / failureShare delta m} := by
  let bad : ℕ → Set Ω := fun m => {omega | ∃ n, 1 / failureShare delta m ≤
    mixture (Measure.pi (fun _ : feature => gaussianReal 0 (a m)))
      (vectorTiltProcess phi Y R) n omega}
  have hm : ∀ m, MeasurableSet (bad m) := fun m =>
    actual_fixed_gaussian_prior_crossing_set_is_measurable F phi Y hphi hY R (a m) _
  have hbound : ∀ m, μ.real (bad m) ≤ failureShare delta m := by
    intro m
    have hdm : 0 < failureShare delta m := by unfold failureShare; positivity
    exact mixture_all_time_crossing_probability μ _ F _
      (actual_bounded_predictable_vector_tilt_family_is_a_supermartingale μ F phi hphi Y hY K R hb hYb hz)
      (actual_vector_tilt_family_is_jointly_adapted F phi Y hphi hY R)
      (actual_vector_tilt_family_is_gaussian_product_integrable μ F phi Y hphi hY K R (a m) hb hYb)
      (fun _ _ _ => (Real.exp_pos _).le)
      (fun theta omega => congrFun (actual_quadratic_weight_process_has_initial_one_and_the_exact_step
        (directionalWeight phi theta) Y R 1).1 omega) _ hdm
  have he := actual_one_event_covering_every_round_has_the_true_probability_guarantee
    μ bad delta hd.le hm hbound
  have heq : (⋂ m, (bad m)ᶜ) = {omega | ∀ m n,
      mixture (Measure.pi (fun _ : feature => gaussianReal 0 (a m)))
        (vectorTiltProcess phi Y R) n omega < 1 / failureShare delta m} := by
    ext omega
    simp [bad, not_le]
  rw [heq] at he
  exact he

/-- The same one-event schedule has internally computed feature-Gram
determinants and noise inverse quadratics at every prior and sample count. -/
theorem actual_predetermined_prior_schedule_has_one_common_matrix_confidence_event
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (phi : ℕ → Ω → feature → ℝ) (Y : ℕ → Ω → ℝ)
    (hphi : ∀ i j, StronglyMeasurable[F i] (fun omega => phi i omega j))
    (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i)) (K R : ℝ≥0)
    (a : ℕ → ℝ≥0) (hb : ∀ i j, ∀ᵐ omega ∂μ, |phi i omega j| ≤ K)
    (hYb : ∀ i, ∀ᵐ omega ∂μ, Y i omega ∈ Icc (-(R : ℝ)) R)
    (hz : ∀ i, μ[Y i | F i] =ᵐ[μ] 0) (delta : ℝ) (hd : 0 < delta) :
    1 - delta ≤ μ.real {omega | ∀ m n,
      (a m : ℝ) * (featureNoiseSum phi Y n omega ⬝ᵥ
        ((1 + (a m : ℝ) • ((R : ℝ) ^ 2 • featureQuadraticGram phi n omega))⁻¹ *ᵥ
          featureNoiseSum phi Y n omega)) <
        Real.log (1 + (a m : ℝ) • ((R : ℝ) ^ 2 • featureQuadraticGram phi n omega)).det +
          2 * Real.log (1 / failureShare delta m)} := by
  have he := actual_predetermined_gaussian_prior_schedule_has_one_common_alltime_event
    μ F phi Y hphi hY K R a hb hYb hz delta hd
  have heq : {omega | ∀ m n,
      mixture (Measure.pi (fun _ : feature => gaussianReal 0 (a m)))
        (vectorTiltProcess phi Y R) n omega < 1 / failureShare delta m} =
      {omega | ∀ m n,
        (a m : ℝ) * (featureNoiseSum phi Y n omega ⬝ᵥ
          ((1 + (a m : ℝ) • ((R : ℝ) ^ 2 • featureQuadraticGram phi n omega))⁻¹ *ᵥ
            featureNoiseSum phi Y n omega)) <
          Real.log (1 + (a m : ℝ) • ((R : ℝ) ^ 2 • featureQuadraticGram phi n omega)).det +
            2 * Real.log (1 / failureShare delta m)} := by
    ext omega
    apply forall_congr'
    intro m
    apply forall_congr'
    intro n
    rw [actual_vector_gaussian_mixture_has_the_exact_self_normalized_value phi Y R (a m)]
    apply actual_vector_gaussian_threshold_is_the_log_determinant_quadratic_bound
    · exact (actual_cumulative_feature_gram_is_positive_semidefinite phi n omega).smul (sq_nonneg _)
    · unfold failureShare
      positivity
  rw [heq] at he
  exact he

end SafeLearning.CompleteModulesLandscapeScheduledPrior

#print axioms SafeLearning.CompleteModulesLandscapeScheduledPrior.actual_fixed_gaussian_prior_crossing_set_is_measurable
#print axioms SafeLearning.CompleteModulesLandscapeScheduledPrior.actual_predetermined_gaussian_prior_schedule_has_one_common_alltime_event
#print axioms SafeLearning.CompleteModulesLandscapeScheduledPrior.actual_predetermined_prior_schedule_has_one_common_matrix_confidence_event
