import SafeLearning.CompleteModulesLandscapeScheduledPrior
import SafeLearning.CompleteModulesLandscapeSuiQuadratic
import SafeLearning.CompleteModulesLandscapeZeroInformation

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace SafeLearning.CompleteModulesLandscapeSuiFeatureConfidence
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped ENNReal NNReal Topology BigOperators
open CompleteAppliedAzuma CompleteAppliedExponentialMartingale
open CompleteModulesLandscapeVectorMixture CompleteModulesLandscapeVectorSelfNormalized
open CompleteModulesLandscapeGaussianGPRegularization CompleteModulesLandscapeScheduledPrior
open CompleteModulesLandscapeSuiQuadratic CompleteModulesLandscapeZeroInformation
open CompleteFoundationsTelescopingModels

def actualSourceInformationRegularizer (lambda Gamma : ℝ) : ℝ :=
  if Gamma ≤ 1 / 2 then lambda * Gamma else lambda

def actualSourceInformationPrior (R lambda Gamma : ℝ) : ℝ≥0 :=
  Real.toNNReal (1 / (R ^ 2 * actualSourceInformationRegularizer lambda Gamma))

theorem actual_positive_information_regularizer_is_positive
    (lambda Gamma : ℝ) (hlambda : 0 < lambda) (hGamma : 0 < Gamma) :
    0 < actualSourceInformationRegularizer lambda Gamma := by
  unfold actualSourceInformationRegularizer
  split_ifs <;> positivity

/-- Each scheduled prior uses only the predetermined information upper
bound. On its positive domain it is exactly the prior whose Gaussian
normalization gives the corresponding actual regularized inverse. -/
theorem actual_source_information_prior_is_the_true_positive_gp_prior
    (R lambda Gamma : ℝ) (hR : 0 < R) (hlambda : 0 < lambda) (hGamma : 0 < Gamma) :
    actualSourceInformationPrior R lambda Gamma =
      actualGPIsotropicPriorVariance R (actualSourceInformationRegularizer lambda Gamma)
        hR (actual_positive_information_regularizer_is_positive lambda Gamma hlambda hGamma) := by
  apply Subtype.ext
  change (Real.toNNReal (1 / (R ^ 2 * actualSourceInformationRegularizer lambda Gamma)) : ℝ) = _
  rw [Real.coe_toNNReal _ (by
    have hr := actual_positive_information_regularizer_is_positive lambda Gamma hlambda hGamma
    positivity)]
  rfl

variable {feature : Type*} [Fintype feature] [DecidableEq feature]

/-- A zero cumulative feature Gram forces every actual sampled coordinate
to vanish, so its same observed feature-noise sum is zero for any noise. -/
theorem actual_zero_cumulative_feature_gram_forces_the_actual_noise_sum_to_vanish
    {Ω : Type*} (phi : ℕ → Ω → feature → ℝ) (Y : ℕ → Ω → ℝ)
    (n : ℕ) (omega : Ω) (hzero : featureQuadraticGram phi n omega = 0) :
    featureNoiseSum phi Y n omega = 0 := by
  have hphi : ∀ i, i ∈ Finset.range n → ∀ j, phi i omega j = 0 := by
    intro i hi j
    have hdiag : (∑ k ∈ Finset.range n, phi k omega j * phi k omega j) = 0 := by
      simpa only [featureQuadraticGram, partialSum, Matrix.zero_apply] using
        congrArg (fun A : Matrix feature feature ℝ => A j j) hzero
    have hs := Finset.single_le_sum (fun k _ => mul_self_nonneg (phi k omega j)) hi
    rw [hdiag] at hs
    nlinarith [mul_self_nonneg (phi i omega j)]
  ext j
  change (∑ i ∈ Finset.range n, phi i omega j * Y i omega) = 0
  exact Finset.sum_eq_zero (fun i hi => by rw [hphi i hi j, zero_mul])

/-- Primitive predictable bounded features and conditionally centered
bounded noise derive a common actual all-time inverse-quadratic event with
the literal 300 information/log-cubed coefficient. Every information bound
is deterministic and bounds the same computed feature Gram. -/
theorem actual_alltime_feature_noise_has_the_source_information_log_cubed_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (phi : ℕ → Ω → feature → ℝ) (Y : ℕ → Ω → ℝ)
    (hphi : ∀ i j, StronglyMeasurable[F i] (fun omega => phi i omega j))
    (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i)) (K R : ℝ≥0)
    (hb : ∀ i j, ∀ᵐ omega ∂μ, |phi i omega j| ≤ K)
    (hYb : ∀ i, ∀ᵐ omega ∂μ, Y i omega ∈ Icc (-(R : ℝ)) R)
    (hz : ∀ i, μ[Y i | F i] =ᵐ[μ] 0) (hR : 0 < (R : ℝ))
    (lambda : ℝ) (hlambda : 0 < lambda) (hscale : (R : ℝ) ^ 2 ≤ lambda)
    (Gamma : ℕ → ℝ) (hGamma : ∀ t, 0 ≤ Gamma t)
    (hinfo : ∀ n omega, Real.log (1 + lambda⁻¹ • featureQuadraticGram phi n omega).det ≤
      2 * Gamma (n + 1)) (delta : ℝ) (hd : 0 < delta) (hdone : delta < 1) :
    1 - delta ≤ μ.real {omega | ∀ n,
      2 * ((featureNoiseSum phi Y n omega ⬝ᵥ
        ((lambda • 1 + featureQuadraticGram phi n omega)⁻¹ *ᵥ
          featureNoiseSum phi Y n omega)) / lambda) ≤
        300 * Gamma (n + 1) * (Real.log (((n + 1 : ℕ) : ℝ) / delta)) ^ 3} := by
  let a : ℕ → ℝ≥0 := fun m => actualSourceInformationPrior R lambda (Gamma (m + 2))
  have he := actual_predetermined_prior_schedule_has_one_common_matrix_confidence_event
    μ F phi Y hphi hY K R a hb hYb hz delta hd
  apply he.trans
  apply measureReal_mono _ (measure_ne_top μ _)
  intro omega hw n
  cases n with
  | zero =>
    have hlog : 0 ≤ Real.log (1 / delta) := Real.log_nonneg ((one_le_div hd).mpr hdone.le)
    have hbound : 0 ≤ 300 * Gamma 1 * (Real.log (1 / delta)) ^ 3 :=
      mul_nonneg (mul_nonneg (by norm_num) (hGamma 1)) (pow_nonneg hlog _)
    have hzS : featureNoiseSum phi Y 0 omega = 0 := by
      ext j
      simp [featureNoiseSum, CompleteAppliedAzuma.partialSum]
    rw [hzS]
    simpa using hbound
  | succ m =>
    have hG := actual_cumulative_feature_gram_is_positive_semidefinite phi (m + 1) omega
    by_cases hg : 0 < Gamma (m + 2)
    · have hr := actual_positive_information_regularizer_is_positive lambda (Gamma (m + 2)) hlambda hg
      have hn := hw m (m + 1)
      dsimp only [a] at hn
      rw [actual_source_information_prior_is_the_true_positive_gp_prior R lambda (Gamma (m + 2)) hR hlambda hg,
        actual_gp_scaled_prior_quadratic_is_the_actual_regularized_quadratic _ hG _ R _ hR hr,
        actual_gp_prior_normalized_determinant_is_the_actual_normalized_determinant _ R _ hR hr] at hn
      have hcast : m + 1 + 1 = m + 2 := by omega
      have hindex : m + 2 - 2 = m := by omega
      by_cases hhalf : Gamma (m + 2) ≤ 1 / 2
      · simp only [actualSourceInformationRegularizer, if_pos hhalf] at hn
        have hh := actual_small_information_inverse_budget_implies_source_three_hundred_bound
          _ hG _ R lambda (Gamma (m + 2)) delta hR hlambda hscale hg hhalf hd hdone (m + 2)
          (by omega) (by simpa only [hcast] using hinfo (m + 1) omega) (by simpa only [hindex] using hn)
        simpa only [Nat.succ_eq_add_one, hcast] using hh
      · simp only [actualSourceInformationRegularizer, if_neg hhalf] at hn
        have hh := actual_large_information_inverse_budget_implies_source_three_hundred_bound
          _ hG _ R lambda (Gamma (m + 2)) delta hR hlambda hscale (le_of_lt (lt_of_not_ge hhalf))
          hd hdone (m + 2) (by omega) (by simpa only [hcast] using hinfo (m + 1) omega)
          (by simpa only [hindex] using hn)
        simpa only [Nat.succ_eq_add_one, hcast] using hh
    · have hgz : Gamma (m + 2) = 0 := le_antisymm (le_of_not_gt hg) (hGamma _)
      have hsmall : (1 / 2) * Real.log (1 + lambda⁻¹ • featureQuadraticGram phi (m + 1) omega).det ≤ 0 := by
        have hi := hinfo (m + 1) omega
        have hh : m + 1 + 1 = m + 2 := by omega
        rw [hh, hgz] at hi
        linarith
      have hzG := actual_nonpositive_normalized_psd_information_forces_the_matrix_to_vanish
        _ hG lambda hlambda hsmall
      have hzS := actual_zero_cumulative_feature_gram_forces_the_actual_noise_sum_to_vanish phi Y (m + 1) omega hzG
      have hh : m + 1 + 1 = m + 2 := by omega
      rw [hh, hgz, hzS]
      simp

end SafeLearning.CompleteModulesLandscapeSuiFeatureConfidence

#print axioms SafeLearning.CompleteModulesLandscapeSuiFeatureConfidence.actual_positive_information_regularizer_is_positive
#print axioms SafeLearning.CompleteModulesLandscapeSuiFeatureConfidence.actual_source_information_prior_is_the_true_positive_gp_prior
#print axioms SafeLearning.CompleteModulesLandscapeSuiFeatureConfidence.actual_zero_cumulative_feature_gram_forces_the_actual_noise_sum_to_vanish
#print axioms SafeLearning.CompleteModulesLandscapeSuiFeatureConfidence.actual_alltime_feature_noise_has_the_source_information_log_cubed_budget
