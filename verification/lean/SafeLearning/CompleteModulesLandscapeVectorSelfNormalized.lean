import SafeLearning.CompleteModulesLandscapeVectorMixtureJoint
import SafeLearning.CompleteModulesLandscapeGaussianVectorIntegral

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace SafeLearning.CompleteModulesLandscapeVectorSelfNormalized
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped ENNReal NNReal Topology BigOperators
open CompleteAppliedAzuma CompleteAppliedExponentialMartingale
open CompleteModulesLandscapeVectorMixture CompleteModulesLandscapeVectorMixtureJoint
open CompleteModulesLandscapeContinuousMixture CompleteModulesLandscapeGaussianVectorIntegral
open CompleteModulesSafeOptFiniteInformationBound

variable {feature : Type*} [Fintype feature] [DecidableEq feature]

def vectorGaussianValue (a : ℝ≥0) (V : Matrix feature feature ℝ) (S : feature → ℝ) : ℝ :=
  (Real.sqrt (1 + (a : ℝ) • V).det)⁻¹ *
    Real.exp ((a : ℝ) / 2 * (S ⬝ᵥ ((1 + (a : ℝ) • V)⁻¹ *ᵥ S)))

/-- The actual cumulative feature outer-product matrix is positive
semidefinite, derived from its sum of squared directional projections. -/
theorem actual_cumulative_feature_gram_is_positive_semidefinite
    {Ω : Type*} (phi : ℕ → Ω → feature → ℝ) (n : ℕ) (omega : Ω) :
    (featureQuadraticGram phi n omega).PosSemidef := by
  have hh : (featureQuadraticGram phi n omega).IsHermitian := by
    ext j k
    simp [Matrix.conjTranspose, featureQuadraticGram, partialSum, mul_comm]
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hh
  intro theta
  have h := (actual_vector_projection_sums_are_the_noise_vector_and_gram_quadratic
    phi (fun _ _ => 0) theta n omega).2
  have hs : 0 ≤ partialSum (fun i omega => directionalWeight phi theta i omega ^ 2) n omega :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  simpa only [star_trivial, h] using hs

/-- The actual integrated exponential process equals the determinant and
inverse quadratic of its own cumulative feature Gram and noise vector. -/
theorem actual_vector_gaussian_mixture_has_the_exact_self_normalized_value
    {Ω : Type*} (phi : ℕ → Ω → feature → ℝ) (Y : ℕ → Ω → ℝ) (R a : ℝ≥0) :
    mixture (Measure.pi (fun _ : feature => gaussianReal 0 a)) (vectorTiltProcess phi Y R) =
      fun n omega => vectorGaussianValue a ((R : ℝ) ^ 2 • featureQuadraticGram phi n omega)
        (featureNoiseSum phi Y n omega) := by
  funext n omega
  unfold mixture vectorGaussianValue
  convert actual_finite_coordinate_psd_gaussian_quadratic_integral_has_the_exact_determinant_value
    a ((R : ℝ) ^ 2 • featureQuadraticGram phi n omega)
    ((actual_cumulative_feature_gram_is_positive_semidefinite phi n omega).smul (sq_nonneg _))
    (featureNoiseSum phi Y n omega) using 1
  congr 1
  funext theta
  rw [actual_vector_tilt_process_is_the_noise_vector_gram_exponential]
  congr 1
  simp only [Matrix.smul_mulVec, dotProduct_smul]
  ring

/-- Positive normalized determinants make the ordinary logarithmic
threshold exactly equivalent to the actual self-normalized quadratic bound. -/
theorem actual_vector_gaussian_threshold_is_the_log_determinant_quadratic_bound
    (a : ℝ≥0) (V : Matrix feature feature ℝ) (hV : V.PosSemidef) (S : feature → ℝ)
    (delta : ℝ) (hd : 0 < delta) :
    vectorGaussianValue a V S < 1 / delta ↔
      (a : ℝ) * (S ⬝ᵥ ((1 + (a : ℝ) • V)⁻¹ *ᵥ S)) <
        Real.log (1 + (a : ℝ) • V).det + 2 * Real.log (1 / delta) := by
  have hD : 0 < (1 + (a : ℝ) • V).det := lt_of_lt_of_le zero_lt_one
    (actual_positive_semidefinite_normalized_determinant_is_a_positive_spectral_product V hV a a.coe_nonneg).2
  have hs : 0 < Real.sqrt (1 + (a : ℝ) • V).det := Real.sqrt_pos.mpr hD
  unfold vectorGaussianValue
  rw [inv_mul_lt_iff₀ hs, ← Real.lt_log_iff_exp_lt (by positivity),
    Real.log_mul hs.ne' (by positivity), Real.log_sqrt hD.le]
  constructor <;> intro h <;> nlinarith

/-- Bounded predictable finite features and bounded centered noise yield
one genuine all-time matrix self-normalized event with probability at least
1-delta. The determinant and noise quadratic are both derived internally. -/
theorem actual_all_time_finite_feature_self_normalized_matrix_confidence
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (phi : ℕ → Ω → feature → ℝ) (Y : ℕ → Ω → ℝ)
    (hphi : ∀ i j, StronglyMeasurable[F i] (fun omega => phi i omega j))
    (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i)) (K R a : ℝ≥0)
    (hb : ∀ i j, ∀ᵐ omega ∂μ, |phi i omega j| ≤ K)
    (hYb : ∀ i, ∀ᵐ omega ∂μ, Y i omega ∈ Icc (-(R : ℝ)) R)
    (hz : ∀ i, μ[Y i | F i] =ᵐ[μ] 0) (delta : ℝ) (hd : 0 < delta) :
    1 - delta ≤ μ.real {omega | ∀ n,
      (a : ℝ) * (featureNoiseSum phi Y n omega ⬝ᵥ
        ((1 + (a : ℝ) • ((R : ℝ) ^ 2 • featureQuadraticGram phi n omega))⁻¹ *ᵥ
          featureNoiseSum phi Y n omega)) <
        Real.log (1 + (a : ℝ) • ((R : ℝ) ^ 2 • featureQuadraticGram phi n omega)).det +
          2 * Real.log (1 / delta)} := by
  have he := actual_all_time_vector_gaussian_mixture_confidence_event μ F phi Y hphi hY K R a hb hYb hz delta hd
  rw [actual_vector_gaussian_mixture_has_the_exact_self_normalized_value phi Y R a] at he
  convert he using 2
  ext omega
  apply forall_congr'
  intro n
  exact (actual_vector_gaussian_threshold_is_the_log_determinant_quadratic_bound a
    ((R : ℝ) ^ 2 • featureQuadraticGram phi n omega)
    ((actual_cumulative_feature_gram_is_positive_semidefinite phi n omega).smul (sq_nonneg _))
    (featureNoiseSum phi Y n omega) delta hd).symm

end SafeLearning.CompleteModulesLandscapeVectorSelfNormalized
