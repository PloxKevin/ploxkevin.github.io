import SafeLearning.CompleteModulesLandscapeGaussianWeightedMixture

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace SafeLearning.CompleteModulesLandscapeVectorMixture
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Matrix
open CompleteAppliedAzuma CompleteAppliedExponentialMartingale
open CompleteModulesLandscapeQuadraticWeights CompleteModulesLandscapeContinuousMixture
open CompleteModulesLandscapeMixtureVille

variable {feature : Type*} [Fintype feature]

def directionalWeight {Ω : Type*} (phi : ℕ → Ω → feature → ℝ) (theta : feature → ℝ)
    (i : ℕ) (omega : Ω) : ℝ := theta ⬝ᵥ phi i omega

def featureNoiseSum {Ω : Type*} (phi : ℕ → Ω → feature → ℝ) (Y : ℕ → Ω → ℝ)
    (n : ℕ) (omega : Ω) (j : feature) : ℝ :=
  partialSum (fun i omega => phi i omega j * Y i omega) n omega

def featureQuadraticGram {Ω : Type*} (phi : ℕ → Ω → feature → ℝ)
    (n : ℕ) (omega : Ω) : Matrix feature feature ℝ :=
  fun j k => partialSum (fun i omega => phi i omega j * phi i omega k) n omega

def vectorTiltProcess {Ω : Type*} (phi : ℕ → Ω → feature → ℝ)
    (Y : ℕ → Ω → ℝ) (R : ℝ≥0) (theta : feature → ℝ) : ℕ → Ω → ℝ :=
  quadraticProcess (directionalWeight phi theta) Y R 1

/-- Every fixed vector tilt gives an actual predictable bounded scalar projection. -/
theorem actual_predictable_finite_vector_projection_is_measurable_and_bounded
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) (F : Filtration ℕ mΩ)
    (phi : ℕ → Ω → feature → ℝ)
    (hphi : ∀ i j, StronglyMeasurable[F i] (fun omega => phi i omega j)) (K : ℝ≥0)
    (hb : ∀ i j, ∀ᵐ omega ∂μ, |phi i omega j| ≤ K) (theta : feature → ℝ) :
    (∀ i, StronglyMeasurable[F i] (directionalWeight phi theta i)) ∧
      ∀ i, ∀ᵐ omega ∂μ,
        |directionalWeight phi theta i omega| ≤ (K : ℝ) * ∑ j, |theta j| := by
  constructor
  · intro i
    have h : StronglyMeasurable[F i] (∑ j : feature, (fun omega => theta j * phi i omega j)) := by
      apply Finset.stronglyMeasurable_sum
      intro j hj
      exact stronglyMeasurable_const.mul (hphi i j)
    simpa only [directionalWeight,dotProduct,Finset.sum_fn] using h
  · intro i
    filter_upwards [ae_all_iff.mpr (hb i)] with omega hb
    calc
      _ ≤ ∑ j, |theta j * phi i omega j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, |theta j| * (K : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hb j) (abs_nonneg _)
      _ = _ := by rw [Finset.sum_mul,mul_comm]

/-- The scalar projected sum and squared-weight sum are the actual vector
noise and actual cumulative outer-product quadratic, not independent fixtures. -/
theorem actual_vector_projection_sums_are_the_noise_vector_and_gram_quadratic
    {Ω : Type*} (phi : ℕ → Ω → feature → ℝ) (Y : ℕ → Ω → ℝ)
    (theta : feature → ℝ) (n : ℕ) (omega : Ω) :
    partialSum (fun i => directionalWeight phi theta i * Y i) n omega =
      theta ⬝ᵥ featureNoiseSum phi Y n omega ∧
    partialSum (fun i omega => directionalWeight phi theta i omega ^ 2) n omega =
      theta ⬝ᵥ (featureQuadraticGram phi n omega *ᵥ theta) := by
  constructor
  · simp only [partialSum,directionalWeight,featureNoiseSum,dotProduct,Pi.mul_apply]
    simp_rw [Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    ring
  · simp only [partialSum,directionalWeight,featureQuadraticGram,dotProduct,Matrix.mulVec,pow_two]
    simp_rw [Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro i hi
    ring

/-- The true vector family is an exponential process with the actual Gram quadratic. -/
theorem actual_vector_tilt_process_is_the_noise_vector_gram_exponential
    {Ω : Type*} (phi : ℕ → Ω → feature → ℝ) (Y : ℕ → Ω → ℝ)
    (R : ℝ≥0) (theta : feature → ℝ) (n : ℕ) (omega : Ω) :
    vectorTiltProcess phi Y R theta n omega =
      Real.exp (theta ⬝ᵥ featureNoiseSum phi Y n omega -
        (R : ℝ) ^ 2 * (theta ⬝ᵥ (featureQuadraticGram phi n omega *ᵥ theta)) / 2) := by
  have h := actual_vector_projection_sums_are_the_noise_vector_and_gram_quadratic phi Y theta n omega
  simp only [vectorTiltProcess,quadraticProcess,one_mul,one_pow,h.1,h.2]

/-- Arbitrary bounded predictable finite vector features and bounded centered
noise derive every fixed-vector-tilt supermartingale, with actual outer-product variance. -/
theorem actual_bounded_predictable_vector_tilt_family_is_a_supermartingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (phi : ℕ → Ω → feature → ℝ)
    (hphi : ∀ i j, StronglyMeasurable[F i] (fun omega => phi i omega j))
    (Y : ℕ → Ω → ℝ) (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i)) (K R : ℝ≥0)
    (hb : ∀ i j, ∀ᵐ omega ∂μ, |phi i omega j| ≤ K)
    (hYb : ∀ i, ∀ᵐ omega ∂μ, Y i omega ∈ Icc (-(R : ℝ)) R)
    (hz : ∀ i, μ[Y i | F i] =ᵐ[μ] 0) (theta : feature → ℝ) :
    Supermartingale (vectorTiltProcess phi Y R theta) F μ := by
  have hp := actual_predictable_finite_vector_projection_is_measurable_and_bounded μ F phi hphi K hb theta
  let bound : ℝ≥0 := ⟨(K : ℝ) * ∑ j, |theta j|,by positivity⟩
  exact actual_predictable_quadratic_weight_process_is_a_supermartingale μ F _ Y hp.1 hY
    bound R hp.2 hYb hz 1

end SafeLearning.CompleteModulesLandscapeVectorMixture
