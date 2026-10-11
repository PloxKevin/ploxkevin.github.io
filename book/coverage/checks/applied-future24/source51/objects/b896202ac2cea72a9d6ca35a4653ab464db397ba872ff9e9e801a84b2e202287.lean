import SafeLearning.CompleteModulesLandscapeVectorMixture
import Mathlib.MeasureTheory.Integral.Pi

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace SafeLearning.CompleteModulesLandscapeVectorMixtureJoint
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Matrix
open CompleteAppliedAzuma CompleteAppliedExponentialMartingale
open CompleteModulesLandscapeQuadraticWeights CompleteModulesLandscapeContinuousMixture
open CompleteModulesLandscapeMixtureVille CompleteModulesLandscapeVectorMixture

variable {feature : Type*} [Fintype feature]

/-- The actual vector family is jointly measurable in the current filtration
and every coordinate of the Gaussian tilt, including an empty feature family. -/
theorem actual_vector_tilt_family_is_jointly_adapted
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (F : Filtration ℕ mΩ)
    (phi : ℕ → Ω → feature → ℝ) (Y : ℕ → Ω → ℝ)
    (hphi : ∀ i j, StronglyMeasurable[F i] (fun omega => phi i omega j))
    (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i)) (R : ℝ≥0) (n : ℕ) :
    StronglyMeasurable[(F n).prod inferInstance]
      (fun p : Ω × (feature → ℝ) => vectorTiltProcess phi Y R p.2 n p.1) := by
  have hp : ∀ i, i ∈ Finset.range n → ∀ j,
      StronglyMeasurable[F n] (fun omega => phi i omega j) := by
    intro i hi j
    exact (hphi i j).mono (F.mono (by have := Finset.mem_range.mp hi; omega))
  have hy : ∀ i, i ∈ Finset.range n → StronglyMeasurable[F n] (Y i) := by
    intro i hi
    exact (hY i).mono (F.mono (by have := Finset.mem_range.mp hi; omega))
  let : MeasurableSpace Ω := F n
  have hq : ∀ i, i ∈ Finset.range n →
      Measurable (fun p : Ω × (feature → ℝ) => directionalWeight phi p.2 i p.1) := by
    intro i hi
    unfold directionalWeight dotProduct
    apply Finset.measurable_sum
    intro j hj
    exact ((measurable_pi_apply j).comp measurable_snd).mul ((hp i hi j).measurable.comp measurable_fst)
  have hs : Measurable (fun p : Ω × (feature → ℝ) =>
      partialSum (fun i => directionalWeight phi p.2 i * Y i) n p.1) := by
    unfold partialSum
    apply Finset.measurable_sum
    intro i hi
    exact (hq i hi).mul ((hy i hi).measurable.comp measurable_fst)
  have hv : Measurable (fun p : Ω × (feature → ℝ) =>
      partialSum (fun i omega => directionalWeight phi p.2 i omega ^ 2) n p.1) := by
    unfold partialSum
    exact Finset.measurable_sum _ (fun i hi => (hq i hi).pow_const 2)
  change StronglyMeasurable (fun p : Ω × (feature → ℝ) => vectorTiltProcess phi Y R p.2 n p.1)
  simpa [vectorTiltProcess, quadraticProcess] using
    ((hs.sub ((hv.const_mul ((R : ℝ) ^ 2)).div_const 2)).exp.stronglyMeasurable)

/-- Product integrability follows from the actual coordinate noise sums being
bounded, and from finite products of genuine Gaussian exponential moments. -/
theorem actual_vector_tilt_family_is_gaussian_product_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (phi : ℕ → Ω → feature → ℝ) (Y : ℕ → Ω → ℝ)
    (hphi : ∀ i j, StronglyMeasurable[F i] (fun omega => phi i omega j))
    (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i)) (K R a : ℝ≥0)
    (hb : ∀ i j, ∀ᵐ omega ∂μ, |phi i omega j| ≤ K)
    (hYb : ∀ i, ∀ᵐ omega ∂μ, Y i omega ∈ Icc (-(R : ℝ)) R) (n : ℕ) :
    Integrable (fun p : Ω × (feature → ℝ) => vectorTiltProcess phi Y R p.2 n p.1)
      (μ.prod (Measure.pi (fun _ : feature => gaussianReal 0 a))) := by
  have hm := actual_vector_tilt_family_is_jointly_adapted F phi Y hphi hY R n
  have hle : (F n).prod (inferInstance : MeasurableSpace (feature → ℝ)) ≤
      mΩ.prod (inferInstance : MeasurableSpace (feature → ℝ)) := by
    exact sup_le_sup (MeasurableSpace.comap_mono (F.le n)) le_rfl
  have hm' := (hm.mono hle).measurable
  let C : ℝ := (n : ℝ) * (K : ℝ) * (R : ℝ)
  have hC : 0 ≤ C := by positivity
  have hs : ∀ᵐ omega ∂μ, ∀ j, |featureNoiseSum phi Y n omega j| ≤ C := by
    have hphi' : ∀ᵐ omega ∂μ, ∀ i j, |phi i omega j| ≤ K :=
      ae_all_iff.mpr (fun i => ae_all_iff.mpr (hb i))
    filter_upwards [hphi', ae_all_iff.mpr hYb] with omega hphi' hYb
    intro j
    calc
      _ ≤ ∑ i ∈ Finset.range n, |phi i omega j * Y i omega| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range n, (K : ℝ) * (R : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul]
        exact mul_le_mul (hphi' i j) (abs_le.mpr (hYb i)) (abs_nonneg _) K.property
      _ = C := by simp [C]; ring
  have hi : Integrable (fun theta : feature → ℝ =>
      ∏ j, (Real.exp (C * theta j) + Real.exp (-C * theta j)))
      (Measure.pi (fun _ : feature => gaussianReal 0 a)) := by
    exact Integrable.fintype_prod (fun _ =>
      (integrable_exp_mul_gaussianReal C).add (integrable_exp_mul_gaussianReal (-C)))
  apply (hi.comp_snd μ).mono' hm'.aestronglyMeasurable
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hs] with p hp
  rw [actual_vector_tilt_process_is_the_noise_vector_gram_exponential,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hQ : 0 ≤ p.2 ⬝ᵥ (featureQuadraticGram phi n p.1 *ᵥ p.2) := by
    rw [← (actual_vector_projection_sums_are_the_noise_vector_and_gram_quadratic phi Y p.2 n p.1).2]
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hlin : p.2 ⬝ᵥ featureNoiseSum phi Y n p.1 ≤ C * ∑ j, |p.2 j| := by
    calc
      _ ≤ ∑ j, |p.2 j * featureNoiseSum phi Y n p.1 j| := by
        exact (le_abs_self _).trans (Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ j, C * |p.2 j| := by
        apply Finset.sum_le_sum
        intro j hj
        rw [abs_mul, mul_comm C]
        exact mul_le_mul_of_nonneg_left (hp j) (abs_nonneg _)
      _ = _ := by rw [Finset.mul_sum]
  have he : Real.exp (p.2 ⬝ᵥ featureNoiseSum phi Y n p.1 -
      (R : ℝ) ^ 2 * (p.2 ⬝ᵥ (featureQuadraticGram phi n p.1 *ᵥ p.2)) / 2) ≤
      Real.exp (C * ∑ j, |p.2 j|) := by
    apply Real.exp_le_exp.mpr
    have hnonneg : 0 ≤ (R : ℝ) ^ 2 * (p.2 ⬝ᵥ (featureQuadraticGram phi n p.1 *ᵥ p.2)) / 2 := by positivity
    linarith
  apply he.trans
  rw [Finset.mul_sum, Real.exp_sum]
  apply Finset.prod_le_prod₀
  · intro j hj
    exact (Real.exp_pos _).le
  · intro j hj
    by_cases htheta : 0 ≤ p.2 j
    · rw [abs_of_nonneg htheta]
      exact le_add_of_nonneg_right (Real.exp_pos _).le
    · rw [abs_of_neg (lt_of_not_ge htheta)]
      have hneg : C * -p.2 j = -C * p.2 j := by ring
      rw [hneg]
      exact le_add_of_nonneg_left (Real.exp_pos _).le

/-- Primitive bounded predictable features and centered bounded noise derive
the actual Gaussian-vector mixture supermartingale. -/
theorem actual_vector_gaussian_mixture_is_a_supermartingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (phi : ℕ → Ω → feature → ℝ) (Y : ℕ → Ω → ℝ)
    (hphi : ∀ i j, StronglyMeasurable[F i] (fun omega => phi i omega j))
    (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i)) (K R a : ℝ≥0)
    (hb : ∀ i j, ∀ᵐ omega ∂μ, |phi i omega j| ≤ K)
    (hYb : ∀ i, ∀ᵐ omega ∂μ, Y i omega ∈ Icc (-(R : ℝ)) R)
    (hz : ∀ i, μ[Y i | F i] =ᵐ[μ] 0) :
    Supermartingale (mixture (Measure.pi (fun _ : feature => gaussianReal 0 a))
      (vectorTiltProcess phi Y R)) F μ := by
  exact mixture_supermartingale μ _ F _
    (actual_bounded_predictable_vector_tilt_family_is_a_supermartingale μ F phi hphi Y hY K R hb hYb hz)
    (actual_vector_tilt_family_is_jointly_adapted F phi Y hphi hY R)
    (actual_vector_tilt_family_is_gaussian_product_integrable μ F phi Y hphi hY K R a hb hYb)

/-- The actual integrated vector-tilt process gives one simultaneous all-time
event of probability at least 1-delta, without an assumed confidence event. -/
theorem actual_all_time_vector_gaussian_mixture_confidence_event
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (phi : ℕ → Ω → feature → ℝ) (Y : ℕ → Ω → ℝ)
    (hphi : ∀ i j, StronglyMeasurable[F i] (fun omega => phi i omega j))
    (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i)) (K R a : ℝ≥0)
    (hb : ∀ i j, ∀ᵐ omega ∂μ, |phi i omega j| ≤ K)
    (hYb : ∀ i, ∀ᵐ omega ∂μ, Y i omega ∈ Icc (-(R : ℝ)) R)
    (hz : ∀ i, μ[Y i | F i] =ᵐ[μ] 0) (delta : ℝ) (hd : 0 < delta) :
    1 - delta ≤ μ.real {omega | ∀ n,
      mixture (Measure.pi (fun _ : feature => gaussianReal 0 a))
        (vectorTiltProcess phi Y R) n omega < 1 / delta} := by
  exact mixture_simultaneous_confidence_event μ _ F _
    (actual_bounded_predictable_vector_tilt_family_is_a_supermartingale μ F phi hphi Y hY K R hb hYb hz)
    (actual_vector_tilt_family_is_jointly_adapted F phi Y hphi hY R)
    (actual_vector_tilt_family_is_gaussian_product_integrable μ F phi Y hphi hY K R a hb hYb)
    (fun _ _ _ => (Real.exp_pos _).le)
    (fun theta omega => congrFun (actual_quadratic_weight_process_has_initial_one_and_the_exact_step
      (directionalWeight phi theta) Y R 1).1 omega) delta hd

end SafeLearning.CompleteModulesLandscapeVectorMixtureJoint
