import SafeLearning.CompleteModulesLandscapeQuadraticWeights
import SafeLearning.CompleteModulesLandscapeScalarGaussianMixture
import SafeLearning.CompleteModulesLandscapeMixtureVille

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteModulesLandscapeGaussianWeightedMixture
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open CompleteAppliedAzuma CompleteAppliedExponentialMartingale
open CompleteModulesLandscapeQuadraticWeights CompleteModulesLandscapeScalarGaussianMixture
open CompleteModulesLandscapeContinuousMixture CompleteModulesLandscapeMixtureVille

def weightedGaussianProcess {Ω : Type*} (q Y : ℕ → Ω → ℝ) (R a : ℝ≥0)
    (n : ℕ) (omega : Ω) : ℝ :=
  mixtureValue a ((R : ℝ) ^ 2 * partialSum (fun i omega => q i omega ^ 2) n omega)
    (partialSum (fun i => q i * Y i) n omega)

/-- Adaptation is joint with the real Gaussian tilt, not only pointwise in a fixed tilt. -/
theorem actual_weighted_quadratic_tilt_family_is_jointly_adapted
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (F : Filtration ℕ mΩ)
    (q Y : ℕ → Ω → ℝ) (hq : ∀ i, StronglyMeasurable[F i] (q i))
    (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i)) (R : ℝ≥0) (n : ℕ) :
    StronglyMeasurable[(F n).prod inferInstance]
      (fun p : Ω × ℝ => quadraticProcess q Y R p.2 n p.1) := by
  have hprod : ∀ i, StronglyMeasurable[F (i + 1)] (q i * Y i) :=
    fun i => ((hq i).mono (F.mono (Nat.le_succ i))).mul (hY i)
  have hquad : ∀ i, StronglyMeasurable[F (i + 1)] (fun omega => q i omega ^ 2) :=
    fun i => ((hq i).mono (F.mono (Nat.le_succ i))).pow 2
  have hs := partialSum_adapted F _ hprod n
  have hv := partialSum_adapted F _ hquad n
  let : MeasurableSpace Ω := F n
  change StronglyMeasurable (fun p : Ω × ℝ => quadraticProcess q Y R p.2 n p.1)
  exact ((measurable_snd.mul (hs.measurable.comp measurable_fst)).sub
    (((measurable_snd.pow_const 2).mul_const ((R : ℝ) ^ 2)).mul
      (hv.measurable.comp measurable_fst) |>.div_const 2)).exp.stronglyMeasurable

/-- The genuine joint product integral is finite. The accumulated weighted noise
is bounded by n*K*R almost surely, so two actual Gaussian exponential moments dominate it. -/
theorem actual_weighted_quadratic_tilt_family_is_gaussian_product_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (q Y : ℕ → Ω → ℝ) (hq : ∀ i, StronglyMeasurable[F i] (q i))
    (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i)) (K R a : ℝ≥0)
    (hqbound : ∀ i, ∀ᵐ omega ∂μ, |q i omega| ≤ K)
    (hYbound : ∀ i, ∀ᵐ omega ∂μ, Y i omega ∈ Icc (-(R : ℝ)) R) (n : ℕ) :
    Integrable (fun p : Ω × ℝ => quadraticProcess q Y R p.2 n p.1) (μ.prod (gaussianReal 0 a)) := by
  have hprod : ∀ i, StronglyMeasurable[F (i + 1)] (q i * Y i) :=
    fun i => ((hq i).mono (F.mono (Nat.le_succ i))).mul (hY i)
  have hquad : ∀ i, StronglyMeasurable[F (i + 1)] (fun omega => q i omega ^ 2) :=
    fun i => ((hq i).mono (F.mono (Nat.le_succ i))).pow 2
  have hs := ((partialSum_adapted F _ hprod n).mono (F.le n)).measurable
  have hv := ((partialSum_adapted F _ hquad n).mono (F.le n)).measurable
  have hm : Measurable (fun p : Ω × ℝ => quadraticProcess q Y R p.2 n p.1) :=
    ((measurable_snd.mul (hs.comp measurable_fst)).sub
      (((measurable_snd.pow_const 2).mul_const ((R : ℝ) ^ 2)).mul
        (hv.comp measurable_fst) |>.div_const 2)).exp
  let C : ℝ := (n : ℝ) * (K : ℝ) * (R : ℝ)
  have hb : ∀ᵐ omega ∂μ, |partialSum (fun i => q i * Y i) n omega| ≤ C := by
    filter_upwards [ae_all_iff.mpr hqbound,ae_all_iff.mpr hYbound] with omega hqbound hYbound
    calc
      _ ≤ ∑ i ∈ Finset.range n, |q i omega * Y i omega| := by
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range n, (K : ℝ) * (R : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul]
        exact mul_le_mul (hqbound i) (abs_le.mpr (hYbound i)) (abs_nonneg _) K.property
      _ = C := by simp [C]; ring
  have hi : Integrable (fun theta : ℝ => Real.exp (C * theta) + Real.exp (-C * theta))
      (gaussianReal 0 a) := (integrable_exp_mul_gaussianReal C).add (integrable_exp_mul_gaussianReal (-C))
  apply (hi.comp_snd μ).mono' hm.aestronglyMeasurable
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hb] with p hp
  change ‖Real.exp (p.2 * partialSum (fun i => q i * Y i) n p.1 -
    p.2 ^ 2 * (R : ℝ) ^ 2 * partialSum (fun i omega => q i omega ^ 2) n p.1 / 2)‖ ≤ _
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  have hQ : 0 ≤ partialSum (fun i omega => q i omega ^ 2) n p.1 := by
    unfold partialSum
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcomp : 0 ≤ p.2 ^ 2 * (R : ℝ) ^ 2 * partialSum (fun i omega => q i omega ^ 2) n p.1 / 2 := by positivity
  have hlin : p.2 * partialSum (fun i => q i * Y i) n p.1 ≤ C * |p.2| := by
    calc
      _ ≤ |p.2 * partialSum (fun i => q i * Y i) n p.1| := le_abs_self _
      _ = |p.2| * |partialSum (fun i => q i * Y i) n p.1| := abs_mul _ _
      _ ≤ |p.2| * C := mul_le_mul_of_nonneg_left hp (abs_nonneg _)
      _ = _ := mul_comm _ _
  have he : quadraticProcess q Y R p.2 n p.1 ≤ Real.exp (C * |p.2|) := by
    apply Real.exp_le_exp.mpr
    change p.2 * partialSum _ n p.1 - _ ≤ _
    linarith
  apply he.trans
  by_cases htheta : 0 ≤ p.2
  · rw [abs_of_nonneg htheta]
    exact le_add_of_nonneg_right (Real.exp_pos _).le
  · rw [abs_of_neg (lt_of_not_ge htheta)]
    have e : C * -p.2 = -C * p.2 := by ring
    rw [e]
    exact le_add_of_nonneg_left (Real.exp_pos _).le

/-- The actual Gaussian integral equals the explicit self-normalized process. -/
theorem actual_weighted_gaussian_mixture_is_the_exact_self_normalized_process
    {Ω : Type*} (q Y : ℕ → Ω → ℝ) (R a : ℝ≥0) (ha : 0 < a) :
    mixture (gaussianReal 0 a) (quadraticProcess q Y R) = weightedGaussianProcess q Y R a := by
  funext n omega
  have hQ : 0 ≤ partialSum (fun i omega => q i omega ^ 2) n omega := by
    unfold partialSum
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  unfold mixture weightedGaussianProcess
  convert actual_gaussian_tilt_integral_is_the_exact_scalar_self_normalized_value
    a ha ((R : ℝ) ^ 2 * partialSum (fun i omega => q i omega ^ 2) n omega)
    (partialSum (fun i => q i * Y i) n omega) (by positivity) using 1
  congr 1
  funext tilt
  unfold quadraticProcess
  congr 1
  ring

/-- Bounded predictable weights and centered bounded noise derive the genuine
Gaussian mixture supermartingale, with its actual random quadratic variance. -/
theorem actual_weighted_gaussian_self_normalized_process_is_a_supermartingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (q Y : ℕ → Ω → ℝ) (hq : ∀ i, StronglyMeasurable[F i] (q i))
    (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i)) (K R a : ℝ≥0) (ha : 0 < a)
    (hqbound : ∀ i, ∀ᵐ omega ∂μ, |q i omega| ≤ K)
    (hYbound : ∀ i, ∀ᵐ omega ∂μ, Y i omega ∈ Icc (-(R : ℝ)) R)
    (hzero : ∀ i, μ[Y i | F i] =ᵐ[μ] 0) :
    Supermartingale (weightedGaussianProcess q Y R a) F μ := by
  rw [← actual_weighted_gaussian_mixture_is_the_exact_self_normalized_process q Y R a ha]
  exact mixture_supermartingale μ (gaussianReal 0 a) F (quadraticProcess q Y R)
    (actual_predictable_quadratic_weight_process_is_a_supermartingale μ F q Y hq hY K R hqbound hYbound hzero)
    (actual_weighted_quadratic_tilt_family_is_jointly_adapted F q Y hq hY R)
    (actual_weighted_quadratic_tilt_family_is_gaussian_product_integrable μ F q Y hq hY K R a hqbound hYbound)

/-- Exact real algebra converts the actual Gaussian mixture threshold to
its determinant and self-normalized square; both denominator domains are explicit. -/
theorem actual_scalar_gaussian_mixture_threshold_is_the_self_normalized_square_bound
    (a : ℝ≥0) (variance sum delta : ℝ) (hv : 0 ≤ variance) (hd : 0 < delta) :
    mixtureValue a variance sum < 1 / delta ↔
      (a : ℝ) * sum ^ 2 / (1 + (a : ℝ) * variance) <
        Real.log (1 + (a : ℝ) * variance) + 2 * Real.log (1 / delta) := by
  have hD : 0 < 1 + (a : ℝ) * variance := by positivity
  have hs : 0 < Real.sqrt (1 + (a : ℝ) * variance) := Real.sqrt_pos.mpr hD
  unfold mixtureValue
  rw [inv_mul_lt_iff₀ hs,← Real.lt_log_iff_exp_lt (by positivity),
    Real.log_mul hs.ne' (by positivity),Real.log_sqrt hD.le]
  constructor <;> intro h <;> nlinarith

/-- One actual simultaneous event controls every accumulated weighted sum
with its actual squared-weight variance, without supplying the event as a premise. -/
theorem actual_all_time_weighted_gaussian_self_normalized_noise_confidence
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (q Y : ℕ → Ω → ℝ) (hq : ∀ i, StronglyMeasurable[F i] (q i))
    (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i)) (K R a : ℝ≥0) (ha : 0 < a)
    (hqbound : ∀ i, ∀ᵐ omega ∂μ, |q i omega| ≤ K)
    (hYbound : ∀ i, ∀ᵐ omega ∂μ, Y i omega ∈ Icc (-(R : ℝ)) R)
    (hzero : ∀ i, μ[Y i | F i] =ᵐ[μ] 0) (delta : ℝ) (hd : 0 < delta) :
    1 - delta ≤ μ.real {omega | ∀ n,
      (a : ℝ) * (partialSum (fun i => q i * Y i) n omega) ^ 2 /
          (1 + (a : ℝ) * (R : ℝ) ^ 2 * partialSum (fun i omega => q i omega ^ 2) n omega) <
        Real.log (1 + (a : ℝ) * (R : ℝ) ^ 2 * partialSum (fun i omega => q i omega ^ 2) n omega) +
          2 * Real.log (1 / delta)} := by
  have hv := mixture_simultaneous_confidence_event μ (gaussianReal 0 a) F (quadraticProcess q Y R)
    (actual_predictable_quadratic_weight_process_is_a_supermartingale μ F q Y hq hY K R hqbound hYbound hzero)
    (actual_weighted_quadratic_tilt_family_is_jointly_adapted F q Y hq hY R)
    (actual_weighted_quadratic_tilt_family_is_gaussian_product_integrable μ F q Y hq hY K R a hqbound hYbound)
    (fun _ _ _ => (Real.exp_pos _).le)
    (fun tilt omega => congrFun (actual_quadratic_weight_process_has_initial_one_and_the_exact_step q Y R tilt).1 omega)
    delta hd
  rw [actual_weighted_gaussian_mixture_is_the_exact_self_normalized_process q Y R a ha] at hv
  convert hv using 2
  ext omega
  apply forall_congr'
  intro n
  have hQ : 0 ≤ partialSum (fun i omega => q i omega ^ 2) n omega := by
    unfold partialSum
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  simpa only [weightedGaussianProcess,mul_assoc] using
    (actual_scalar_gaussian_mixture_threshold_is_the_self_normalized_square_bound a
      ((R : ℝ) ^ 2 * partialSum (fun i omega => q i omega ^ 2) n omega)
      (partialSum (fun i => q i * Y i) n omega) delta (by positivity) hd).symm

end SafeLearning.CompleteModulesLandscapeGaussianWeightedMixture
