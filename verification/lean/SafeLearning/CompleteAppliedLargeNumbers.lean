import Mathlib

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedLargeNumbers
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal Function

variable {Omega : Type*} [MeasurableSpace Omega]

def actualSampleMean (sample : ℕ → Omega → ℝ) (size : ℕ) (outcome : Omega) : ℝ :=
  (∑ index ∈ Finset.range size,sample index outcome)/(size:ℝ)

theorem actual_strong_law_for_integrable_iid_samples
    (measure : Measure Omega) [IsProbabilityMeasure measure]
    (sample : ℕ → Omega → ℝ) (hintegrable : Integrable (sample 0) measure)
    (hindependent : Pairwise ((· ⟂ᵢ[measure] ·) on sample))
    (hidentical : ∀ n,IdentDistrib (sample n) (sample 0) measure measure) :
    ∀ᵐ outcome ∂measure,Tendsto (fun n => actualSampleMean sample n outcome)
      atTop (𝓝 (∫ x,sample 0 x ∂measure)) :=
  strong_law_ae_real sample hintegrable hindependent hidentical

theorem actual_sample_means_are_measurable
    (sample : ℕ → Omega → ℝ) (hmeasurable : ∀ n,Measurable (sample n)) (size : ℕ) :
    Measurable (actualSampleMean sample size) := by
  exact (Finset.measurable_fun_sum (Finset.range size) (fun index _ => hmeasurable index)).div_const _

theorem actual_mean_of_each_nonempty_iid_sample_mean
    (measure : Measure Omega) [IsProbabilityMeasure measure]
    (sample : ℕ → Omega → ℝ) (hintegrable : Integrable (sample 0) measure)
    (hidentical : ∀ n,IdentDistrib (sample n) (sample 0) measure measure)
    (size : ℕ) (hsize : 0 < size) :
    (∫ x,actualSampleMean sample size x ∂measure) = ∫ x,sample 0 x ∂measure := by
  have hi : ∀ n,Integrable (sample n) measure :=
    fun n => (hidentical n).symm.integrable_snd hintegrable
  unfold actualSampleMean
  rw [integral_div,integral_finsetSum _ (fun index _ => hi index)]
  simp_rw [(hidentical _).integral_eq]
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hsize.ne')

theorem actual_iid_sample_mean_is_square_integrable
    (measure : Measure Omega) [IsProbabilityMeasure measure]
    (sample : ℕ → Omega → ℝ) (hsquare : MemLp (sample 0) 2 measure)
    (hidentical : ∀ n,IdentDistrib (sample n) (sample 0) measure measure) (size : ℕ) :
    MemLp (actualSampleMean sample size) 2 measure := by
  have h : MemLp (fun x => ∑ index ∈ Finset.range size,sample index x) 2 measure :=
    memLp_finsetSum _ (fun index _ => (hidentical index).symm.memLp_snd hsquare)
  convert h.const_mul ((size:ℝ)⁻¹) using 1
  funext x
  simp only [actualSampleMean,div_eq_mul_inv,mul_comm]

theorem actual_iid_sample_mean_variance
    (measure : Measure Omega) [IsProbabilityMeasure measure]
    (sample : ℕ → Omega → ℝ) (hsquare : MemLp (sample 0) 2 measure)
    (hindependent : Pairwise ((· ⟂ᵢ[measure] ·) on sample))
    (hidentical : ∀ n,IdentDistrib (sample n) (sample 0) measure measure)
    (size : ℕ) (hsize : 0 < size) :
    variance (actualSampleMean sample size) measure=variance (sample 0) measure/(size:ℝ) := by
  have hi : ∀ n,MemLp (sample n) 2 measure :=
    fun n => (hidentical n).symm.memLp_snd hsquare
  have hsum := IndepFun.variance_sum (fun index (_ : index ∈ Finset.range size) => hi index)
    (fun index _ other _ hne => hindependent hne)
  have he : actualSampleMean sample size =
      (fun x => (size:ℝ)⁻¹*(∑ index ∈ Finset.range size,sample index x)) := by
    funext x
    simp only [actualSampleMean,div_eq_mul_inv,mul_comm]
  rw [he,variance_const_mul]
  have hf : (∑ index ∈ Finset.range size,sample index) =
      (fun x => ∑ index ∈ Finset.range size,sample index x) := by
    funext x
    simp
  rw [←hf,hsum]
  simp_rw [(hidentical _).variance_eq]
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  field_simp

theorem actual_chebyshev_bound_for_iid_sample_means
    (measure : Measure Omega) [IsProbabilityMeasure measure]
    (sample : ℕ → Omega → ℝ) (hsquare : MemLp (sample 0) 2 measure)
    (hindependent : Pairwise ((· ⟂ᵢ[measure] ·) on sample))
    (hidentical : ∀ n,IdentDistrib (sample n) (sample 0) measure measure)
    (size : ℕ) (hsize : 0 < size) (radius : ℝ) (hradius : 0 < radius) :
    measure.real {outcome | radius ≤ |actualSampleMean sample size outcome-
      (∫ x,sample 0 x ∂measure)|} ≤ variance (sample 0) measure/((size:ℝ)*radius^2) := by
  have hmean := actual_mean_of_each_nonempty_iid_sample_mean measure sample
    (hsquare.integrable (by norm_num)) hidentical size hsize
  have hv := actual_iid_sample_mean_variance measure sample hsquare hindependent hidentical size hsize
  have h := meas_ge_le_variance_div_sq
    (actual_iid_sample_mean_is_square_integrable measure sample hsquare hidentical size) hradius
  rw [hmean,hv] at h
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [ENNReal.toReal_ofReal (div_nonneg (div_nonneg (variance_nonneg _ _) (Nat.cast_nonneg _))
    (sq_nonneg _))] at hr
  simpa only [measureReal_def,div_div] using hr

theorem actual_strict_chebyshev_bound_for_iid_sample_means
    (measure : Measure Omega) [IsProbabilityMeasure measure]
    (sample : ℕ → Omega → ℝ) (hsquare : MemLp (sample 0) 2 measure)
    (hindependent : Pairwise ((· ⟂ᵢ[measure] ·) on sample))
    (hidentical : ∀ n,IdentDistrib (sample n) (sample 0) measure measure)
    (size : ℕ) (hsize : 0 < size) (radius : ℝ) (hradius : 0 < radius) :
    measure.real {outcome | radius < |actualSampleMean sample size outcome-
      (∫ x,sample 0 x ∂measure)|} ≤ variance (sample 0) measure/((size:ℝ)*radius^2) := by
  have hsub : {outcome | radius < |actualSampleMean sample size outcome-
      (∫ x,sample 0 x ∂measure)|} ⊆
      {outcome | radius ≤ |actualSampleMean sample size outcome-
      (∫ x,sample 0 x ∂measure)|} := by
    intro outcome h
    change radius < |actualSampleMean sample size outcome-
      (∫ x,sample 0 x ∂measure)| at h
    change radius ≤ |actualSampleMean sample size outcome-
      (∫ x,sample 0 x ∂measure)|
    exact le_of_lt h
  exact (measureReal_mono hsub).trans
    (actual_chebyshev_bound_for_iid_sample_means measure sample hsquare
      hindependent hidentical size hsize radius hradius)

theorem actual_weak_law_follows_from_the_chebyshev_variance_bound
    (measure : Measure Omega) [IsProbabilityMeasure measure]
    (sample : ℕ → Omega → ℝ) (hsquare : MemLp (sample 0) 2 measure)
    (hindependent : Pairwise ((· ⟂ᵢ[measure] ·) on sample))
    (hidentical : ∀ n,IdentDistrib (sample n) (sample 0) measure measure)
    (radius : ℝ) (hradius : 0 < radius) :
    Tendsto (fun size => measure.real {outcome | radius <
      |actualSampleMean sample size outcome-(∫ x,sample 0 x ∂measure)|})
      atTop (𝓝 0) := by
  have hlimit : Tendsto (fun size : ℕ =>
      (variance (sample 0) measure/radius^2)*(1/(size:ℝ))) atTop (𝓝 0) := by
    simpa using tendsto_one_div_atTop_nhds_zero_nat.const_mul
      (variance (sample 0) measure/radius^2)
  refine squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) ?_ hlimit
  filter_upwards [eventually_gt_atTop (0:ℕ)] with size hsize
  have h := actual_strict_chebyshev_bound_for_iid_sample_means measure sample hsquare
    hindependent hidentical size hsize radius hradius
  convert h using 1
  ring

theorem actual_finite_variance_is_square_integrability
    (measure : Measure Omega) [IsProbabilityMeasure measure]
    (quantity : Omega → ℝ) (hintegrable : Integrable quantity measure) :
    evariance quantity measure < ∞ ↔ MemLp quantity 2 measure :=
  evariance_lt_top_iff_memLp hintegrable.aestronglyMeasurable

theorem actual_weak_law_under_the_literal_finite_variance_assumption
    (measure : Measure Omega) [IsProbabilityMeasure measure]
    (sample : ℕ → Omega → ℝ) (hintegrable : Integrable (sample 0) measure)
    (hvariance : evariance (sample 0) measure < ∞)
    (hindependent : Pairwise ((· ⟂ᵢ[measure] ·) on sample))
    (hidentical : ∀ n,IdentDistrib (sample n) (sample 0) measure measure)
    (radius : ℝ) (hradius : 0 < radius) :
    Tendsto (fun size => measure.real {outcome | radius <
      |actualSampleMean sample size outcome-(∫ x,sample 0 x ∂measure)|})
      atTop (𝓝 0) :=
  actual_weak_law_follows_from_the_chebyshev_variance_bound measure sample
    ((actual_finite_variance_is_square_integrability measure (sample 0) hintegrable).mp hvariance)
    hindependent hidentical radius hradius

end SafeLearning.CompleteAppliedLargeNumbers
