import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal
namespace SafeLearning.CompleteAppliedJointDensityBayesGeneral25
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable (μ : Measure X) [SFinite μ] (ν : Measure Y) [SFinite ν]
variable (p : X × Y → ℝ≥0∞) (hp : Measurable p)
include hp

def marginalDensity (y : Y) : ℝ≥0∞ := ∫⁻ x, p (x,y) ∂μ

theorem marginalDensity_measurable : Measurable (marginalDensity μ p) :=
  hp.lintegral_prod_left'

def regularEvidence : Set Y := {y | marginalDensity μ p y ≠ 0 ∧ marginalDensity μ p y ≠ ∞}

theorem regularEvidence_measurable : MeasurableSet (regularEvidence μ p) := by
  exact (measurableSet_eq_fun (marginalDensity_measurable μ p hp) measurable_const).compl.inter
    (measurableSet_eq_fun (marginalDensity_measurable μ p hp) measurable_const).compl

def safeNormalizer (y : Y) : ℝ≥0∞ := by
  classical
  exact if y ∈ regularEvidence μ p then marginalDensity μ p y else 1

theorem safeNormalizer_measurable : Measurable (safeNormalizer μ p) := by
  exact (marginalDensity_measurable μ p hp).piecewise
    (regularEvidence_measurable μ p hp) measurable_const

theorem safeNormalizer_ne_zero (y : Y) : safeNormalizer μ p y ≠ 0 := by
  classical
  by_cases hy : y ∈ regularEvidence μ p
  · simpa [safeNormalizer,hy] using hy.1
  · simp [safeNormalizer,hy]

def normalizedDensity (y : Y) (x : X) : ℝ≥0∞ := by
  classical
  exact if y ∈ regularEvidence μ p then p (x,y) / safeNormalizer μ p y else 0

theorem normalizedDensity_measurable : Measurable (Function.uncurry (normalizedDensity μ p)) := by
  classical
  change Measurable (fun yx : Y × X => if yx.1 ∈ regularEvidence μ p
    then p (yx.2,yx.1) / safeNormalizer μ p yx.1 else 0)
  exact ((hp.comp measurable_swap).div
    ((safeNormalizer_measurable μ p hp).comp measurable_fst)).piecewise
      ((regularEvidence_measurable μ p hp).preimage measurable_fst) measurable_const

def posteriorKernel (x0 : X) : Kernel Y X := by
  classical
  exact Kernel.piecewise (regularEvidence_measurable μ p hp)
    ((Kernel.const Y μ).withDensity (normalizedDensity μ p))
    (Kernel.const Y (Measure.dirac x0))

theorem actual_positive_finite_evidence_posterior_has_the_ratio_density
    (x0 : X) (y : Y) (hy : y ∈ regularEvidence μ p) :
    posteriorKernel μ p hp x0 y = μ.withDensity (fun x => p (x,y) / marginalDensity μ p y) := by
  classical
  simp only [posteriorKernel,Kernel.piecewise_apply,ite_eq_left hy]
  rw [Kernel.withDensity_apply _ (normalizedDensity_measurable μ p hp),Kernel.const_apply]
  congr 1
  funext x
  simp [normalizedDensity,safeNormalizer,hy]

instance posteriorKernel_markov (x0 : X) : IsMarkovKernel (posteriorKernel μ p hp x0) := by
  classical
  refine ⟨fun y => ⟨?_⟩⟩
  by_cases hy : y ∈ regularEvidence μ p
  · rw [actual_positive_finite_evidence_posterior_has_the_ratio_density μ p hp x0 y hy,
      withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
    simp_rw [div_eq_mul_inv]
    have hsection : Measurable (fun x => p (x,y)) := hp.comp (measurable_id.prodMk measurable_const)
    rw [lintegral_mul_const _ hsection]
    exact ENNReal.mul_inv_cancel hy.1 hy.2
  · simp [posteriorKernel,Kernel.piecewise_apply,hy]

theorem actual_joint_density_y_marginal_is_its_integrated_density :
    ((μ.prod ν).withDensity p).map Prod.snd = ν.withDensity (marginalDensity μ p) := by
  apply Measure.ext_of_lintegral
  intro test htest
  rw [lintegral_map htest measurable_snd]
  change (∫⁻ xy, (test ∘ Prod.snd) xy ∂(μ.prod ν).withDensity p) = _
  rw [lintegral_withDensity_eq_lintegral_mul _ hp (htest.comp measurable_snd),
    lintegral_withDensity_eq_lintegral_mul _ (marginalDensity_measurable μ p hp) htest]
  rw [lintegral_prod_symm _ ((hp.mul (htest.comp measurable_snd)).aemeasurable)]
  apply lintegral_congr
  intro y
  change (∫⁻ x, p (x,y) * test y ∂μ) = marginalDensity μ p y * test y
  exact lintegral_mul_const _ (show Measurable (fun x => p (x,y)) from hp.comp (measurable_id.prodMk measurable_const))

theorem actual_probability_joint_has_normalized_marginal
    (hnorm : ∫⁻ xy, p xy ∂μ.prod ν = 1) :
    ∫⁻ y, marginalDensity μ p y ∂ν = 1 := by
  change (∫⁻ y, ∫⁻ x, p (x,y) ∂μ ∂ν) = 1
  rw [← lintegral_prod_symm _ hp.aemeasurable]
  exact hnorm

theorem actual_probability_joint_has_almost_everywhere_regular_evidence
    (hnorm : ∫⁻ xy, p xy ∂μ.prod ν = 1) :
    ∀ᵐ y ∂ν.withDensity (marginalDensity μ p), y ∈ regularEvidence μ p := by
  have hfinite : ∀ᵐ y ∂ν, marginalDensity μ p y ≠ ∞ := by
    have := ae_lt_top (marginalDensity_measurable μ p hp)
      (show (∫⁻ y, marginalDensity μ p y ∂ν) ≠ ∞ by
        rw [actual_probability_joint_has_normalized_marginal μ ν p hp hnorm]; simp)
    filter_upwards [this] with y hy
    exact hy.ne
  rw [ae_withDensity_iff (marginalDensity_measurable μ p hp)]
  filter_upwards [hfinite] with y hy hpos
  exact ⟨hpos,hy⟩

theorem actual_probability_joint_reversed_is_its_marginal_and_ratio_posterior
    (x0 : X)
    (hnorm : ∫⁻ xy, p xy ∂μ.prod ν = 1) :
    ((μ.prod ν).withDensity p).map Prod.swap =
      ν.withDensity (marginalDensity μ p) ⊗ₘ posteriorKernel μ p hp x0 := by
  let densityKernel := (Kernel.const Y μ).withDensity (normalizedDensity μ p)
  haveI hdensityFinite : IsFiniteKernel densityKernel := by
    refine ⟨1,by simp,fun y => ?_⟩
    rw [show densityKernel y = μ.withDensity (normalizedDensity μ p y) by
      exact Kernel.withDensity_apply _ (normalizedDensity_measurable μ p hp) y,
      withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
    by_cases hy : y ∈ regularEvidence μ p
    · simp only [normalizedDensity,hy,ite_true,safeNormalizer]
      simp only [hy,ite_true,div_eq_mul_inv]
      rw [lintegral_mul_const _ (hp.comp (measurable_id.prodMk measurable_const))]
      exact le_of_eq (ENNReal.mul_inv_cancel hy.1 hy.2)
    · simp [normalizedDensity,hy]
  have heq : posteriorKernel μ p hp x0 =ᵐ[ν.withDensity (marginalDensity μ p)] densityKernel := by
    filter_upwards [actual_probability_joint_has_almost_everywhere_regular_evidence μ ν p hp hnorm]
      with y hy
    simp [posteriorKernel,Kernel.piecewise_apply,hy,densityKernel]
  rw [Measure.compProd_congr heq]
  rw [Measure.withDensity_compProd_withDensity (marginalDensity_measurable μ p hp)
    (normalizedDensity_measurable μ p hp),Measure.compProd_const]
  have hswap : ((μ.prod ν).withDensity p).map Prod.swap =
      (ν.prod μ).withDensity (fun yx => p (yx.2,yx.1)) := by
    apply Measure.ext_of_lintegral
    intro test htest
    rw [lintegral_map htest measurable_swap]
    change (∫⁻ xy, (test ∘ Prod.swap) xy ∂(μ.prod ν).withDensity p) = _
    rw [lintegral_withDensity_eq_lintegral_mul _ hp (htest.comp measurable_swap)]
    change _ = (∫⁻ yx, test yx ∂(ν.prod μ).withDensity (p ∘ Prod.swap))
    rw [lintegral_withDensity_eq_lintegral_mul _ (hp.comp measurable_swap) htest]
    have ht : Measurable (fun yx : Y × X => p yx.swap * test yx) :=
      (hp.comp measurable_swap).mul htest
    have h := lintegral_map ht measurable_swap (μ := μ.prod ν)
    rw [Measure.prod_swap] at h
    simpa only [Prod.swap_swap,Function.comp_def,Pi.mul_apply] using h.symm
  rw [hswap]
  apply withDensity_congr_ae
  have hfiniteMarginal : ∀ᵐ y ∂ν, marginalDensity μ p y ≠ ∞ := by
    have h := ae_lt_top (marginalDensity_measurable μ p hp)
      (show (∫⁻ y, marginalDensity μ p y ∂ν) ≠ ∞ by
        rw [actual_probability_joint_has_normalized_marginal μ ν p hp hnorm]; simp)
    filter_upwards [h] with y hy
    exact hy.ne
  change ∀ᵐ yx ∂ν.prod μ, p (yx.2,yx.1) = marginalDensity μ p yx.1 * normalizedDensity μ p yx.1 yx.2
  apply (Measure.ae_prod_iff_ae_ae (μ := ν) (ν := μ)
    (measurableSet_eq_fun (hp.comp measurable_swap)
      (((marginalDensity_measurable μ p hp).comp measurable_fst).mul
        (normalizedDensity_measurable μ p hp)))).mpr
  filter_upwards [hfiniteMarginal] with y hy
  by_cases hzero : marginalDensity μ p y = 0
  · have hz : ∀ᵐ x ∂μ, p (x,y) = 0 :=
      (lintegral_eq_zero_iff (hp.comp (measurable_id.prodMk measurable_const))).mp hzero
    filter_upwards [hz] with x hx
    simp [hzero,hx]
  · filter_upwards with x
    have hreg : y ∈ regularEvidence μ p := ⟨hzero,hy⟩
    change p (x,y) = marginalDensity μ p y * normalizedDensity μ p y x
    simp only [normalizedDensity,hreg,ite_true]
    rw [show safeNormalizer μ p y = marginalDensity μ p y by simp [safeNormalizer,hreg]]
    exact (ENNReal.mul_div_cancel hzero hy).symm

end SafeLearning.CompleteAppliedJointDensityBayesGeneral25
