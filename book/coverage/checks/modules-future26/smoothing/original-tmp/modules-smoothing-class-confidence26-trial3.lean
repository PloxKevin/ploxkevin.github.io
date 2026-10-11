import SafeLearning.CompleteAppliedGaussianQuantile

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace SafeLearning.CompleteModulesSmoothingNeymanPearson26

variable {E : Type*} [MeasurableSpace E]

theorem actual_density_test_transfer_from_low_likelihood_region
    (base : Measure E) (p q h : E → ℝ) (S : Set E) (hS : MeasurableSet S)
    (hp : Integrable p base) (hq : Integrable q base)
    (hhp : Integrable (fun z => h z * p z) base)
    (hhq : Integrable (fun z => h z * q z) base)
    (hh : ∀ z, 0 ≤ h z ∧ h z ≤ 1)
    (cutoff : ℝ) (ht : 0 ≤ cutoff)
    (hinside : ∀ z ∈ S, q z ≤ cutoff * p z)
    (houtside : ∀ z ∉ S, cutoff * p z ≤ q z)
    (hmass : (∫ z in S, p z ∂base) ≤ ∫ z, h z * p z ∂base) :
    (∫ z in S, q z ∂base) ≤ ∫ z, h z * q z ∂base := by
  have hpoint (z : E) :
      cutoff * (h z * p z - S.indicator p z) ≤ h z * q z - S.indicator q z := by
    by_cases hz : z ∈ S
    · simp only [Set.indicator_of_mem hz]
      have hn : 0 ≤ (1-h z) * (cutoff*p z-q z) :=
        mul_nonneg (sub_nonneg.mpr (hh z).2) (sub_nonneg.mpr (hinside z hz))
      nlinarith
    · simp only [Set.indicator_of_notMem hz, sub_zero]
      have hn := mul_nonneg ((hh z).1) (sub_nonneg.mpr (houtside z hz))
      nlinarith
  have hi := integral_mono ((hhp.sub (hp.indicator hS)).const_mul cutoff)
    (hhq.sub (hq.indicator hS)) hpoint
  simp only [Pi.sub_apply] at hi
  rw [integral_const_mul,integral_sub hhp (hp.indicator hS),
    integral_sub hhq (hq.indicator hS),integral_indicator hS,integral_indicator hS] at hi
  nlinarith [mul_nonneg ht (sub_nonneg.mpr hmass)]

theorem actual_density_test_transfer_from_high_likelihood_region
    (base : Measure E) (p q h : E → ℝ) (S : Set E) (hS : MeasurableSet S)
    (hp : Integrable p base) (hq : Integrable q base)
    (hhp : Integrable (fun z => h z * p z) base)
    (hhq : Integrable (fun z => h z * q z) base)
    (hh : ∀ z, 0 ≤ h z ∧ h z ≤ 1)
    (cutoff : ℝ) (ht : 0 ≤ cutoff)
    (hinside : ∀ z ∈ S, cutoff * p z ≤ q z)
    (houtside : ∀ z ∉ S, q z ≤ cutoff * p z)
    (hmass : (∫ z, h z * p z ∂base) ≤ ∫ z in S, p z ∂base) :
    (∫ z, h z * q z ∂base) ≤ ∫ z in S, q z ∂base := by
  have hpoint (z : E) :
      h z * q z - S.indicator q z ≤ cutoff * (h z * p z - S.indicator p z) := by
    by_cases hz : z ∈ S
    · simp only [Set.indicator_of_mem hz]
      have hn : 0 ≤ (1-h z) * (q z-cutoff*p z) :=
        mul_nonneg (sub_nonneg.mpr (hh z).2) (sub_nonneg.mpr (hinside z hz))
      nlinarith
    · simp only [Set.indicator_of_notMem hz, sub_zero]
      have hn := mul_nonneg ((hh z).1) (sub_nonneg.mpr (houtside z hz))
      nlinarith
  have hi := integral_mono (hhq.sub (hq.indicator hS))
    ((hhp.sub (hp.indicator hS)).const_mul cutoff) hpoint
  simp only [Pi.sub_apply] at hi
  rw [integral_const_mul,integral_sub hhp (hp.indicator hS),
    integral_sub hhq (hq.indicator hS),integral_indicator hS,integral_indicator hS] at hi
  nlinarith [mul_nonneg ht (sub_nonneg.mpr hmass)]

theorem actual_bounded_measurable_test_has_integrable_density_products
    (base : Measure E) (p h : E → ℝ) (hp : Integrable p base)
    (hm : Measurable h) (hh : ∀ z, 0 ≤ h z ∧ h z ≤ 1) :
    Integrable (fun z => h z * p z) base := by
  apply hp.bdd_mul hm.aestronglyMeasurable
  exact ae_of_all base (fun z => by
    rw [Real.norm_eq_abs,abs_of_nonneg (hh z).1]
    exact (hh z).2)


open CompleteAppliedGaussianCDF CompleteAppliedGaussianQuantile

theorem actual_scalar_shifted_gaussian_density_ratio (shift point : ℝ) :
    gaussianPDFReal shift 1 point = gaussianPDFReal 0 1 point *
      Real.exp (shift*point-shift^2/2) := by
  simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem actual_scalar_gaussian_low_halfspace_is_a_likelihood_region
    (shift threshold : ℝ) (hshift : 0 ≤ shift) :
    (∀ point ≤ threshold, gaussianPDFReal shift 1 point ≤
      Real.exp (shift*threshold-shift^2/2) * gaussianPDFReal 0 1 point) ∧
    (∀ point ≥ threshold, Real.exp (shift*threshold-shift^2/2) *
      gaussianPDFReal 0 1 point ≤ gaussianPDFReal shift 1 point) := by
  constructor <;> intro point hp
  · rw [actual_scalar_shifted_gaussian_density_ratio shift point]
    rw [mul_comm (Real.exp _)]
    apply mul_le_mul_of_nonneg_left _ (gaussianPDFReal_nonneg _ _ _)
    exact Real.exp_le_exp.mpr (by nlinarith)
  · rw [actual_scalar_shifted_gaussian_density_ratio shift point]
    rw [mul_comm (Real.exp _)]
    apply mul_le_mul_of_nonneg_left _ (gaussianPDFReal_nonneg _ _ _)
    exact Real.exp_le_exp.mpr (by nlinarith)

theorem actual_shifted_scalar_gaussian_halfspace_mass (shift threshold : ℝ) :
    (gaussianReal shift 1).real (Iic threshold) = standardCDF (threshold-shift) := by
  have hmap : (gaussianReal 0 1).map (fun x : ℝ => x+shift) = gaussianReal shift 1 := by
    simpa using (gaussianReal_map_add_const (μ:=0) (v:=1) shift)
  have hh := map_measureReal_apply (μ:=gaussianReal 0 1)
    (show Measurable (fun x : ℝ => x+shift) by fun_prop) (s:=Iic threshold) measurableSet_Iic
  rw [hmap] at hh
  have hs : (fun x : ℝ => x+shift) ⁻¹' Iic threshold = Iic (threshold-shift) := by
    ext x
    simp only [mem_preimage,mem_Iic]
    constructor <;> intro hx <;> linarith
  simpa only [hs,standardCDF] using hh

theorem actual_scalar_gaussian_transfer_for_every_bounded_measurable_test
    (h : ℝ → ℝ) (hm : Measurable h) (hb : ∀ z, 0 ≤ h z ∧ h z ≤ 1)
    (shift threshold : ℝ) (hshift : 0 ≤ shift)
    (hbase : standardCDF threshold ≤ ∫ z, h z ∂gaussianReal 0 1) :
    standardCDF (threshold-shift) ≤ ∫ z, h z ∂gaussianReal shift 1 := by
  have hp := integrable_gaussianPDFReal 0 1
  have hq := integrable_gaussianPDFReal shift 1
  have hhp := actual_bounded_measurable_test_has_integrable_density_products volume _ h hp hm hb
  have hhq := actual_bounded_measurable_test_has_integrable_density_products volume _ h hq hm hb
  have hi := actual_scalar_gaussian_low_halfspace_is_a_likelihood_region shift threshold hshift
  have hx (mean : ℝ) : (gaussianReal mean 1).real (Iic threshold) =
      ∫ z in Iic threshold, gaussianPDFReal mean 1 z := by
    rw [measureReal_def,gaussianReal_apply_eq_integral _ (by norm_num),ENNReal.toReal_ofReal]
    exact integral_nonneg (fun z => gaussianPDFReal_nonneg _ _ _)
  have hf (mean : ℝ) : (∫ z, h z ∂gaussianReal mean 1) =
      ∫ z, h z * gaussianPDFReal mean 1 z := by
    rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1:ℝ≥0)≠0)]
    simp only [smul_eq_mul,mul_comm]
  have hbase' : (∫ z in Iic threshold, gaussianPDFReal 0 1 z) ≤
      ∫ z, h z * gaussianPDFReal 0 1 z := by
    rw [←hx 0,←hf 0]
    exact hbase
  have ht := actual_density_test_transfer_from_low_likelihood_region volume
    (gaussianPDFReal 0 1) (gaussianPDFReal shift 1) h (Iic threshold)
    measurableSet_Iic hp hq hhp hhq hb (Real.exp (shift*threshold-shift^2/2))
    (Real.exp_pos _).le (fun z hz => hi.1 z hz)
    (fun z hz => hi.2 z (le_of_lt (lt_of_not_ge hz))) hbase'
  rw [←hx shift,actual_shifted_scalar_gaussian_halfspace_mass,←hf shift] at ht
  exact ht

theorem actual_scalar_ideal_majority_for_every_strict_standardized_shift
    (h : ℝ → ℝ) (hm : Measurable h) (hb : ∀ z, 0 ≤ h z ∧ h z ≤ 1)
    (shift : ℝ) (hshift : 0 ≤ shift) (hradius : shift < 2)
    (hbase : standardCDF 2 ≤ ∫ z, h z ∂gaussianReal 0 1) :
    (1/2:ℝ) < ∫ z, h z ∂gaussianReal shift 1 := by
  have htransfer := actual_scalar_gaussian_transfer_for_every_bounded_measurable_test
    h hm hb shift 2 hshift hbase
  have hhalf : (1/2:ℝ) < standardCDF (2-shift) := by
    rw [←actual_standard_gaussian_symmetry_and_half_mass]
    apply actual_standard_gaussian_cdf_is_continuous_and_strictly_increasing.2
    linarith
  exact hhalf.trans_le htransfer


variable {Y : Type*} [MeasurableSpace Y] [MeasurableSingletonClass Y]

def scalarClassMass (classifier : ℝ → Y) (shift : ℝ) (label : Y) : ℝ :=
  (gaussianReal shift 1).real (classifier ⁻¹' {label})

def scalarIdealWinner (classifier : ℝ → Y) (shift : ℝ) (label : Y) : Prop :=
  ∀ other, other ≠ label → scalarClassMass classifier shift other < scalarClassMass classifier shift label

theorem actual_scalar_ideal_classifier_retains_every_true_majority_label
    (classifier : ℝ → Y) (hf : Measurable classifier) (label : Y)
    (shift : ℝ) (hshift : 0 ≤ shift) (hradius : shift < 2)
    (hbase : standardCDF 2 ≤ scalarClassMass classifier 0 label) :
    scalarIdealWinner classifier shift label := by
  let A := classifier ⁻¹' {label}
  have hA : MeasurableSet A := hf (measurableSet_singleton label)
  let h : ℝ → ℝ := A.indicator (fun _ => 1)
  have hm : Measurable h := measurable_const.indicator hA
  have hb : ∀ z, 0 ≤ h z ∧ h z ≤ 1 := by
    intro z
    by_cases hz : z ∈ A <;> simp [h,hz]
  have hh (mean : ℝ) : (∫ z, h z ∂gaussianReal mean 1) = scalarClassMass classifier mean label := by
    simpa only [h,scalarClassMass,A,smul_eq_mul,mul_one] using
      (integral_indicator_const (μ:=gaussianReal mean 1) (1:ℝ) hA)
  have hmj : (1/2:ℝ) < scalarClassMass classifier shift label := by
    rw [←hh shift]
    exact actual_scalar_ideal_majority_for_every_strict_standardized_shift h hm hb shift hshift hradius
      (by rw [hh 0]; exact hbase)
  intro other hother
  let B := classifier ⁻¹' {other}
  have hB : MeasurableSet B := hf (measurableSet_singleton other)
  have hd : Disjoint A B := by
    rw [Set.disjoint_left]
    intro z ha hb
    exact hother (hb.symm.trans ha)
  have hu := measureReal_mono (μ:=gaussianReal shift 1)
    (s₁:=A∪B) (s₂:=univ) (subset_univ _)
  rw [measureReal_union hd hB] at hu
  have hone : (gaussianReal shift 1).real univ = 1 := by simp
  rw [hone] at hu
  change scalarClassMass classifier shift label + scalarClassMass classifier shift other ≤ 1 at hu
  linarith

theorem actual_scalar_confidence_is_over_estimation_samples
    {Omega : Type*} [MeasurableSpace Omega]
    (samples : Measure Omega) [IsProbabilityMeasure samples]
    (classifier : ℝ → Y) (hf : Measurable classifier) (selectedLabel : Omega → Y)
    (confidenceEvent : Set Omega) (hconfidence : (999/1000:ℝ) ≤ samples.real confidenceEvent)
    (hvalid : ∀ omega ∈ confidenceEvent,
      standardCDF 2 ≤ scalarClassMass classifier 0 (selectedLabel omega)) :
    (999/1000:ℝ) ≤ samples.real {omega | ∀ shift : ℝ,
      0 ≤ shift → shift < 2 → scalarIdealWinner classifier shift (selectedLabel omega)} := by
  apply hconfidence.trans
  apply measureReal_mono (h₂:=by finiteness)
  intro omega homega shift hnonnegative hstrict
  exact actual_scalar_ideal_classifier_retains_every_true_majority_label classifier hf
    (selectedLabel omega) shift hnonnegative hstrict (hvalid omega homega)

theorem actual_scalar_boundary_halfspace_has_no_strict_majority :
    (gaussianReal 2 1).real (Iic 2) = 1/2 ∧
    (gaussianReal 2 1).real (Iic 2)ᶜ = 1/2 ∧
    ¬ ((gaussianReal 2 1).real (Iic 2)ᶜ < (gaussianReal 2 1).real (Iic 2)) := by
  have hh : (gaussianReal 2 1).real (Iic 2) = 1/2 := by
    rw [actual_shifted_scalar_gaussian_halfspace_mass]
    norm_num only [sub_self]
    exact actual_standard_gaussian_symmetry_and_half_mass
  have hc := measureReal_add_measureReal_compl (μ:=gaussianReal 2 1)
    (s:=Iic 2) measurableSet_Iic
  rw [hh] at hc
  have hone : (gaussianReal 2 1).real univ = 1 := by simp
  rw [hone] at hc
  refine ⟨hh, by linarith, ?_⟩
  rw [hh]
  linarith

end SafeLearning.CompleteModulesSmoothingNeymanPearson26


