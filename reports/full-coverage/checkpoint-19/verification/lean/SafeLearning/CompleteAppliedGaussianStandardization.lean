import SafeLearning.CompleteAppliedGaussianCDF

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace SafeLearning.CompleteAppliedGaussianStandardization
open CompleteAppliedGaussianCDF

theorem actual_standard_gaussian_cdf_reflection (a : ℝ) :
    standardCDF (-a)=1-standardCDF a := by
  let μ := gaussianReal 0 1
  haveI : NullSingletonClass μ := nullSingletonClass_gaussianReal (by norm_num)
  have hm : μ.map (fun x : ℝ=>-x)=μ := by
    simpa [μ] using (gaussianReal_map_neg (μ:=0) (v:=1))
  have hp : (fun x : ℝ=>-x) ⁻¹' Iic (-a)=Ici a := by
    ext x;simp
  have hsym := map_measureReal_apply (μ:=μ)
    (by fun_prop : Measurable (fun x : ℝ=>-x)) (s:=Iic (-a)) measurableSet_Iic
  rw [hm,hp] at hsym
  have hatom : μ.real (Ioi a)=μ.real (Ici a) :=
    measureReal_congr Ioi_ae_eq_Ici
  have hc := measureReal_compl (μ:=μ) (s:=Iic a) measurableSet_Iic
  simp only [compl_Iic] at hc
  have hu : μ.real univ=1 := by simp [μ]
  rw [hu] at hc
  change μ.real (Iic (-a))=1-μ.real (Iic a)
  linarith

theorem actual_standard_gaussian_unit_interval_probability :
    (gaussianReal 0 1).real (Icc (-1:ℝ) 1)=2*standardCDF 1-1 := by
  haveI : NullSingletonClass (gaussianReal (0:ℝ) (1:ℝ≥0)) :=
    nullSingletonClass_gaussianReal (by norm_num)
  have hset : Iic (1:ℝ)\Iio (-1)=Icc (-1) 1 := by
    ext x;simp
  have hdiff := measureReal_sdiff (μ:=gaussianReal 0 1)
    (s₁:=Iic (1:ℝ)) (s₂:=Iio (-1)) (by intro x hx;change x< -1 at hx;exact hx.le.trans (by norm_num))
    measurableSet_Iio
  rw [hset,measureReal_congr (Iio_ae_eq_Iic (μ:=gaussianReal 0 1))] at hdiff
  change (gaussianReal 0 1).real (Icc (-1) 1)=standardCDF 1-standardCDF (-1) at hdiff
  rw [actual_standard_gaussian_cdf_reflection] at hdiff
  linarith

theorem actual_source_gaussian_standardization_has_the_true_standard_law
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω→ℝ}
    (hX : HasLaw X (gaussianReal 10 4) P) :
    HasLaw (fun ω=>(X ω-10)/2) (gaussianReal 0 1) P := by
  have h := gaussianReal_div_const (gaussianReal_sub_const hX 10) 2
  have hv : (4:NNReal)/(NNReal.mk ((2:ℝ)^2) (sq_nonneg 2))=1 := by
    ext;norm_num
  rw [hv] at h
  norm_num at h
  exact h

theorem actual_source_gaussian_event_probabilities
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω→ℝ}
    (hX : HasLaw X (gaussianReal 10 4) P) :
    P.real {ω | X ω≤12}=standardCDF 1 ∧
    P.real {ω | 8≤X ω ∧ X ω≤12}=2*standardCDF 1-1 := by
  have hz := actual_source_gaussian_standardization_has_the_true_standard_law hX
  have hp := hz.measureReal_eq (p:=fun z : ℝ=>z≤1) measurableSet_Iic
  have hi := hz.measureReal_eq (p:=fun z : ℝ=>-1≤z ∧ z≤1) measurableSet_Icc
  have he : {ω | (X ω-10)/2≤1}={ω | X ω≤12} := by
    ext ω;simp only [mem_setOf_eq];constructor <;> intro h <;> linarith
  have hei : {ω | -1≤(X ω-10)/2 ∧ (X ω-10)/2≤1}=
      {ω | 8≤X ω ∧ X ω≤12} := by
    ext ω;simp only [mem_setOf_eq];constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  rw [he] at hp
  rw [hei] at hi
  exact ⟨hp,hi.trans actual_standard_gaussian_unit_interval_probability⟩

theorem actual_source_gaussian_rounding_and_non_ninety_five_percent_coverage
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω→ℝ}
    (hX : HasLaw X (gaussianReal 10 4) P) :
    |P.real {ω | X ω≤12}-(8413/10000:ℝ)|<1/20000 ∧
    |P.real {ω | 8≤X ω ∧ X ω≤12}-(6826/10000:ℝ)|<1/10000 ∧
    P.real {ω | 8≤X ω ∧ X ω≤12}<(95/100:ℝ) ∧
    (2*(8413/10000:ℝ)-1)=6826/10000 ∧ Real.sqrt (4:ℝ)=2 := by
  have he := actual_source_gaussian_event_probabilities hX
  rw [he.1,he.2]
  have hp := actual_standard_gaussian_cdf_one_certified_probability
  constructor
  · rw [abs_lt];constructor <;> linarith
  constructor
  · rw [abs_lt];constructor <;> linarith
  constructor
  · linarith
  norm_num

end SafeLearning.CompleteAppliedGaussianStandardization
