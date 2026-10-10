import SafeLearning.CompleteAppliedDensityScaling

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedUniformDefinitions
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
open SafeLearning.CompleteAppliedDensityScaling

def actualUniformDensity (left right : ℝ) : ℝ → ℝ :=
  (Icc left right).indicator (fun _ => 1/(right-left))

def actualUniformLaw (left right : ℝ) : Measure ℝ :=
  actualDensityLaw (actualUniformDensity left right)

theorem actual_uniform_density_is_measurable (left right : ℝ) :
    Measurable (actualUniformDensity left right) :=
  measurable_const.indicator measurableSet_Icc

theorem actual_uniform_density_is_nonnegative (left right : ℝ) (hlt : left < right) :
    ∀ point,0 ≤ actualUniformDensity left right point := by
  intro point
  by_cases hpoint : point ∈ Icc left right
  · simp only [actualUniformDensity,indicator_of_mem hpoint]
    exact div_nonneg (by norm_num) (sub_pos.mpr hlt).le
  · simp [actualUniformDensity,hpoint]

theorem actual_uniform_law_is_the_true_normalized_restriction
    (left right : ℝ) (hlt : left < right) :
    actualUniformLaw left right =
      (ENNReal.ofReal (right-left))⁻¹ • volume.restrict (Icc left right) := by
  have he : (fun point => ENNReal.ofReal (actualUniformDensity left right point)) =
      (Icc left right).indicator (fun _ => (ENNReal.ofReal (right-left))⁻¹) := by
    funext point
    by_cases hpoint : point ∈ Icc left right
    · simp only [actualUniformDensity,indicator_of_mem hpoint,one_div]
      exact ENNReal.ofReal_inv_of_pos (sub_pos.mpr hlt)
    · simp [actualUniformDensity,hpoint]
  rw [actualUniformLaw,actualDensityLaw,he,withDensity_indicator measurableSet_Icc,
    withDensity_const]

theorem actual_uniform_law_is_a_probability_measure
    (left right : ℝ) (hlt : left < right) :
    IsProbabilityMeasure (actualUniformLaw left right) := by
  constructor
  rw [actual_uniform_law_is_the_true_normalized_restriction left right hlt,
    Measure.smul_apply,Measure.restrict_apply MeasurableSet.univ,univ_inter,
    smul_eq_mul,Real.volume_Icc]
  exact ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hlt)))
    ENNReal.ofReal_ne_top

theorem actual_uniform_probability_is_length_ratio
    (left right : ℝ) (hlt : left < right) (event : Set ℝ)
    (hevent : MeasurableSet event) :
    actualUniformLaw left right event =
      volume (event ∩ Icc left right)/ENNReal.ofReal (right-left) := by
  rw [actual_uniform_law_is_the_true_normalized_restriction left right hlt,
    Measure.smul_apply,Measure.restrict_apply hevent,smul_eq_mul,ENNReal.div_eq_inv_mul]

theorem actual_uniform_density_integrates_to_one
    (left right : ℝ) (hlt : left < right) :
    Integrable (actualUniformDensity left right) volume ∧
      (∫ point,actualUniformDensity left right point)=1 := by
  constructor
  · exact (integrableOn_const (C := (1/(right-left):ℝ))
      (measure_Icc_lt_top.ne) enorm_ne_top).integrable_indicator measurableSet_Icc
  · rw [actualUniformDensity,integral_indicator measurableSet_Icc,integral_const,
      measureReal_restrict_apply MeasurableSet.univ,univ_inter,measureReal_def,
      Real.volume_Icc,ENNReal.toReal_ofReal (sub_pos.mpr hlt).le,smul_eq_mul]
    exact mul_one_div_cancel (sub_pos.mpr hlt).ne'

theorem actual_uniform_half_interval_density_is_two_and_can_exceed_one
    (point : ℝ) (hpoint : point ∈ Icc (0:ℝ) (1/2)) :
    actualUniformDensity 0 (1/2) point=2 ∧
      1 < actualUniformDensity 0 (1/2) point := by
  simp only [actualUniformDensity,indicator_of_mem hpoint]
  norm_num

def actualUnitSquare : Set (ℝ × ℝ) :=
  Icc (-1/2:ℝ) (1/2) ×ˢ Icc (-1/2:ℝ) (1/2)

def actualUnitSquareLaw : Measure (ℝ × ℝ) :=
  (actualUniformLaw (-1/2) (1/2)).prod (actualUniformLaw (-1/2) (1/2))

theorem actual_unit_square_law_has_density_one_on_the_square_and_zero_elsewhere :
    actualUnitSquareLaw =
      (volume.prod volume).withDensity (actualUnitSquare.indicator (fun _ => 1)) := by
  unfold actualUnitSquareLaw actualUniformLaw actualDensityLaw
  rw [prod_withDensity
    (actual_uniform_density_is_measurable _ _).ennreal_ofReal
    (actual_uniform_density_is_measurable _ _).ennreal_ofReal]
  congr 1
  funext point
  have hden : 1/((1/2:ℝ)-(-1/2))=1 := by norm_num
  simp only [actualUniformDensity,hden]
  by_cases hfirst : point.1 ∈ Icc (-1/2:ℝ) (1/2) <;>
    by_cases hsecond : point.2 ∈ Icc (-1/2:ℝ) (1/2) <;>
    simp only [actualUnitSquare,indicator_apply,mem_prod,hfirst,hsecond]
    <;> norm_num

theorem actual_unit_square_law_is_normalized_with_independent_uniform_coordinates :
    IsProbabilityMeasure actualUnitSquareLaw ∧
      IndepFun Prod.fst Prod.snd actualUnitSquareLaw ∧
      actualUnitSquareLaw.map Prod.fst=actualUniformLaw (-1/2) (1/2) ∧
      actualUnitSquareLaw.map Prod.snd=actualUniformLaw (-1/2) (1/2) := by
  let : IsProbabilityMeasure (actualUniformLaw (-1/2) (1/2)) :=
    actual_uniform_law_is_a_probability_measure _ _ (by norm_num)
  constructor
  · unfold actualUnitSquareLaw
    infer_instance
  constructor
  · exact indepFun_prod (μ := actualUniformLaw (-1/2) (1/2))
      (ν := actualUniformLaw (-1/2) (1/2)) measurable_id measurable_id
  constructor
  · exact measurePreserving_fst.map_eq
  · exact measurePreserving_snd.map_eq

end SafeLearning.CompleteAppliedUniformDefinitions
