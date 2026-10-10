import Mathlib

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedNaturalStep
open Matrix Set
open scoped BigOperators

def actualFisher : Matrix (Fin 2) (Fin 2) ℝ := !![4,0;0,1]
def actualGradient : Fin 2 → ℝ := ![2,1]
def actualNaturalDirection : Fin 2 → ℝ := ![1/2,1]
def actualScale : ℝ := Real.sqrt (1/20)
def actualStep : Fin 2 → ℝ := actualScale • actualNaturalDirection
def actualQuadraticKL (delta : Fin 2 → ℝ) : ℝ :=
  (1/2)*(delta ⬝ᵥ (actualFisher *ᵥ delta))
def actualPredictedImprovement (delta : Fin 2 → ℝ) : ℝ := actualGradient ⬝ᵥ delta

theorem actual_source_fisher_is_positive_definite : actualFisher.PosDef := by
  have he : actualFisher = Matrix.diagonal (![4,1] : Fin 2 → ℝ) := by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [actualFisher,Matrix.diagonal_apply]
  rw [he,Matrix.posDef_diagonal_iff]
  intro i; fin_cases i <;> norm_num

theorem actual_inverse_fisher_natural_direction :
    actualFisher⁻¹ *ᵥ actualGradient=actualNaturalDirection ∧
      actualGradient ⬝ᵥ actualNaturalDirection=2 := by
  have he : actualFisher *ᵥ actualNaturalDirection=actualGradient := by
    ext i; fin_cases i <;>
      norm_num [actualFisher,actualNaturalDirection,actualGradient,Matrix.mulVec,
        dotProduct,Fin.sum_univ_succ]
  constructor
  · let := actual_source_fisher_is_positive_definite.isUnit.invertible
    rw [← he,Matrix.mulVec_mulVec,Matrix.inv_mul_of_invertible,Matrix.one_mulVec]
  · norm_num [actualGradient,actualNaturalDirection,dotProduct,Fin.sum_univ_succ]

/-- The underlying bound is genuine metric Cauchy--Schwarz for arbitrary dimensions. -/
theorem actual_general_positive_fisher_objective_bound
    {I : Type*} [Fintype I] [DecidableEq I]
    (fisher : Matrix I I ℝ) (hf : fisher.PosDef) (gradient delta : I → ℝ)
    (budget : ℝ) (hbudget : delta ⬝ᵥ (fisher *ᵥ delta) ≤ budget) :
    (gradient ⬝ᵥ delta)^2 ≤ (gradient ⬝ᵥ (fisher⁻¹ *ᵥ gradient))*budget := by
  let := hf.isUnit.invertible
  have he : fisher *ᵥ (fisher⁻¹ *ᵥ gradient)=gradient := by
    rw [Matrix.mulVec_mulVec,Matrix.mul_inv_of_invertible,Matrix.one_mulVec]
  have hcs := hf.star_dotProduct_mulVec_mul_le (fisher⁻¹ *ᵥ gradient) delta
  have hpair := hf.isHermitian.star_dotProduct_mulVec_comm (fisher⁻¹ *ᵥ gradient) delta
  simp only [star_trivial,he] at hpair
  simp only [star_trivial,he,hpair] at hcs
  have hnonneg : 0 ≤ gradient ⬝ᵥ (fisher⁻¹ *ᵥ gradient) := by
    simpa only [star_trivial] using hf.inv.posSemidef.dotProduct_mulVec_nonneg gradient
  have hbound := mul_le_mul_of_nonneg_left hbudget hnonneg
  rw [dotProduct_comm (fisher⁻¹ *ᵥ gradient) gradient] at hcs
  simpa only [pow_two,dotProduct_comm delta gradient] using hcs.trans hbound

theorem actual_source_quadratic_and_linear_forms (delta : Fin 2 → ℝ) :
    actualQuadraticKL delta=2*(delta 0)^2+(1/2)*(delta 1)^2 ∧
      actualPredictedImprovement delta=2*delta 0+delta 1 := by
  constructor <;>
    norm_num [actualQuadraticKL,actualPredictedImprovement,actualFisher,actualGradient,
      Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  all_goals ring

theorem actual_source_step_coordinates_active_constraint_and_improvement :
    actualStep 0=actualScale/2 ∧ actualStep 1=actualScale ∧
      actualQuadraticKL actualStep=1/20 ∧ actualPredictedImprovement actualStep=2*actualScale := by
  have hs : actualScale^2=(1/20:ℝ) := Real.sq_sqrt (by norm_num)
  have he0 : actualStep 0=actualScale/2 := by
    simp [actualStep,actualNaturalDirection,smul_eq_mul];ring
  have he1 : actualStep 1=actualScale := by simp [actualStep,actualNaturalDirection]
  refine ⟨he0,he1,?_,?_⟩
  · rw [(actual_source_quadratic_and_linear_forms actualStep).1,he0,he1]
    nlinarith
  · rw [(actual_source_quadratic_and_linear_forms actualStep).2,he0,he1]
    ring

theorem actual_source_step_is_the_unique_global_quadratic_trust_region_optimizer
    (delta : Fin 2 → ℝ) (hfeas : actualQuadraticKL delta ≤ 1/20) :
    actualPredictedImprovement delta ≤ actualPredictedImprovement actualStep ∧
      (actualPredictedImprovement delta=actualPredictedImprovement actualStep ↔ delta=actualStep) := by
  have hs : actualScale^2=(1/20:ℝ) := Real.sq_sqrt (by norm_num)
  have hp : 0 < actualScale := Real.sqrt_pos.mpr (by norm_num)
  rw [(actual_source_quadratic_and_linear_forms delta).1] at hfeas
  have hj := (actual_source_step_coordinates_active_constraint_and_improvement).2.2.2
  have hform := (actual_source_quadratic_and_linear_forms delta).2
  have hcs : (2*delta 0+delta 1)^2 ≤ 2*(4*(delta 0)^2+(delta 1)^2) := by
    nlinarith [sq_nonneg (2*delta 0-delta 1)]
  have hupper : 2*delta 0+delta 1 ≤ 2*actualScale := by nlinarith
  refine ⟨by rw [hform,hj];exact hupper,?_⟩
  constructor
  · intro he
    rw [hform,hj] at he
    have hz : (2*delta 0-delta 1)^2=0 := by nlinarith [sq_nonneg (2*delta 0-delta 1)]
    have heq : 2*delta 0=delta 1 := by nlinarith
    ext i
    fin_cases i
    · change delta 0=actualStep 0
      rw [actual_source_step_coordinates_active_constraint_and_improvement.1]
      linarith
    · change delta 1=actualStep 1
      rw [actual_source_step_coordinates_active_constraint_and_improvement.2.1]
      linarith
  · intro he;rw [he]

theorem actual_source_predicted_improvement_is_the_greatest_feasible_value :
    IsGreatest {value : ℝ | ∃ delta : Fin 2 → ℝ,
      actualQuadraticKL delta ≤ 1/20 ∧ actualPredictedImprovement delta=value}
      (2*actualScale) := by
  have h := actual_source_step_coordinates_active_constraint_and_improvement
  refine ⟨⟨actualStep,h.2.2.1.le,h.2.2.2⟩,?_⟩
  rintro value ⟨delta,hd,he⟩
  rw [← he,← h.2.2.2]
  exact (actual_source_step_is_the_unique_global_quadratic_trust_region_optimizer delta hd).1

theorem actual_source_step_and_improvement_roundings :
    |actualStep 0-0.111803| < (0.0000005:ℝ) ∧
      |actualStep 1-0.223607| < 0.0000005 ∧
      |actualPredictedImprovement actualStep-0.447214| < 0.0000005 := by
  have hs : actualScale^2=(1/20:ℝ) := Real.sq_sqrt (by norm_num)
  have hp : 0 ≤ actualScale := Real.sqrt_nonneg _
  have hl : (0.223606797:ℝ) < actualScale := by nlinarith
  have hu : actualScale < (0.223606798:ℝ) := by nlinarith
  have h := actual_source_step_coordinates_active_constraint_and_improvement
  rw [h.1,h.2.1,h.2.2.2]
  refine ⟨?_,?_,?_⟩ <;> apply abs_lt.mpr <;> constructor <;> linarith

end SafeLearning.CompleteAppliedNaturalStep
