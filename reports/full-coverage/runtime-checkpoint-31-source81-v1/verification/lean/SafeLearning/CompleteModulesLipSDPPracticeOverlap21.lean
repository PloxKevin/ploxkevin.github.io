import SafeLearning.CompleteModulesInvalidQC
import SafeLearning.CompleteModulesLipSDPWalkthrough

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix Polynomial
open scoped BigOperators Matrix.Norms.L2Operator
namespace SafeLearning.CompleteModulesLipSDPPracticeOverlap21
open CompleteModulesInvalidQC CompleteModulesLipSDP CompleteModulesLipSDPProduct
  CompleteModulesLipSDPWalkthrough

def firstInput : Fin 2 → ℝ := ![0,2]
def secondInput : Fin 2 → ℝ := ![-1,0]

theorem actual_source_multiplier_is_psd_with_outer_product_form :
    coupledMultiplier = vecMulVec (![1,-1] : Fin 2 → ℝ) ![1,-1] ∧
      coupledMultiplier.PosSemidef ∧
      (∀ y : Fin 2 → ℝ, y ⬝ᵥ (coupledMultiplier *ᵥ y) = (y 0-y 1)^2) := by
  refine ⟨?_, coupled_multiplier_is_positive_semidefinite, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [coupledMultiplier,vecMulVec]
  · intro y
    simp [coupledMultiplier,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
    ring

theorem actual_literal_relu_increments_and_negative_coupled_qc :
    firstInput-secondInput = ![1,2] ∧
      reluVector firstInput-reluVector secondInput = ![0,2] ∧
      coupledIncrementQC firstInput secondInput = -4 := by
  refine ⟨?_,?_,?_⟩
  · ext i; fin_cases i <;> norm_num [firstInput,secondInput]
  · ext i; fin_cases i <;> norm_num [firstInput,secondInput,reluVector]
  · norm_num [firstInput,secondInput,reluVector,coupledIncrementQC,coupledMultiplier,
      Matrix.mulVec,dotProduct,Fin.sum_univ_two]

theorem actual_identity_multiplier_has_both_scalar_contributions_zero :
    2*(0:ℝ)*(1-0)=0 ∧ 2*(2:ℝ)*(2-2)=0 ∧
      2*((reluVector firstInput-reluVector secondInput) ⬝ᵥ
        ((1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ
          (firstInput-secondInput-(reluVector firstInput-reluVector secondInput))))=0 := by
  norm_num [firstInput,secondInput,reluVector,Matrix.mulVec,dotProduct,Fin.sum_univ_two]

def pooling : Matrix (Fin 2) (Fin 3) ℝ := !![1/2,1/2,0;0,1/2,1/2]

theorem actual_pooling_map_and_row_gram (x : Fin 3 → ℝ) :
    pooling *ᵥ x = ![(x 0+x 1)/2,(x 1+x 2)/2] ∧
      pooling * poolingᵀ = !![1/2,1/4;1/4,1/2] := by
  constructor
  · ext i; fin_cases i <;>
      simp [pooling,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [pooling,Matrix.mul_apply,Fin.sum_univ_succ]

theorem actual_pooling_gram_full_spectrum (eigenvalue : ℝ) :
    eigenvalue ∈ spectrum ℝ (pooling * poolingᵀ) ↔
      eigenvalue=3/4 ∨ eigenvalue=1/4 := by
  have he := (actual_pooling_map_and_row_gram (0 : Fin 3 → ℝ)).2
  have hc : (pooling * poolingᵀ).charpoly=(X-C (3/4:ℝ))*(X-C (1/4)) := by
    rw [he,Matrix.charpoly_fin_two,Matrix.det_fin_two]
    norm_num [Matrix.trace,Fin.sum_univ_two]
    have hC : C (3/4:ℝ)+C (1/4)=(1:ℝ[X]) := by
      rw [←map_add];norm_num
    have hP : C (3/4:ℝ)*C (1/4)=C (3/16:ℝ) := by
      rw [←map_mul];norm_num
    calc
      _ = X^2-(C (3/4:ℝ)+C (1/4))*X+C (3/4:ℝ)*C (1/4) := by
        rw [hC,hP];ring
      _ = _ := by ring
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly,Polynomial.IsRoot,hc]
  simp [mul_eq_zero,sub_eq_zero]

theorem actual_pooling_every_input_energy_identity (x : Fin 3 → ℝ) :
    (3/4:ℝ)*(∑ i, x i^2) - (∑ j, ((pooling *ᵥ x) j)^2) =
      ((x 0-x 1+x 2)^2+(x 0-x 2)^2)/4 := by
  rw [(actual_pooling_map_and_row_gram x).1]
  simp [Fin.sum_univ_succ]
  ring

theorem actual_pooling_spectral_norm_squared_and_value :
    ‖pooling‖^2=3/4 ∧ ‖pooling‖=Real.sqrt 3/2 := by
  have hu : ‖pooling‖ ≤ Real.sqrt (3/4:ℝ) := by
    apply actual_spectral_norm_le_of_quadratic_bound _ _ (by norm_num)
    intro x
    have he := actual_pooling_every_input_energy_identity x
    nlinarith [sq_nonneg (x 0-x 1+x 2),sq_nonneg (x 0-x 2)]
  have hl := actual_spectral_matrix_gain pooling (![1,2,1] : Fin 3 → ℝ)
  have hi : ‖WithLp.toLp 2 (![1,2,1] : Fin 3 → ℝ)‖^2=6 := by
    rw [squared_norm_of_coordinates]
    norm_num [Fin.sum_univ_succ]
  have ho : ‖WithLp.toLp 2 (pooling *ᵥ (![1,2,1] : Fin 3 → ℝ))‖^2=9/2 := by
    rw [squared_norm_of_coordinates,(actual_pooling_map_and_row_gram _).1]
    norm_num [Fin.sum_univ_two]
  have hs : ‖pooling‖^2=3/4 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3/4 by norm_num),
      Real.sqrt_nonneg (3/4:ℝ),norm_nonneg pooling,
      norm_nonneg (WithLp.toLp 2 (![1,2,1] : Fin 3 → ℝ)),
      norm_nonneg (WithLp.toLp 2 (pooling *ᵥ (![1,2,1] : Fin 3 → ℝ)))]
  refine ⟨hs,?_⟩
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num),
    Real.sqrt_nonneg 3,norm_nonneg pooling]

theorem actual_source_pooling_attainer_and_overlap_counterexample :
    (∑ i : Fin 3, (![1,2,1] : Fin 3 → ℝ) i^2)=6 ∧
      (∑ j : Fin 2, ((pooling *ᵥ (![1,2,1] : Fin 3 → ℝ)) j)^2)=9/2 ∧
      (9/2:ℝ)/6=3/4 ∧
      ¬ (∀ x : Fin 3 → ℝ, (∑ j, ((pooling *ᵥ x) j)^2) ≤
        (1/2:ℝ)*(∑ i, x i^2)) := by
  have hi : (∑ i : Fin 3, (![1,2,1] : Fin 3 → ℝ) i^2)=6 := by
    norm_num [Fin.sum_univ_succ]
  have ho : (∑ j : Fin 2, ((pooling *ᵥ (![1,2,1] : Fin 3 → ℝ)) j)^2)=9/2 := by
    rw [(actual_pooling_map_and_row_gram _).1]
    norm_num [Fin.sum_univ_two]
  refine ⟨hi,ho,by norm_num,?_⟩
  intro h
  have hh := h ![1,2,1]
  rw [hi,ho] at hh
  norm_num at hh

theorem actual_pooling_gain_roundings_and_general_bound :
    |‖pooling‖-(0.866025:ℝ)|<0.0000005 ∧
      |1/Real.sqrt 2-(0.707107:ℝ)|<0.0000005 ∧
      1/Real.sqrt 2<‖pooling‖ ∧ ‖pooling‖ ≤ 1 := by
  rw [actual_pooling_spectral_norm_squared_and_value.2]
  have h3 := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have h2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have p3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have p2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have lo3 : (1.732049:ℝ)<Real.sqrt 3 := by nlinarith
  have up3 : Real.sqrt 3<(1.732051:ℝ) := by nlinarith
  have lo2 : (1.414213:ℝ)<Real.sqrt 2 := by nlinarith
  have up2 : Real.sqrt 2<(1.414214:ℝ) := by nlinarith
  have il : (0.7071065:ℝ)<1/Real.sqrt 2 := by
    rw [lt_div_iff₀ p2]
    nlinarith
  have iu : 1/Real.sqrt 2<(0.7071075:ℝ) := by
    rw [div_lt_iff₀ p2]
    nlinarith
  refine ⟨?_,?_,?_,?_⟩
  · rw [abs_lt];constructor <;> linarith
  · rw [abs_lt];constructor <;> linarith
  · linarith
  · nlinarith

end SafeLearning.CompleteModulesLipSDPPracticeOverlap21
