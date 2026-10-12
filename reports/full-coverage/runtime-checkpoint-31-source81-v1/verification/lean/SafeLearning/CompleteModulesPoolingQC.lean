import SafeLearning.CompleteModulesPooling
import SafeLearning.CompleteModulesWeightedSeminorm
import SafeLearning.CompleteModulesInvalidQC

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace SafeLearning.CompleteModulesPoolingQC
open CompleteModulesLipSDP CompleteModulesPooling CompleteModulesWeightedSeminorm
variable {C I : Type*} [Fintype C] [DecidableEq C] [Fintype I] [Nonempty I]

omit [Fintype C] [DecidableEq C] [Nonempty I] in
theorem actual_average_pool_increment_is_linear (first second : C × I → ℝ) :
    actualDisjointAveragePool first-actualDisjointAveragePool second=
      actualDisjointAveragePool (first-second) := by
  ext channel
  simp only [actualDisjointAveragePool,actualAverageWindow,Pi.sub_apply,Finset.sum_sub_distrib,sub_div]

omit [DecidableEq C] [Nonempty I] in
theorem actual_average_pool_commutes_with_full_channel_matrix
    (factor : Matrix C C ℝ) (input : C × I → ℝ) :
    factor*ᵥactualDisjointAveragePool input=
      actualDisjointAveragePool (fun pair : C × I =>
        (factor*ᵥ(fun channel => input (channel,pair.2))) pair.1) := by
  ext channel
  simp only [Matrix.mulVec,dotProduct,actualDisjointAveragePool,actualAverageWindow]
  simp_rw [Finset.sum_div,Finset.mul_sum,mul_div_assoc]
  exact Finset.sum_comm

theorem actual_average_pool_admits_arbitrary_positive_semidefinite_full_multiplier
    (weight : Matrix C C ℝ) (hweight : weight.PosSemidef) (input : C × I → ℝ) :
    quadratic weight (actualDisjointAveragePool input) ≤
      (1/(Fintype.card I : ℝ))*(∑ coordinate : I,quadratic weight (fun channel => input (channel,coordinate))) := by
  obtain ⟨factor,hfactor⟩ := actual_positive_semidefinite_weight_has_actual_gram_factor weight hweight
  rw [hfactor,quadratic_gram,actual_average_pool_commutes_with_full_channel_matrix]
  simp_rw [quadratic_gram]
  have hs := Finset.sum_le_sum (fun (channel : C) (_ : channel ∈ Finset.univ) =>
    actual_average_window_squared_increment_bound
      (fun coordinate => (factor*ᵥ(fun source => input (source,coordinate))) channel) (fun _ => 0))
  simp only [actualAverageWindow,Finset.sum_const_zero,zero_div,sub_zero,← Finset.mul_sum] at hs
  rw [Finset.sum_comm] at hs
  exact hs

theorem actual_average_pool_full_multiplier_incremental_qc
    (weight : Matrix C C ℝ) (hweight : weight.PosSemidef) (first second : C × I → ℝ) :
    0 ≤ (1/(Fintype.card I : ℝ))*(∑ coordinate : I,
      quadratic weight (fun channel => first (channel,coordinate)-second (channel,coordinate)))-
        quadratic weight (actualDisjointAveragePool first-actualDisjointAveragePool second) := by
  rw [actual_average_pool_increment_is_linear]
  exact sub_nonneg.mpr (actual_average_pool_admits_arbitrary_positive_semidefinite_full_multiplier weight hweight _)

omit [DecidableEq C] in
theorem actual_maximum_pool_admits_nonnegative_diagonal_incremental_multiplier
    (weight : C → ℝ) (hweight : ∀ channel,0 ≤ weight channel) (first second : C × I → ℝ) :
    0 ≤ (∑ channel : C,weight channel*(∑ coordinate : I,(first (channel,coordinate)-second (channel,coordinate))^2))-
      ∑ channel : C,weight channel*((actualDisjointMaximumPool first-actualDisjointMaximumPool second) channel)^2 := by
  apply sub_nonneg.mpr
  apply Finset.sum_le_sum
  intro channel _
  exact mul_le_mul_of_nonneg_left
    (actual_maximum_window_squared_increment_bound (fun coordinate => first (channel,coordinate))
      (fun coordinate => second (channel,coordinate))) (hweight channel)

def actualCoupledMaximumPoolQC (first second : Fin 2 × Fin 2 → ℝ) : ℝ :=
  (∑ coordinate : Fin 2,quadratic CompleteModulesInvalidQC.coupledMultiplier
    (fun channel => first (channel,coordinate)-second (channel,coordinate)))-
      quadratic CompleteModulesInvalidQC.coupledMultiplier
        (actualDisjointMaximumPool first-actualDisjointMaximumPool second)

def actualMaxPoolCounterexampleFirst : Fin 2 × Fin 2 → ℝ :=
  fun pair => if pair.2=0 then (if pair.1=0 then 2 else -2) else 0

def actualMaxPoolCounterexampleSecond : Fin 2 × Fin 2 → ℝ :=
  fun pair => if pair.2=0 then (if pair.1=0 then 1 else -3) else 0

theorem actual_coupled_maximum_pool_qc_fails :
    actualCoupledMaximumPoolQC actualMaxPoolCounterexampleFirst actualMaxPoolCounterexampleSecond=(-1:ℝ) := by
  norm_num [actualCoupledMaximumPoolQC,actualMaxPoolCounterexampleFirst,actualMaxPoolCounterexampleSecond,
    actualDisjointMaximumPool,actualMaximumWindow,quadratic,CompleteModulesInvalidQC.coupledMultiplier,
    Matrix.mulVec,dotProduct,Fin.sum_univ_two,Finset.univ_fin2]

theorem actual_positive_semidefinite_full_multiplier_is_not_valid_for_maximum_pool :
    CompleteModulesInvalidQC.coupledMultiplier.PosSemidef ∧
      ¬ ∀ first second : Fin 2 × Fin 2 → ℝ,0 ≤ actualCoupledMaximumPoolQC first second := by
  refine ⟨CompleteModulesInvalidQC.coupled_multiplier_is_positive_semidefinite,?_⟩
  intro h
  have hf := h actualMaxPoolCounterexampleFirst actualMaxPoolCounterexampleSecond
  rw [actual_coupled_maximum_pool_qc_fails] at hf
  norm_num at hf

end SafeLearning.CompleteModulesPoolingQC
