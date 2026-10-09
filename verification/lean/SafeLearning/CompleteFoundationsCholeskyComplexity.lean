import SafeLearning.CompleteFoundationsCholeskyCost
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SafeLearning.CompleteFoundationsCholeskyComplexity
open Filter Asymptotics
open scoped BigOperators Topology
open SafeLearning.CompleteFoundationsCholeskyCost

theorem actual_program_operation_count_is_at_most_cubic (n : ℕ) :
    dimensionCost n ≤ n^3 := by
  rw [dimensionCost,actual_program_cost_as_squares]
  calc
    (∑ i∈Finset.range n,(i+1)^2) ≤ ∑ _i∈Finset.range n,n^2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := Finset.mem_range.mp hi
      exact Nat.pow_le_pow_left (by omega : i+1 ≤ n) 2
    _=n^3 := by simp [pow_succ,mul_comm]

theorem actual_source_cholesky_program_is_big_o_cubic :
    IsBigO atTop (fun n : ℕ=>(dimensionCost n : ℝ)) (fun n : ℕ=>(n : ℝ)^3) := by
  rw [isBigO_iff]
  refine ⟨1,Filter.Eventually.of_forall (fun n=>?_)⟩
  have h : (dimensionCost n : ℝ) ≤ (n : ℝ)^3 := by
    exact_mod_cast actual_program_operation_count_is_at_most_cubic n
  simpa only [Real.norm_of_nonneg (Nat.cast_nonneg _),Real.norm_of_nonneg (pow_nonneg (Nat.cast_nonneg n) 3),one_mul] using h
end SafeLearning.CompleteFoundationsCholeskyComplexity
