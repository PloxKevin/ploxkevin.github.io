import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Matrix Set
open scoped BigOperators
namespace SafeLearning.CompleteModulesNNDoublyHyperdominant24

theorem actual_monotone_samples_monovary
    {n : Type*} (phi : ℝ→ℝ) (hphi : Monotone phi) (v : n→ℝ) :
    Monovary v (fun i=>phi (v i)) := by
  intro i j hij
  by_contra h
  exact (not_lt_of_ge (hphi (le_of_lt (lt_of_not_ge h)))) hij

theorem actual_doubly_stochastic_cross_product_is_bounded_by_matching_product
    {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : P∈Matrix.doublyStochastic ℝ n)
    (v w : n→ℝ) (hvw : Monovary v w) :
    v ⬝ᵥ (P*ᵥw) ≤ v ⬝ᵥw := by
  classical
  obtain ⟨a,ha,hasum,haP⟩ := Matrix.exists_eq_sum_perm_of_mem_doublyStochastic hP
  have hperm : ∀ e : Equiv.Perm n, v ⬝ᵥ (e.permMatrix ℝ*ᵥw)≤v ⬝ᵥw := by
    intro e
    rw [Equiv.Perm.permMatrix_mulVec]
    exact hvw.sum_mul_comp_perm_le_sum_mul
  have hsum : ∑ e : Equiv.Perm n, a e*(v ⬝ᵥ (e.permMatrix ℝ*ᵥw)) ≤
      ∑ e : Equiv.Perm n,a e*(v ⬝ᵥw) :=
    Finset.sum_le_sum (fun e _=>mul_le_mul_of_nonneg_left (hperm e) (ha e))
  have heq : v ⬝ᵥ (P*ᵥw)=∑ e : Equiv.Perm n,a e*(v ⬝ᵥ (e.permMatrix ℝ*ᵥw)) := by
    rw [←haP]
    simp [Matrix.mulVec,Matrix.dotProduct,Finset.mul_sum,Finset.sum_mul,
      Finset.sum_comm,Finset.sum_congr,smul_eq_mul,mul_assoc]
  rw [heq]
  simpa only [←Finset.sum_mul,hasum,one_mul] using hsum

end SafeLearning.CompleteModulesNNDoublyHyperdominant24
