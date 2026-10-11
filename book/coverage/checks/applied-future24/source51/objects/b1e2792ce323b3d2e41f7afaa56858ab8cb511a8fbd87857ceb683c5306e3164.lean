import SafeLearning.CompleteAppliedEntropyConditionals
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedEntropyDisintegration
open MeasureTheory ProbabilityTheory Set
open SafeLearning.CompleteAppliedInformation SafeLearning.CompleteAppliedFiniteEntropy
open SafeLearning.CompleteAppliedEntropyChain SafeLearning.CompleteAppliedEntropyConditionals
open scoped ENNReal NNReal Classical

theorem actual_first_marginal_row_sum {n m : ℕ} (law : PMF (Fin n × Fin m)) (i : Fin n) :
    (law.map Prod.fst) i=∑' j,law (i,j) := by
  rw [PMF.map_apply,tsum_fintype,Fintype.sum_prod_type,tsum_fintype]
  calc
    _ = (∑ a,if i=a then ∑ j,law (a,j) else 0) := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases h : i=a
      · simp [h]
      · simp [h]
    _ = _ := by simp

def actualPosteriorKernel {n m : ℕ} (law : PMF (Fin n × Fin m)) (i : Fin n) : PMF (Fin m) :=
  if h : (law.map Prod.fst) i=0 then law.map Prod.snd
  else PMF.normalize (fun j => law (i,j))
    (by rwa [← actual_first_marginal_row_sum])
    (by rw [← actual_first_marginal_row_sum];exact (law.map Prod.fst).apply_ne_top i)

theorem actual_posterior_kernel_atom {n m : ℕ} (law : PMF (Fin n × Fin m)) (i : Fin n)
    (hi : (law.map Prod.fst) i≠0) (j : Fin m) :
    actualPosteriorKernel law i j=law (i,j)*((law.map Prod.fst) i)⁻¹ := by
  rw [actualPosteriorKernel,dite_eq_right hi,PMF.normalize_apply,← actual_first_marginal_row_sum]

theorem actual_zero_marginal_zero_joint_atom {n m : ℕ} (law : PMF (Fin n × Fin m))
    (i : Fin n) (hi : (law.map Prod.fst) i=0) (j : Fin m) : law (i,j)=0 := by
  have hsum := actual_first_marginal_row_sum law i
  rw [hi,tsum_fintype] at hsum
  apply le_antisymm _ bot_le
  calc
    law (i,j) ≤ ∑ k,law (i,k) :=
      Finset.single_le_sum (f := fun k : Fin m => law (i,k))
        (fun _ _ => bot_le) (Finset.mem_univ j)
    _ = 0 := hsum.symm

theorem actual_every_joint_factorizes {n m : ℕ} (law : PMF (Fin n × Fin m)) :
    conditionalJoint (law.map Prod.fst) (actualPosteriorKernel law)=law := by
  ext ij
  rcases ij with ⟨i,j⟩
  rw [actual_conditional_joint_atom]
  by_cases hi : (law.map Prod.fst) i=0
  · rw [hi,zero_mul,actual_zero_marginal_zero_joint_atom law i hi j]
  · rw [actual_posterior_kernel_atom law i hi]
    calc
      _ = law (i,j)*((law.map Prod.fst) i*((law.map Prod.fst) i)⁻¹) := by ring
      _ = law (i,j) := by rw [ENNReal.mul_inv_cancel hi ((law.map Prod.fst).apply_ne_top i),mul_one]

theorem actual_arbitrary_joint_conditional_entropy_chain_rule {n m : ℕ}
    (law : PMF (Fin n × Fin m)) :
    actualJointEntropy law=shannonEntropy (law.map Prod.fst)+genuineConditionalEntropy law := by
  have h := actual_measure_conditioned_entropy_chain_rule (law.map Prod.fst)
    (actualPosteriorKernel law)
  rw [actual_every_joint_factorizes] at h
  exact h

theorem actual_posterior_kernel_is_conditional_law {n m : ℕ}
    (law : PMF (Fin n × Fin m)) (i : Fin n) (hi : (law.map Prod.fst) i≠0) :
    actualConditionalSecond law i=(actualPosteriorKernel law i).toMeasure := by
  have h := actual_second_conditional_law (law.map Prod.fst) (actualPosteriorKernel law) i hi
  rw [actual_every_joint_factorizes] at h
  exact h

end SafeLearning.CompleteAppliedEntropyDisintegration
