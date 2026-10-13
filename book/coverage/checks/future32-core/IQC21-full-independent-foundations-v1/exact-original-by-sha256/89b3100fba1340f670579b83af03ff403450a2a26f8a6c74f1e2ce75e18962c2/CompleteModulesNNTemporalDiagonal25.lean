import SafeLearning.CompleteModulesNNDoublyHyperdominant25

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Matrix Set
open scoped BigOperators
namespace SafeLearning.CompleteModulesNNTemporalDiagonal25
open SafeLearning.CompleteModulesNNDoublyHyperdominant25

def prefixToeplitz (S : Finset ℤ) (c : ℤ→ℝ) (N : ℕ) :
    Matrix (Fin (N+1)) (Fin (N+1)) ℝ :=
  fun i j=>∑ d∈S, if (i.val:ℤ)-(j.val:ℤ)=d then c d else 0

private theorem injective_coefficient_contribution_lower_bound
    {n : Type*} [Fintype n] [DecidableEq n]
    (g : n→ℤ) (hinj : Function.Injective g) (hzero : ∃ j,g j=0)
    (d : ℤ) (c : ℝ) (hc : d≠0→c≤0) :
    c≤∑ j,if g j=d then c else 0 := by
  classical
  by_cases h : ∃ j,g j=d
  · obtain ⟨j,hj⟩ := h
    have he : (∑ k,if g k=d then c else 0)=c := by
      rw [Finset.sum_eq_single j]
      · simp [hj]
      · intro k _ hkj
        have hk : g k≠d := fun hk=>hkj (hinj (hk.trans hj.symm))
        simp [hk]
      · simp
    rw [he]
  · have hn : d≠0 := by
      intro hd
      subst d
      exact h hzero
    have he : (∑ k,if g k=d then c else 0)=0 := by
      apply Finset.sum_eq_zero
      intro k _
      have hk : g k≠d := fun hk=>h ⟨k,hk⟩
      simp [hk]
    rw [he]
    exact hc hn

theorem actual_every_finite_fir_prefix_toeplitz_matrix_is_doubly_hyperdominant
    (S : Finset ℤ) (c : ℤ→ℝ) (hc : ∀ d,d≠0→c d≤0)
    (hsum : 0≤∑ d∈S,c d) (N : ℕ) :
    (∀ i j,i≠j→prefixToeplitz S c N i j≤0) ∧
      (∀ i,0≤∑ j,prefixToeplitz S c N i j) ∧
      (∀ j,0≤∑ i,prefixToeplitz S c N i j) := by
  refine ⟨?_,?_,?_⟩
  · intro i j hij
    unfold prefixToeplitz
    apply Finset.sum_nonpos
    intro d _
    split_ifs with h
    · apply hc
      intro hd
      subst d
      apply hij
      apply Fin.ext
      omega
    · exact le_rfl
  · intro i
    have hbound : (∑ d∈S,c d)≤∑ j,prefixToeplitz S c N i j := by
      unfold prefixToeplitz
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro d _
      apply injective_coefficient_contribution_lower_bound
        (fun j : Fin (N+1)=>(i.val:ℤ)-(j.val:ℤ)) ?_ ⟨i,by simp⟩ d (c d) (hc d)
      intro j k hjk
      dsimp at hjk
      apply Fin.ext
      omega
    exact hsum.trans hbound
  · intro j
    have hbound : (∑ d∈S,c d)≤∑ i,prefixToeplitz S c N i j := by
      unfold prefixToeplitz
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro d _
      apply injective_coefficient_contribution_lower_bound
        (fun i : Fin (N+1)=>(i.val:ℤ)-(j.val:ℤ)) ?_ ⟨j,by simp⟩ d (c d) (hc d)
      intro i k hik
      dsimp at hik
      apply Fin.ext
      omega
    exact hsum.trans hbound

theorem actual_time_invariant_monotone_channel_has_the_true_finite_fir_hard_prefix_qc
    (S : Finset ℤ) (c : ℤ→ℝ) (hc : ∀ d,d≠0→c d≤0)
    (hsum : 0≤∑ d∈S,c d) (phi : ℝ→ℝ) (hphi : Monotone phi)
    (hz : phi 0=0) (v : ℕ→ℝ) (N : ℕ) :
    0≤2*∑ i : Fin (N+1),∑ j : Fin (N+1),
      v i.val*(prefixToeplitz S c N i j)*phi (v j.val) := by
  obtain ⟨hoff,hrow,hcol⟩ :=
    actual_every_finite_fir_prefix_toeplitz_matrix_is_doubly_hyperdominant S c hc hsum N
  have h := actual_repeated_monotone_map_satisfies_every_doubly_hyperdominant_qc
    (prefixToeplitz S c N) hoff hrow hcol phi hphi hz (fun i=>v i.val)
  have he : (fun i : Fin (N+1)=>v i.val) ⬝ᵥ
      (prefixToeplitz S c N *ᵥ (fun j=>phi (v j.val))) =
      ∑ i : Fin (N+1),∑ j : Fin (N+1),v i.val*prefixToeplitz S c N i j*phi (v j.val) := by
    simp [dotProduct,Matrix.mulVec,Finset.mul_sum,mul_assoc]
  rw [he] at h
  exact mul_nonneg (by norm_num) h

theorem actual_diagonal_temporal_coefficients_allow_independent_monotone_channels
    {n : Type*} [Fintype n]
    (S : Finset ℤ) (c : n→ℤ→ℝ) (hc : ∀ i d,d≠0→c i d≤0)
    (hsum : ∀ i,0≤∑ d∈S,c i d)
    (phi : n→ℝ→ℝ) (hphi : ∀ i,Monotone (phi i)) (hz : ∀ i,phi i 0=0)
    (v : ℕ→n→ℝ) (N : ℕ) :
    0≤∑ k : n,2*∑ i : Fin (N+1),∑ j : Fin (N+1),
      v i.val k*(prefixToeplitz S (c k) N i j)*phi k (v j.val k) := by
  exact Finset.sum_nonneg fun k _=>
    actual_time_invariant_monotone_channel_has_the_true_finite_fir_hard_prefix_qc
      S (c k) (hc k) (hsum k) (phi k) (hphi k) (hz k) (fun t=>v t k) N

end SafeLearning.CompleteModulesNNTemporalDiagonal25
