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
    (P : Matrix n n ℝ) (hP : P∈doublyStochastic ℝ n)
    (v w : n→ℝ) (hvw : Monovary v w) :
    v ⬝ᵥ (P*ᵥ w) ≤ v ⬝ᵥw := by
  classical
  obtain ⟨a,ha,hasum,haP⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hP
  have hperm : ∀ e : Equiv.Perm n, v ⬝ᵥ (e.permMatrix ℝ *ᵥ w)≤v ⬝ᵥw := by
    intro e
    rw [Matrix.permMatrix_mulVec]
    exact hvw.sum_mul_comp_perm_le_sum_mul
  have hsum : ∑ e : Equiv.Perm n, a e*(v ⬝ᵥ (e.permMatrix ℝ *ᵥ w)) ≤
      ∑ e : Equiv.Perm n,a e*(v ⬝ᵥw) :=
    Finset.sum_le_sum (fun e _=>mul_le_mul_of_nonneg_left (hperm e) (ha e))
  have heq : v ⬝ᵥ (P*ᵥ w)=∑ e : Equiv.Perm n,a e*(v ⬝ᵥ (e.permMatrix ℝ *ᵥ w)) := by
    rw [←haP]
    simp only [Matrix.sum_mulVec,dotProduct_sum,Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]
  rw [heq]
  simpa only [←Finset.sum_mul,hasum,one_mul] using hsum

def scale {n : Type*} [Fintype n] (M : Matrix n n ℝ) : ℝ :=
  1 + ∑ i, ∑ j, |M i j|

def augmented {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) : Matrix (Option n) (Option n) ℝ
  | some i, some j => (if i=j then 1 else 0) - M i j / scale M
  | some i, none => (∑ j, M i j) / scale M
  | none, some j => (∑ i, M i j) / scale M
  | none, none => 1 - (∑ i, ∑ j, M i j) / scale M

theorem actual_scale_is_positive_and_bounds_each_diagonal_and_total_mass
    {n : Type*} [Fintype n] (M : Matrix n n ℝ) :
    0 < scale M ∧ (∀ i, M i i ≤ scale M) ∧ (∑ i, ∑ j, M i j) ≤ scale M := by
  have hn : 0 ≤ ∑ i, ∑ j, |M i j| := Finset.sum_nonneg fun i _=>
    Finset.sum_nonneg fun j _=>abs_nonneg _
  refine ⟨by unfold scale; linarith, ?_, ?_⟩
  · intro i
    have hrow : |M i i| ≤ ∑ j, |M i j| :=
      Finset.single_le_sum (fun j _=>abs_nonneg (M i j)) (Finset.mem_univ i)
    have htotal : (∑ j, |M i j|) ≤ ∑ k, ∑ j, |M k j| :=
      Finset.single_le_sum (fun k _=>Finset.sum_nonneg fun j _=>abs_nonneg (M k j)) (Finset.mem_univ i)
    have h := le_abs_self (M i i)
    unfold scale
    linarith
  · have hsum : (∑ i, ∑ j, M i j) ≤ ∑ i, ∑ j, |M i j| :=
      Finset.sum_le_sum fun i _=>Finset.sum_le_sum fun j _=>le_abs_self _
    unfold scale
    linarith

theorem actual_doubly_hyperdominant_matrix_has_a_true_augmented_doubly_stochastic_model
    {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ)
    (hoff : ∀ i j, i≠j → M i j≤0)
    (hrow : ∀ i, 0≤∑ j,M i j) (hcol : ∀ j,0≤∑ i,M i j) :
    augmented M ∈ doublyStochastic ℝ (Option n) := by
  classical
  obtain ⟨hl,hd,ht⟩ := actual_scale_is_positive_and_bounds_each_diagonal_and_total_mass M
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨?_,?_,?_⟩
  · intro i j
    cases i with
    | none =>
      cases j with
      | none =>
        simp only [augmented]
        have h : (∑ i,∑ j,M i j)/scale M≤1 :=
          (div_le_iff₀ hl).mpr (by simpa using ht)
        linarith
      | some j => exact div_nonneg (hcol j) hl.le
    | some i =>
      cases j with
      | none => exact div_nonneg (hrow i) hl.le
      | some j =>
        by_cases hij : i=j
        · subst j
          simp only [augmented,ite_true]
          have h : M i i/scale M≤1 :=
            (div_le_iff₀ hl).mpr (by simpa using hd i)
          linarith
        · simp only [augmented,ite_eq_right hij,zero_sub]
          exact neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg (hoff i j hij) hl.le)
  · intro i
    cases i with
    | none =>
      simp only [Fintype.sum_option,augmented]
      rw [←Finset.sum_div,Finset.sum_comm]
      ring
    | some i =>
      simp only [Fintype.sum_option,augmented]
      rw [Finset.sum_sub_distrib,←Finset.sum_div]
      simp
  · intro j
    cases j with
    | none =>
      simp only [Fintype.sum_option,augmented]
      rw [←Finset.sum_div]
      ring
    | some j =>
      simp only [Fintype.sum_option,augmented]
      rw [Finset.sum_sub_distrib,←Finset.sum_div]
      simp

theorem actual_augmented_zero_padded_cross_product_is_the_scaled_original_form
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (v w : n→ℝ) :
    (fun i : Option n=>i.elim 0 v) ⬝ᵥ
      (augmented M *ᵥ (fun i : Option n=>i.elim 0 w)) =
        v ⬝ᵥ w - (v ⬝ᵥ (M *ᵥ w))/scale M := by
  classical
  simp only [dotProduct,Matrix.mulVec,Fintype.sum_option,Option.elim_none,
    Option.elim_some,zero_mul,zero_add,augmented,mul_zero]
  simp_rw [sub_mul,Finset.sum_sub_distrib]
  simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  simp_rw [mul_sub,Finset.sum_sub_distrib]
  congr 1
  simp_rw [Finset.mul_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem actual_repeated_monotone_map_satisfies_every_doubly_hyperdominant_qc
    {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ)
    (hoff : ∀ i j, i≠j → M i j≤0)
    (hrow : ∀ i, 0≤∑ j,M i j) (hcol : ∀ j,0≤∑ i,M i j)
    (phi : ℝ→ℝ) (hphi : Monotone phi) (hz : phi 0=0) (v : n→ℝ) :
    0 ≤ v ⬝ᵥ (M *ᵥ (fun i=>phi (v i))) := by
  let x : Option n→ℝ := fun i=>i.elim 0 v
  have hp := actual_doubly_hyperdominant_matrix_has_a_true_augmented_doubly_stochastic_model
    M hoff hrow hcol
  have hmono := actual_monotone_samples_monovary phi hphi x
  have hs := actual_doubly_stochastic_cross_product_is_bounded_by_matching_product
    (augmented M) hp x (fun i=>phi (x i)) hmono
  have hx : (fun i=>phi (x i))=(fun i : Option n=>i.elim 0 (fun j=>phi (v j))) := by
    funext i
    cases i <;> simp [x,hz]
  rw [hx] at hs
  rw [actual_augmented_zero_padded_cross_product_is_the_scaled_original_form] at hs
  have hxw : x ⬝ᵥ (fun i : Option n=>i.elim 0 (fun j=>phi (v j))) =
      v ⬝ᵥ (fun j=>phi (v j)) := by simp [x,dotProduct,Fintype.sum_option]
  rw [hxw] at hs
  have hl := (actual_scale_is_positive_and_bounds_each_diagonal_and_total_mass M).1
  have hd : 0≤(v ⬝ᵥ (M *ᵥ (fun i=>phi (v i))))/scale M := by linarith
  have hnum := mul_nonneg hd hl.le
  simpa only [div_mul_cancel₀ _ hl.ne'] using hnum

end SafeLearning.CompleteModulesNNDoublyHyperdominant24

namespace SafeLearning.CompleteModulesNNTemporalDiagonal24
open SafeLearning.CompleteModulesNNDoublyHyperdominant24

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

end SafeLearning.CompleteModulesNNTemporalDiagonal24
