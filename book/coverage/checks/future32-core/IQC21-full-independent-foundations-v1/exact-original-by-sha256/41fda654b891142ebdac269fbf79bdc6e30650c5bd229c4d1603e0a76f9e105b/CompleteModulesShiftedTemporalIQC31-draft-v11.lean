import SafeLearning.CompleteModulesNNTemporalDiagonal25
import SafeLearning.CompleteModulesNNTanhOffset24

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix Set
open scoped BigOperators
namespace SafeLearning.CompleteModulesShiftedTemporalIQC31
open CompleteModulesNNDoublyHyperdominant25 CompleteModulesNNTemporalDiagonal25
open CompleteModulesLipSDP CompleteModulesNNTanhOffset24

theorem actual_doubly_hyperdominant_qc_needs_only_zero_padded_monovary_samples
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (hoff : ∀ i j,i≠j→M i j≤0)
    (hrow : ∀ i,0≤∑ j,M i j) (hcol : ∀ j,0≤∑ i,M i j)
    (v w : n→ℝ)
    (hmono : Monovary (fun i : Option n=>i.elim 0 v) (fun i : Option n=>i.elim 0 w)) :
    0≤v ⬝ᵥ (M*ᵥ w) := by
  have hp := actual_doubly_hyperdominant_matrix_has_a_true_augmented_doubly_stochastic_model M hoff hrow hcol
  have hs := actual_doubly_stochastic_cross_product_is_bounded_by_matching_product
    (augmented M) hp (fun i : Option n=>i.elim 0 v) (fun i : Option n=>i.elim 0 w) hmono
  rw [actual_augmented_zero_padded_cross_product_is_the_scaled_original_form] at hs
  have hx : (fun i : Option n=>i.elim 0 v) ⬝ᵥ (fun i : Option n=>i.elim 0 w)=v⬝ᵥw := by
    simp [dotProduct,Fintype.sum_option]
  rw [hx] at hs
  have hl := (actual_scale_is_positive_and_bounds_each_diagonal_and_total_mass M).1
  have hd : 0≤(v⬝ᵥ(M*ᵥw))/scale M := by linarith
  have hn := mul_nonneg hd hl.le
  simpa only [div_mul_cancel₀ _ hl.ne'] using hn

theorem actual_slope_bounds_make_both_loop_transformed_coordinates_monotone
    (phi : ℝ→ℝ) (mu nu : ℝ) (hs : slopeRestricted phi mu nu) :
    Monotone (fun x=>nu*x-phi x) ∧ Monotone (fun x=>phi x-mu*x) := by
  constructor <;> intro x y hxy
  · obtain ⟨s,hl,hu,he⟩ := hs y x
    have hn : 0≤y-x := sub_nonneg.mpr hxy
    have h := mul_nonneg (sub_nonneg.mpr hu) hn
    nlinarith
  · obtain ⟨s,hl,hu,he⟩ := hs y x
    have hn : 0≤y-x := sub_nonneg.mpr hxy
    have h := mul_nonneg (sub_nonneg.mpr hl) hn
    nlinarith

theorem actual_loop_transformed_slope_channel_has_the_full_monovary_qc
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (hoff : ∀ i j,i≠j→M i j≤0)
    (hrow : ∀ i,0≤∑ j,M i j) (hcol : ∀ j,0≤∑ i,M i j)
    (phi : ℝ→ℝ) (mu nu : ℝ) (hs : slopeRestricted phi mu nu) (hz : phi 0=0)
    (v : n→ℝ) :
    0≤(fun i=>nu*v i-phi (v i))⬝ᵥ (M *ᵥ (fun i=>phi (v i)-mu*v i)) := by
  apply actual_doubly_hyperdominant_qc_needs_only_zero_padded_monovary_samples M hoff hrow hcol
  let x : Option n→ℝ := fun i=>i.elim 0 v
  have hm := actual_slope_bounds_make_both_loop_transformed_coordinates_monotone phi mu nu hs
  have h := (hm.1.monovary hm.2).comp_right x
  have ha : (fun i=>nu*x i-phi (x i))=(fun i : Option n=>i.elim 0 (fun j=>nu*v j-phi (v j))) := by
    funext i;cases i <;> simp [x,hz]
  have hb : (fun i=>phi (x i)-mu*x i)=(fun i : Option n=>i.elim 0 (fun j=>phi (v j)-mu*v j)) := by
    funext i;cases i <;> simp [x,hz]
  simpa only [Function.comp_def,ha,hb] using h

theorem actual_every_true_slope_channel_has_a_zero_initialized_hard_temporal_prefix_qc
    (S : Finset ℤ) (c : ℤ→ℝ) (hc : ∀ d,d≠0→c d≤0)
    (hcs : 0≤∑ d∈S,c d) (phi : ℝ→ℝ) (mu nu : ℝ)
    (hs : slopeRestricted phi mu nu) (hz : phi 0=0) (v : ℕ→ℝ) (N : ℕ) :
    0≤2*∑ i : Fin (N+1),∑ j : Fin (N+1),
      (nu*v i.val-phi (v i.val))*prefixToeplitz S c N i j*(phi (v j.val)-mu*v j.val) := by
  obtain ⟨hoff,hrow,hcol⟩ := actual_every_finite_fir_prefix_toeplitz_matrix_is_doubly_hyperdominant S c hc hcs N
  have h := actual_loop_transformed_slope_channel_has_the_full_monovary_qc
    (prefixToeplitz S c N) hoff hrow hcol phi mu nu hs hz (fun i=>v i.val)
  have he : (fun i : Fin (N+1)=>nu*v i.val-phi (v i.val))⬝ᵥ
      (prefixToeplitz S c N*ᵥ(fun j=>phi (v j.val)-mu*v j.val))=
      ∑ i : Fin (N+1),∑ j : Fin (N+1),
        (nu*v i.val-phi (v i.val))*prefixToeplitz S c N i j*(phi (v j.val)-mu*v j.val) := by
    simp [dotProduct,Matrix.mulVec,Finset.mul_sum,mul_assoc]
  rw [he] at h
  exact mul_nonneg (by norm_num) h

theorem actual_independent_shifted_tanh_channels_retain_their_own_hard_temporal_qcs
    {n : Type*} [Fintype n]
    (S : Finset ℤ) (c : n→ℤ→ℝ) (hc : ∀ k d,d≠0→c k d≤0)
    (hcs : ∀ k,0≤∑ d∈S,c k d) (center : n→ℝ) (v : ℕ→n→ℝ) (N : ℕ) :
    0≤∑ k : n,2*∑ i : Fin (N+1),∑ j : Fin (N+1),
      (v i.val k-shifted (center k) (v i.val k))*prefixToeplitz S (c k) N i j*
        shifted (center k) (v j.val k) := by
  apply Finset.sum_nonneg
  intro k _
  have h := actual_every_shifted_channel_vanishes_and_has_own_valid_sector (center k)
  simpa only [one_mul,zero_mul,sub_zero] using
    actual_every_true_slope_channel_has_a_zero_initialized_hard_temporal_prefix_qc
      S (c k) (hc k) (hcs k) (shifted (center k)) 0 1 h.2.1 h.1 (fun t=>v t k) N

theorem actual_shifted_tanh_is_odd_exactly_when_its_equilibrium_center_is_zero
    (center : ℝ) : (∀ s : ℝ,shifted center (-s)=-shifted center s) ↔ center=0 := by
  constructor
  · intro h
    have hh := h center
    simp only [shifted,neg_add_cancel,Real.tanh_zero,zero_sub] at hh
    have he : Real.tanh (2*center)=2*Real.tanh center := by rw [two_mul];linarith
    rw [Real.tanh_eq_sinh_div_cosh,Real.tanh_eq_sinh_div_cosh] at he
    have hc := (Real.cosh_pos center).ne'
    have hc2 := (Real.cosh_pos (2*center)).ne'
    field_simp [hc,hc2] at he
    rw [Real.sinh_two_mul,Real.cosh_two_mul] at he
    have hs : (Real.sinh center)^3=0 := by nlinarith only [he]
    exact Real.sinh_eq_zero.mp ((pow_eq_zero_iff (by decide : (3:ℕ)≠0)).mp hs)
  · rintro rfl
    intro s
    simp [shifted,Real.tanh_neg]

end SafeLearning.CompleteModulesShiftedTemporalIQC31

namespace SafeLearning.CompleteModulesShiftedTemporalIQC31

def zeroPaddedDelay (v : ℕ→ℝ) (t j : ℕ) : ℝ := if j≤t then v (t-j) else 0

def actualLagWindow (ell : ℕ) (v : ℕ→ℝ) (t : ℕ) : Fin (ell+1)→ℝ :=
  fun j=>zeroPaddedDelay v t j.val

theorem actual_delay_window_is_the_zero_initialized_causal_shift_register
    (ell : ℕ) (v : ℕ→ℝ) :
    (∀ t,actualLagWindow ell v t 0=v t) ∧
    (∀ j : Fin ell,actualLagWindow ell v 0 j.succ=0) ∧
    (∀ t (j : Fin ell),actualLagWindow ell v (t+1) j.succ=
      actualLagWindow ell v t j.castSucc) := by
  refine ⟨?_,?_,?_⟩
  · intro t;simp [actualLagWindow,zeroPaddedDelay]
  · intro j;simp [actualLagWindow,zeroPaddedDelay]
  · intro t j
    simp only [actualLagWindow,zeroPaddedDelay,Fin.val_succ,Fin.val_castSucc]
    by_cases h : j.val≤t
    · have h1 : j.val+1≤t+1 := by omega
      have he : t+1-(j.val+1)=t-j.val := by omega
      simp [h,h1,he]
    · have h1 : ¬j.val+1≤t+1 := by omega
      simp [h,h1]

theorem actual_zero_padded_finite_delay_sum_equals_the_truncated_past_sum
    (ell N t : ℕ) (ht : t≤N) (c : ℕ→ℝ) (u : ℕ→ℝ) :
    (∑ j : Fin (ell+1),c j.val*zeroPaddedDelay u t j.val)=
      ∑ i : Fin (N+1),if i.val≤t ∧ t-i.val≤ell then c (t-i.val)*u i.val else 0 := by
  classical
  simp only [zeroPaddedDelay,mul_ite,mul_zero]
  rw [←Finset.sum_filter,←Finset.sum_filter]
  apply Finset.sum_bij (fun j hj=>
    (⟨t-j.val,by have hh := (Finset.mem_filter.mp hj).2;omega⟩ : Fin (N+1)))
  · intro j hj
    have hh := (Finset.mem_filter.mp hj).2
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    have hjlt := j.isLt
    constructor <;> omega
  · intro j hj k hk he
    have hjle := (Finset.mem_filter.mp hj).2
    have hkle := (Finset.mem_filter.mp hk).2
    have hval := congrArg Fin.val he
    apply Fin.ext
    dsimp at hval
    omega
  · intro i hi
    have hh := (Finset.mem_filter.mp hi).2
    let j : Fin (ell+1) := ⟨t-i.val,by omega⟩
    have hj : j∈Finset.univ.filter (fun j : Fin (ell+1)=>j.val≤t) := by
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      dsimp [j];omega
    refine ⟨j,hj,?_⟩
    apply Fin.ext
    dsimp [j];omega
  · intro j hj
    have hh := (Finset.mem_filter.mp hj).2
    have he : t-(t-j.val)=j.val := by omega
    dsimp
    rw [he]

end SafeLearning.CompleteModulesShiftedTemporalIQC31

namespace SafeLearning.CompleteModulesShiftedTemporalIQC31

def actualFIRWindowCoefficient (ell : ℕ) (c : ℤ→ℝ) :
    Matrix (Fin (ell+1)) (Fin (ell+1)) ℝ :=
  fun i j=>if i=0 then c (-(j.val:ℤ)) else if j=0 then c (i.val:ℤ) else 0

def actualFIRWindowMiddle (ell : ℕ) (c : ℤ→ℝ) :
    Matrix (Fin (ell+1)⊕Fin (ell+1)) (Fin (ell+1)⊕Fin (ell+1)) ℝ :=
  Matrix.fromBlocks 0 (actualFIRWindowCoefficient ell c)ᵀ (actualFIRWindowCoefficient ell c) 0

def actualFIRWindowSupply (ell : ℕ) (c : ℤ→ℝ) (v w : ℕ→ℝ) (t : ℕ) : ℝ :=
  2*(actualLagWindow ell w t⬝ᵥ(actualFIRWindowCoefficient ell c*ᵥactualLagWindow ell v t))

theorem actual_printed_FIR_middle_matrix_has_the_exact_first_row_and_column_action
    (ell : ℕ) (c : ℤ→ℝ) (u : Fin (ell+1)→ℝ) :
    (actualFIRWindowCoefficient ell c*ᵥu) 0=∑ j,c (-(j.val:ℤ))*u j ∧
      ∀ i : Fin ell,(actualFIRWindowCoefficient ell c*ᵥu) i.succ=c (i.val+1:ℤ)*u 0 := by
  constructor
  · simp [actualFIRWindowCoefficient,Matrix.mulVec,dotProduct]
  · intro i
    simp [actualFIRWindowCoefficient,Matrix.mulVec,dotProduct,Fin.succ_ne_zero,ite_mul]

theorem actual_full_printed_FIR_window_quadratic_form_equals_its_exact_supply
    (ell : ℕ) (c : ℤ→ℝ) (v w : ℕ→ℝ) (t : ℕ) :
    (Sum.elim (actualLagWindow ell v t) (actualLagWindow ell w t))⬝ᵥ
      (actualFIRWindowMiddle ell c*ᵥ(Sum.elim (actualLagWindow ell v t) (actualLagWindow ell w t)))=
        actualFIRWindowSupply ell c v w t := by
  simp only [actualFIRWindowMiddle,Matrix.fromBlocks_mulVec,sumElim_dotProduct_sumElim,
    Matrix.zero_mulVec,zero_add,add_zero]
  rw [Matrix.dotProduct_transpose_mulVec]
  unfold actualFIRWindowSupply
  change (actualLagWindow ell w t⬝ᵥ(actualFIRWindowCoefficient ell c*ᵥactualLagWindow ell v t))+
    (actualLagWindow ell w t⬝ᵥ(actualFIRWindowCoefficient ell c*ᵥactualLagWindow ell v t))=
      2*(actualLagWindow ell w t⬝ᵥ(actualFIRWindowCoefficient ell c*ᵥactualLagWindow ell v t))
  ring

theorem actual_FIR_supply_is_the_two_causal_delay_sums_without_double_counting_zero
    (ell : ℕ) (c : ℤ→ℝ) (v w : ℕ→ℝ) (t : ℕ) :
    actualFIRWindowSupply ell c v w t=
      2*(w t*(∑ j : Fin (ell+1),c (-(j.val:ℤ))*zeroPaddedDelay v t j.val)+
        v t*((∑ j : Fin (ell+1),c (j.val:ℤ)*zeroPaddedDelay w t j.val)-c 0*w t)) := by
  have hp := actual_printed_FIR_middle_matrix_has_the_exact_first_row_and_column_action ell c
    (actualLagWindow ell v t)
  have hzv := (actual_delay_window_is_the_zero_initialized_causal_shift_register ell v).1 t
  have hzw := (actual_delay_window_is_the_zero_initialized_causal_shift_register ell w).1 t
  have hpos : (∑ j : Fin (ell+1),c (j.val:ℤ)*zeroPaddedDelay w t j.val)-c 0*w t=
      ∑ j : Fin ell,c (j.val+1:ℤ)*zeroPaddedDelay w t (j.val+1) := by
    rw [Fin.sum_univ_succ]
    simp [zeroPaddedDelay]
  unfold actualFIRWindowSupply dotProduct
  rw [Fin.sum_univ_succ]
  simp only [hp.1]
  simp_rw [hp.2]
  rw [hzv,hzw,hpos]
  simp [actualLagWindow,Finset.mul_sum,mul_comm,mul_left_comm,mul_assoc]

end SafeLearning.CompleteModulesShiftedTemporalIQC31

namespace SafeLearning.CompleteModulesShiftedTemporalIQC31

theorem actual_banded_prefix_coefficient_is_the_sum_of_two_past_triangles_once
    (ell i j : ℕ) (c : ℤ→ℝ) :
    (if (i:ℤ)-(j:ℤ)∈Finset.Icc (-(ell:ℤ)) (ell:ℤ) then c ((i:ℤ)-(j:ℤ)) else 0)=
      (if (i ≤ j ∧ j - i ≤ ell) then c ((i:ℤ)-(j:ℤ)) else 0)+
      (if (j ≤ i ∧ i - j ≤ ell) then c ((i:ℤ)-(j:ℤ)) else 0)-
      (if i = j then c 0 else 0) := by
  classical
  by_cases he : i=j
  · subst j;simp
  · rcases lt_or_gt_of_ne he with hij|hji
    · have hijle : i≤j := hij.le
      have hnot : ¬ (j ≤ i) := not_le.mpr hij
      by_cases hbound : j-i≤ell
      · have hm : (i:ℤ)-(j:ℤ)∈Finset.Icc (-(ell:ℤ)) (ell:ℤ) := by
          simp only [Finset.mem_Icc];constructor <;> omega
        simp [hm,hijle,hnot,hbound,he]
      · have hm : (i:ℤ)-(j:ℤ)∉Finset.Icc (-(ell:ℤ)) (ell:ℤ) := by
          simp only [Finset.mem_Icc];omega
        simp [hm,hijle,hnot,hbound,he]
    · have hjile : j ≤ i := hji.le
      have hnot : ¬ (i ≤ j) := not_le.mpr hji
      by_cases hbound : i-j≤ell
      · have hm : (i:ℤ)-(j:ℤ)∈Finset.Icc (-(ell:ℤ)) (ell:ℤ) := by
          simp only [Finset.mem_Icc];constructor <;> omega
        simp [hm,hjile,hnot,hbound,he]
      · have hm : (i:ℤ)-(j:ℤ)∉Finset.Icc (-(ell:ℤ)) (ell:ℤ) := by
          simp only [Finset.mem_Icc];omega
        simp [hm,hjile,hnot,hbound,he]

theorem actual_finite_band_toeplitz_entries_are_the_exact_retained_lag_coefficients
    (ell N : ℕ) (c : ℤ→ℝ) (i j : Fin (N+1)) :
    CompleteModulesNNTemporalDiagonal25.prefixToeplitz
      (Finset.Icc (-(ell:ℤ)) (ell:ℤ)) c N i j=
      if (i.val:ℤ)-(j.val:ℤ)∈Finset.Icc (-(ell:ℤ)) (ell:ℤ)
        then c ((i.val:ℤ)-(j.val:ℤ)) else 0 := by
  classical
  simp [CompleteModulesNNTemporalDiagonal25.prefixToeplitz,eq_comm]

theorem actual_causal_window_supply_at_every_time_is_the_exact_two_past_columns
    (ell N t : ℕ) (ht : t≤N) (c : ℤ→ℝ) (v w : ℕ→ℝ) :
    actualFIRWindowSupply ell c v w t=
      2*((∑ i : Fin (N+1),if i.val≤t ∧ t-i.val≤ell
          then w t*c ((i.val:ℤ)-(t:ℤ))*v i.val else 0)+
        (∑ i : Fin (N+1),if i.val≤t ∧ t-i.val≤ell
          then v t*c ((t:ℤ)-(i.val:ℤ))*w i.val else 0)-c 0*w t*v t) := by
  have hn := actual_zero_padded_finite_delay_sum_equals_the_truncated_past_sum
    ell N t ht (fun j=>c (-(j:ℤ))) v
  have hp := actual_zero_padded_finite_delay_sum_equals_the_truncated_past_sum
    ell N t ht (fun j=>c (j:ℤ)) w
  have hn' : (∑ j : Fin (ell+1),c (-(j.val:ℤ))*zeroPaddedDelay v t j.val)=
      ∑ i : Fin (N+1),if i.val≤t ∧ t-i.val≤ell then c ((i.val:ℤ)-(t:ℤ))*v i.val else 0 := by
    rw [hn]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs with h
    · have he : -((t-i.val:ℕ):ℤ)=(i.val:ℤ)-(t:ℤ) := by omega
      rw [he]
    · rfl
  have hp' : (∑ j : Fin (ell+1),c (j.val:ℤ)*zeroPaddedDelay w t j.val)=
      ∑ i : Fin (N+1),if i.val≤t ∧ t-i.val≤ell then c ((t:ℤ)-(i.val:ℤ))*w i.val else 0 := by
    rw [hp]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs with h
    · have he : ((t-i.val:ℕ):ℤ)=(t:ℤ)-(i.val:ℤ) := by omega
      rw [he]
    · rfl
  rw [actual_FIR_supply_is_the_two_causal_delay_sums_without_double_counting_zero,hn',hp']
  rw [mul_sub]
  simp_rw [Finset.mul_sum,mul_ite,mul_zero]
  simp only [mul_assoc]
  ring

end SafeLearning.CompleteModulesShiftedTemporalIQC31

namespace SafeLearning.CompleteModulesShiftedTemporalIQC31

theorem actual_finite_causal_window_quadratic_sum_is_the_exact_banded_toeplitz_form
    (ell N : ℕ) (c : ℤ → ℝ) (v w : ℕ → ℝ) :
    (∑ t : Fin (N+1), actualFIRWindowSupply ell c v w t.val) =
      2 * ∑ i : Fin (N+1), ∑ j : Fin (N+1),
        v i.val * CompleteModulesNNTemporalDiagonal25.prefixToeplitz
          (Finset.Icc (-(ell:ℤ)) (ell:ℤ)) c N i j * w j.val := by
  classical
  have ht : ∀ t : Fin (N+1), actualFIRWindowSupply ell c v w t.val =
      2 * ((∑ i : Fin (N+1), if i.val ≤ t.val ∧ t.val-i.val ≤ ell
          then w t.val*c ((i.val:ℤ)-(t.val:ℤ))*v i.val else 0) +
        (∑ i : Fin (N+1), if i.val ≤ t.val ∧ t.val-i.val ≤ ell
          then v t.val*c ((t.val:ℤ)-(i.val:ℤ))*w i.val else 0) -
        c 0*w t.val*v t.val) := by
    intro t
    exact actual_causal_window_supply_at_every_time_is_the_exact_two_past_columns
      ell N t.val (by omega) c v w
  have he : ∀ i j : Fin (N+1),
      v i.val * CompleteModulesNNTemporalDiagonal25.prefixToeplitz
        (Finset.Icc (-(ell:ℤ)) (ell:ℤ)) c N i j * w j.val =
      (if i.val ≤ j.val ∧ j.val-i.val ≤ ell
          then v i.val*c ((i.val:ℤ)-(j.val:ℤ))*w j.val else 0) +
      (if j.val ≤ i.val ∧ i.val-j.val ≤ ell
          then v i.val*c ((i.val:ℤ)-(j.val:ℤ))*w j.val else 0) -
      (if i=j then c 0*w i.val*v i.val else 0) := by
    intro i j
    rw [actual_finite_band_toeplitz_entries_are_the_exact_retained_lag_coefficients,
      actual_banded_prefix_coefficient_is_the_sum_of_two_past_triangles_once]
    by_cases hij : i=j
    · subst j
      simp
      ring
    · have hne : i.val ≠ j.val := by simpa only [Fin.ext_iff] using hij
      simp only [hne, hij, if_false, sub_zero, mul_add, add_mul]
      simp only [ite_mul, mul_ite, zero_mul, mul_zero, mul_assoc]
  simp_rw [ht, he]
  rw [← Finset.mul_sum]
  simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hfirst :
      (∑ t : Fin (N+1), ∑ i : Fin (N+1),
        if i.val ≤ t.val ∧ t.val-i.val ≤ ell
          then w t.val*c ((i.val:ℤ)-(t.val:ℤ))*v i.val else 0) =
      (∑ i : Fin (N+1), ∑ j : Fin (N+1),
        if i.val ≤ j.val ∧ j.val-i.val ≤ ell
          then v i.val*c ((i.val:ℤ)-(j.val:ℤ))*w j.val else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  have hdiag : (∑ i : Fin (N+1), ∑ j : Fin (N+1),
      if i=j then c 0*w i.val*v i.val else 0) =
      ∑ i : Fin (N+1), c 0*w i.val*v i.val := by simp
  rw [hfirst, hdiag]

end SafeLearning.CompleteModulesShiftedTemporalIQC31
