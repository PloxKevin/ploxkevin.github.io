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
