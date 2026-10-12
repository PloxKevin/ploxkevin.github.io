import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace SafeLearning.CompleteDualPIHalfEnvelope

/-- Fractional nominal half-time of the geometric envelope, rather than an integer index. -/
def nominalHalfTime (radius : ℝ) : ℝ := Real.log 2/Real.log (1/radius)

theorem actual_geometric_envelope_half_time (radius : ℝ) (h0 : 0<radius) (h1 : radius<1) :
    0<nominalHalfTime radius ∧ Real.rpow radius (nominalHalfTime radius)=1/2 := by
  have hl : Real.log radius<0 := Real.log_neg h0 h1
  have hd : Real.log (1/radius)= -Real.log radius := by rw [one_div,Real.log_inv]
  constructor
  · unfold nominalHalfTime
    rw [hd]
    exact div_pos (Real.log_pos (by norm_num)) (by linarith)
  · rw [Real.rpow_eq_pow,Real.rpow_def_of_pos h0]
    unfold nominalHalfTime
    rw [hd]
    have he : Real.log radius*(Real.log 2/(-Real.log radius))= -Real.log 2 := by
      field_simp [hl.ne]
    rw [he,Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<2)]
    norm_num

theorem actual_source_first_integer_half_iteration :
    ∀ n : ℕ,(Real.sqrt (4/5:ℝ))^n≤1/2 ↔ 7≤n := by
  let radius : ℝ := Real.sqrt (4/5:ℝ)
  have hr0 : 0<radius := Real.sqrt_pos.mpr (by norm_num)
  have hr1 : radius<1 := (Real.sqrt_lt (by norm_num : (0:ℝ)≤4/5)
    (by norm_num : (0:ℝ)≤1)).mpr (by norm_num)
  have hs : radius^2=(4/5:ℝ) := Real.sq_sqrt (by norm_num)
  have h6 : radius^6=(64/125:ℝ) := by
    rw [show (6:ℕ)=2*3 by norm_num,pow_mul,hs]
    norm_num
  have h9 : radius<(9/10:ℝ) := by
    nlinarith [hr0]
  have h7 : radius^7<(1/2:ℝ) := by
    rw [show (7:ℕ)=6+1 by norm_num,pow_succ,h6]
    nlinarith
  intro n
  change radius^n≤1/2 ↔ 7≤n
  constructor
  · intro hn
    by_contra h
    have hn6 : n≤6 := by omega
    have hp := pow_le_pow_of_le_one hr0.le hr1.le hn6
    rw [h6] at hp
    linarith
  · intro hn
    exact (pow_le_pow_of_le_one hr0.le hr1.le hn).trans h7.le

theorem every_complex_geometric_mode_has_the_exact_source_envelope
    (z : ℂ) (radius : ℝ) (hmod : ‖z‖=radius) (n : ℕ) : ‖z^n‖=radius^n := by
  rw [norm_pow,hmod]

end SafeLearning.CompleteDualPIHalfEnvelope
