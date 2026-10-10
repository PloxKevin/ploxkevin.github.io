import SafeLearning.CompleteModulesTheory
import SafeLearning.CompleteModulesChords

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Set Filter Matrix
namespace SafeLearning.CompleteModulesTanhChords
open CompleteModulesTheory CompleteModulesLipSDP

theorem actual_tanh_derivative_is_one_minus_square (x : ℝ) :
    1 / (Real.cosh x) ^ 2 = 1 - (Real.tanh x) ^ 2 := by
  rw [Real.tanh_eq_sinh_div_cosh]
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  field_simp
  nlinarith [Real.cosh_sq_sub_sinh_sq x]

theorem actual_tanh_has_the_literal_strictly_positive_bounded_derivative (x : ℝ) :
    HasDerivAt Real.tanh (1 - (Real.tanh x) ^ 2) x ∧
    0 < 1 - (Real.tanh x) ^ 2 ∧ 1 - (Real.tanh x) ^ 2 ≤ 1 := by
  refine ⟨?_,by linarith [Real.tanh_sq_lt_one x],by nlinarith [sq_nonneg (Real.tanh x)]⟩
  simpa only [actual_tanh_derivative_is_one_minus_square] using tanh_derivative x

theorem actual_ordered_tanh_chord_has_a_genuine_mean_value_point
    (first second : ℝ) (h : first < second) :
    ∃ point ∈ Ioo first second,
      (Real.tanh second - Real.tanh first) / (second - first) =
        1 - (Real.tanh point) ^ 2 := by
  obtain ⟨point,hp,he⟩ := exists_hasDerivAt_eq_slope Real.tanh
    (fun x => 1 - (Real.tanh x) ^ 2) h tanh_lipschitz.continuous.continuousOn
    (fun x _ => (actual_tanh_has_the_literal_strictly_positive_bounded_derivative x).1)
  exact ⟨point,hp,he.symm⟩

theorem actual_tanh_chord_quotient_is_positive_and_at_most_one
    (first second : ℝ) (hne : first ≠ second) :
    0 < (Real.tanh first - Real.tanh second) / (first - second) ∧
    (Real.tanh first - Real.tanh second) / (first - second) ≤ 1 := by
  rcases lt_or_gt_of_ne hne with h | h
  · obtain ⟨point,hp,he⟩ := actual_ordered_tanh_chord_has_a_genuine_mean_value_point first second h
    have hs : (Real.tanh first - Real.tanh second) / (first - second) =
        (Real.tanh second - Real.tanh first) / (second - first) := by
      rw [← neg_sub (Real.tanh second) (Real.tanh first),← neg_sub second first,neg_div_neg_eq]
    rw [hs,he]
    exact (actual_tanh_has_the_literal_strictly_positive_bounded_derivative point).2
  · obtain ⟨point,hp,he⟩ := actual_ordered_tanh_chord_has_a_genuine_mean_value_point second first h
    rw [he]
    exact (actual_tanh_has_the_literal_strictly_positive_bounded_derivative point).2

theorem actual_tanh_has_no_positive_global_lower_chord_slope
    (lower : ℝ) (hlower : 0 < lower) :
    ∃ first second : ℝ, first ≠ second ∧
      (Real.tanh first - Real.tanh second) / (first - second) < lower := by
  refine ⟨2/lower,0,(div_pos (by norm_num) hlower).ne',?_⟩
  simp only [Real.tanh_zero,sub_zero]
  apply (div_lt_iff₀ (div_pos (by norm_num) hlower)).mpr
  rw [mul_div_cancel₀ 2 hlower.ne']
  exact (Real.tanh_lt_one _).trans (by norm_num)

theorem actual_tanh_derivative_has_the_literal_local_lower_bound
    (radius point : ℝ) (hp : |point| ≤ radius) :
    1 - (Real.tanh radius) ^ 2 ≤ 1 - (Real.tanh point) ^ 2 := by
  have hr : 0 ≤ radius := (abs_nonneg point).trans hp
  have hc : Real.cosh point ≤ Real.cosh radius := by
    apply Real.cosh_le_cosh.mpr
    simpa only [abs_of_nonneg hr] using hp
  rw [←actual_tanh_derivative_is_one_minus_square,
    ←actual_tanh_derivative_is_one_minus_square]
  apply one_div_le_one_div_of_le
  · positivity
  · nlinarith [Real.cosh_pos point,Real.cosh_pos radius]

theorem actual_local_tanh_chord_has_the_literal_positive_lower_and_upper_bound
    (radius first second : ℝ) (hfirst : |first| ≤ radius)
    (hsecond : |second| ≤ radius) (hne : first ≠ second) :
    0 < 1 - (Real.tanh radius) ^ 2 ∧
    1 - (Real.tanh radius) ^ 2 ≤
      (Real.tanh first - Real.tanh second) / (first - second) ∧
    (Real.tanh first - Real.tanh second) / (first - second) ≤ 1 := by
  refine ⟨(actual_tanh_has_the_literal_strictly_positive_bounded_derivative radius).2.1,
    ?_,(actual_tanh_chord_quotient_is_positive_and_at_most_one first second hne).2⟩
  rcases lt_or_gt_of_ne hne with h | h
  · obtain ⟨point,hp,he⟩ := actual_ordered_tanh_chord_has_a_genuine_mean_value_point first second h
    have hb : |point| ≤ radius := abs_le.mpr ⟨by linarith [hp.1,(abs_le.mp hfirst).1],
      by linarith [hp.2,(abs_le.mp hsecond).2]⟩
    have hs : (Real.tanh first - Real.tanh second) / (first - second) =
        (Real.tanh second - Real.tanh first) / (second - first) := by
      rw [←neg_sub (Real.tanh second) (Real.tanh first),←neg_sub second first,neg_div_neg_eq]
    rw [hs,he]
    exact actual_tanh_derivative_has_the_literal_local_lower_bound radius point hb
  · obtain ⟨point,hp,he⟩ := actual_ordered_tanh_chord_has_a_genuine_mean_value_point second first h
    have hb : |point| ≤ radius := abs_le.mpr ⟨by linarith [hp.1,(abs_le.mp hsecond).1],
      by linarith [hp.2,(abs_le.mp hfirst).2]⟩
    rw [he]
    exact actual_tanh_derivative_has_the_literal_local_lower_bound radius point hb

theorem actual_origin_secant_lower_sector_is_at_least_the_local_derivative_bound
    (radius : ℝ) (hr : 0 < radius) :
    1 - (Real.tanh radius) ^ 2 ≤ Real.tanh radius / radius := by
  have h := actual_local_tanh_chord_has_the_literal_positive_lower_and_upper_bound
    radius radius 0 (by rw [abs_of_pos hr]) (by simpa using hr.le) hr.ne'
  simpa only [Real.tanh_zero,sub_zero] using h.2.1

theorem actual_positive_radius_origin_secant_has_a_mean_value_point
    (radius : ℝ) (hr : 0 < radius) :
    ∃ point ∈ Ioo 0 radius, Real.tanh radius / radius =
      1 - (Real.tanh point) ^ 2 := by
  simpa only [Real.tanh_zero,sub_zero] using
    actual_ordered_tanh_chord_has_a_genuine_mean_value_point 0 radius hr

def actualSourceTanhQCMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![0,1;1,-2]

theorem actual_source_incremental_tanh_qc_has_the_literal_matrix_identity
    (deltaInput deltaOutput : ℝ) :
    quadratic actualSourceTanhQCMatrix ![deltaInput,deltaOutput] =
      2*deltaInput*deltaOutput - 2*deltaOutput^2 := by
  norm_num [quadratic,actualSourceTanhQCMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  ring

theorem actual_source_incremental_tanh_qc_is_nonnegative (first second : ℝ) :
    0 ≤ quadratic actualSourceTanhQCMatrix
      ![first-second,Real.tanh first-Real.tanh second] := by
  rw [actual_source_incremental_tanh_qc_has_the_literal_matrix_identity]
  nlinarith [tanh_incremental_sector first second]

theorem actual_tanh_literal_origin_sector_bounds (point : ℝ) :
    0 ≤ point*Real.tanh point ∧ point*Real.tanh point ≤ point^2 := by
  have h := tanh_global_sector point
  have hs := sq_nonneg (point-Real.tanh point)
  have hm := sq_nonneg (Real.tanh point)
  constructor <;> nlinarith

end SafeLearning.CompleteModulesTanhChords
