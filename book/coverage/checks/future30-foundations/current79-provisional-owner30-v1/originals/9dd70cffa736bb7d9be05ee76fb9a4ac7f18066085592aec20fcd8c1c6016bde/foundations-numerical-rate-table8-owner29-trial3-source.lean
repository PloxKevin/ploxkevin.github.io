import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace SafeLearning.CompleteFoundationsNumericalRateTable30
open scoped Topology

theorem actual_all_five_printed_square_root_entries_are_exact :
    Real.sqrt (100:ℝ)=10 ∧ Real.sqrt (10000:ℝ)=100 ∧
    Real.sqrt (1000000:ℝ)=1000 ∧ Real.sqrt (100000000:ℝ)=10000 ∧
    Real.sqrt (10000000000:ℝ)=100000 := by norm_num

theorem actual_positive_two_thirds_power_has_exact_cube (T : ℝ) (hT : 0<T) :
    (Real.rpow T (2/3))^3=T^2 := by
  simp only [Real.rpow_eq_pow]
  rw [←Real.rpow_natCast,←Real.rpow_mul hT.le]
  norm_num [Real.rpow_natCast]

theorem actual_two_thirds_decimal_rounding_from_exact_cube (T M r : ℝ)
    (hT : 0<T) (hr : 0<r) (hL : 0≤M-r) (hLC : (M-r)^3<T^2) (hUC : T^2<(M+r)^3) :
    |Real.rpow T (2/3)-M|<r := by
  have hx : 0≤Real.rpow T (2/3) := (Real.rpow_pos_of_pos hT _).le
  have hc := actual_positive_two_thirds_power_has_exact_cube T hT
  have hl : M-r<Real.rpow T (2/3) := by
    by_contra h
    have hp := pow_le_pow_left₀ hx (le_of_not_gt h) 3
    rw [hc] at hp
    exact (not_le.mpr hLC) hp
  have hu : Real.rpow T (2/3)<M+r := by
    by_contra h
    have hU : 0≤M+r := by linarith
    have hp := pow_le_pow_left₀ hU (le_of_not_gt h) 3
    rw [hc] at hp
    exact (not_le.mpr hUC) hp
  exact abs_lt.mpr ⟨by linarith,by linarith⟩

theorem actual_all_five_two_thirds_entries_exact_or_rounded :
    |Real.rpow (100:ℝ) (2/3)-21.5|<0.05 ∧
    |Real.rpow (10000:ℝ) (2/3)-464|<0.5 ∧
    Real.rpow (1000000:ℝ) (2/3)=10000 ∧
    |Real.rpow (100000000:ℝ) (2/3)-215000|<500 ∧
    |Real.rpow (10000000000:ℝ) (2/3)-4640000|<5000 := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · apply actual_two_thirds_decimal_rounding_from_exact_cube <;> norm_num
  · apply actual_two_thirds_decimal_rounding_from_exact_cube <;> norm_num
  · apply (pow_left_inj₀ (Real.rpow_nonneg (by norm_num) _)
      (by norm_num : (0:ℝ)≤10000) (by decide : (3:ℕ)≠0)).mp
    have hc := actual_positive_two_thirds_power_has_exact_cube (1000000:ℝ) (by norm_num)
    norm_num only [Real.rpow_eq_pow] at hc ⊢
  · apply actual_two_thirds_decimal_rounding_from_exact_cube <;> norm_num
  · apply actual_two_thirds_decimal_rounding_from_exact_cube <;> norm_num

theorem actual_four_rounded_two_thirds_entries_are_not_exact :
    Real.rpow (100:ℝ) (2/3)≠21.5 ∧ Real.rpow (10000:ℝ) (2/3)≠464 ∧
    Real.rpow (100000000:ℝ) (2/3)≠215000 ∧
    Real.rpow (10000000000:ℝ) (2/3)≠4640000 := by
  refine ⟨?_,?_,?_,?_⟩
  all_goals
    intro he
    have hc := congrArg (fun x : ℝ=>x^3) he
    rw [actual_positive_two_thirds_power_has_exact_cube _ (by norm_num)] at hc
    norm_num at hc

theorem actual_log_even_budget_power_has_rational_enclosure (k : ℕ) (hk : 0<k) :
    (2*(k:ℝ))*2.3025850926<Real.log ((10:ℝ)^(2*k)) ∧
    Real.log ((10:ℝ)^(2*k))<(2*(k:ℝ))*2.3025850934 := by
  rw [Real.log_pow,Real.log_ten_eq]
  push_cast
  have hl : 2.3025850926<Real.log 2+Real.log 5 := by
    linarith [Real.log_two_gt_d9,Real.log_five_gt_d9]
  have hu : Real.log 2+Real.log 5<2.3025850934 := by
    linarith [Real.log_two_lt_d9,Real.log_five_lt_d9]
  have hp : (0:ℝ)<2*k := by exact_mod_cast (by omega : 0<2*k)
  exact ⟨mul_lt_mul_of_pos_left hl hp,mul_lt_mul_of_pos_left hu hp⟩

private theorem actual_log_cube_enclosure (k : ℕ) (hk : 0<k) :
    ((2*(k:ℝ))*2.3025850926)^3<(Real.log ((10:ℝ)^(2*k)))^3 ∧
    (Real.log ((10:ℝ)^(2*k)))^3<((2*(k:ℝ))*2.3025850934)^3 := by
  have h := actual_log_even_budget_power_has_rational_enclosure k hk
  have hL : 0≤(2*(k:ℝ))*2.3025850926 := by positivity
  exact ⟨pow_lt_pow_left₀ h.1 hL (by decide),
    pow_lt_pow_left₀ h.2 (hL.trans h.1.le) (by decide)⟩

theorem actual_all_five_log_cube_entries_are_rounded_at_printed_precision :
    |(Real.log (100:ℝ))^3-97.7|<0.05 ∧
    |(Real.log (10000:ℝ))^3-781|<0.5 ∧
    |(Real.log (1000000:ℝ))^3-2637|<0.5 ∧
    |(Real.log (100000000:ℝ))^3-6251|<0.5 ∧
    |(Real.log (10000000000:ℝ))^3-12208|<0.5 := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · have h := actual_log_cube_enclosure 1 (by decide)
    norm_num at h
    exact abs_lt.mpr ⟨by linarith [h.1],by linarith [h.2]⟩
  · have h := actual_log_cube_enclosure 2 (by decide)
    norm_num at h
    exact abs_lt.mpr ⟨by linarith [h.1],by linarith [h.2]⟩
  · have h := actual_log_cube_enclosure 3 (by decide)
    norm_num at h
    exact abs_lt.mpr ⟨by linarith [h.1],by linarith [h.2]⟩
  · have h := actual_log_cube_enclosure 4 (by decide)
    norm_num at h
    exact abs_lt.mpr ⟨by linarith [h.1],by linarith [h.2]⟩
  · have h := actual_log_cube_enclosure 5 (by decide)
    norm_num at h
    exact abs_lt.mpr ⟨by linarith [h.1],by linarith [h.2]⟩

theorem actual_all_five_rounded_log_cube_entries_are_not_exact :
    (Real.log (100:ℝ))^3≠97.7 ∧ (Real.log (10000:ℝ))^3≠781 ∧
    (Real.log (1000000:ℝ))^3≠2637 ∧ (Real.log (100000000:ℝ))^3≠6251 ∧
    (Real.log (10000000000:ℝ))^3≠12208 := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · have h := (actual_log_cube_enclosure 1 (by decide)).2
    norm_num at h
    exact ne_of_lt (lt_of_lt_of_le h (by norm_num))
  · have h := (actual_log_cube_enclosure 2 (by decide)).1
    norm_num at h
    exact ne_of_gt (lt_of_le_of_lt (by norm_num) h)
  · have h := (actual_log_cube_enclosure 3 (by decide)).2
    norm_num at h
    exact ne_of_lt (lt_of_lt_of_le h (by norm_num))
  · have h := (actual_log_cube_enclosure 4 (by decide)).2
    norm_num at h
    exact ne_of_lt (lt_of_lt_of_le h (by norm_num))
  · have h := (actual_log_cube_enclosure 5 (by decide)).1
    norm_num at h
    exact ne_of_gt (lt_of_le_of_lt (by norm_num) h)
end SafeLearning.CompleteFoundationsNumericalRateTable30
