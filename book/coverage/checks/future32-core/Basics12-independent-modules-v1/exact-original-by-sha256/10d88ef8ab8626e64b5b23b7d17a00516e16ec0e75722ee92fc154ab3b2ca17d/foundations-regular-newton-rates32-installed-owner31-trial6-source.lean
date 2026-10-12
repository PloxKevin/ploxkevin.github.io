import Mathlib
import SafeLearning.CompleteFoundationsConvergenceRates
import SafeLearning.CompleteFoundationsConvergenceRateExamples
import SafeLearning.CompleteFoundationsNewtonRates

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Asymptotics
open scoped Topology NNReal

namespace SafeLearning.CompleteFoundationsRegularNewtonAndRateInterpretation31

open SafeLearning.CompleteFoundationsNewtonRates

theorem actual_derivative_lipschitz_control_gives_the_newton_quadratic_error
    (f : ℝ → ℝ) (root x lower : ℝ) (L : ℝ≥0)
    (hf : ∀ y ∈ uIcc x root, DifferentiableAt ℝ f y)
    (hroot : f root = 0) (hlower : 0 < lower)
    (hderiv : lower ≤ |deriv f x|)
    (hlip : LipschitzOnWith L (deriv f) (uIcc x root)) :
    |newtonStep f x - root| ≤ (L : ℝ) / lower * |x - root| ^ 2 := by
  have hx : x ∈ uIcc x root := left_mem_uIcc
  have hr : root ∈ uIcc x root := right_mem_uIcc
  have hd : deriv f x ≠ 0 := by
    intro h
    simp [h] at hderiv
    linarith
  let residual : ℝ → ℝ := fun y => f y - f x - deriv f x * (y - x)
  have hres : ∀ y ∈ uIcc x root,
      HasDerivWithinAt residual (deriv f y - deriv f x) (uIcc x root) y := by
    intro y hy
    convert! (((hf y hy).hasDerivAt.sub_const (f x)).sub
      (((hasDerivAt_id y).sub_const x).const_smul (deriv f x))).hasDerivWithinAt
        (s := uIcc x root) using 1 <;> simp [residual, Pi.sub_apply, id_eq, smul_eq_mul]
  have hbound : ∀ y ∈ uIcc x root,
      ‖deriv f y - deriv f x‖ ≤ (L : ℝ) * |root - x| := by
    intro y hy
    have h := hlip.dist_le_mul y hy x hx
    have hybound : |y - x| ≤ |root - x| := by
      rcases le_total x root with hxr | hrx
      · rw [uIcc_of_le hxr] at hy
        rw [abs_of_nonneg (sub_nonneg.mpr hy.1), abs_of_nonneg (sub_nonneg.mpr hxr)]
        linarith [hy.2]
      · rw [uIcc_of_ge hrx] at hy
        rw [abs_of_nonpos (sub_nonpos.mpr hy.2), abs_of_nonpos (sub_nonpos.mpr hrx)]
        linarith [hy.1]
    simpa only [Real.dist_eq, Real.norm_eq_abs] using h.trans
      (mul_le_mul_of_nonneg_left hybound L.coe_nonneg)
  have hrem := (convex_uIcc x root).norm_image_sub_le_of_norm_hasDerivWithin_le
    hres hbound hx hr
  have herr : newtonStep f x - root = residual root / deriv f x := by
    dsimp [newtonStep, residual]
    rw [hroot]
    field_simp
    ring
  have hrem' : |residual root| ≤ (L : ℝ) * |x - root| ^ 2 := by
    simpa [residual, Real.norm_eq_abs, abs_sub_comm, pow_two, mul_assoc] using hrem
  rw [herr, abs_div]
  calc
    |residual root| / |deriv f x| ≤ ((L : ℝ) * |x - root| ^ 2) / |deriv f x| :=
      div_le_div_of_nonneg_right hrem' (abs_nonneg _)
    _ ≤ ((L : ℝ) * |x - root| ^ 2) / lower :=
      div_le_div_of_nonneg_left (by positivity) hlower hderiv
    _ = (L : ℝ) / lower * |x - root| ^ 2 := by ring

theorem actual_C2_and_a_nonzero_root_derivative_supply_a_local_quadratic_bound
    (f : ℝ → ℝ) (root : ℝ) (hf : ContDiff ℝ 2 f)
    (hroot : f root = 0) (hregular : deriv f root ≠ 0) :
    ∃ radius coefficient : ℝ, 0 < radius ∧ 0 < coefficient ∧
      ∀ x, |x - root| ≤ radius →
        deriv f x ≠ 0 ∧
        |newtonStep f x - root| ≤ coefficient * |x - root| ^ 2 := by
  have hdf : Continuous (deriv f) := hf.continuous_deriv (by norm_num)
  have hd2 : Continuous (deriv (deriv f)) :=
    (hf.deriv' : ContDiff ℝ 1 (deriv f)).continuous_deriv (by norm_num)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hd2.continuousOn : ContinuousOn (deriv (deriv f)) (Icc (root - 1) (root + 1)))
  let L : ℝ≥0 := ⟨max M 1, le_trans (by norm_num) (le_max_right M 1)⟩
  have hL : 0 < (L : ℝ) := lt_of_lt_of_le (by norm_num) (le_max_right M 1)
  have hlip : LipschitzOnWith L (deriv f) (Icc (root - 1) (root + 1)) := by
    apply (convex_Icc _ _).lipschitzOnWith_of_nnnorm_deriv_le
      (fun y _ => hf.differentiable_deriv_two y)
    intro y hy
    have hh : ‖deriv (deriv f) y‖ ≤ (L : ℝ) := (hM y hy).trans (le_max_left M 1)
    exact_mod_cast hh
  have hm : 0 < |deriv f root| / 2 := by positivity
  obtain ⟨delta, hdelta, hnear⟩ := Metric.continuousAt_iff.mp hdf.continuousAt
    (|deriv f root| / 2) hm
  let radius : ℝ := min 1 (delta / 2)
  refine ⟨radius, (L : ℝ) / (|deriv f root| / 2),
    lt_min (by norm_num) (by positivity), div_pos hL hm, ?_⟩
  intro x hx
  have hx1 : |x - root| ≤ 1 := hx.trans (min_le_left _ _)
  have hxd : |x - root| < delta := lt_of_le_of_lt
    (hx.trans (min_le_right _ _)) (by linarith)
  have hdnear : |deriv f x - deriv f root| < |deriv f root| / 2 := by
    simpa only [Real.dist_eq] using hnear (by simpa only [Real.dist_eq] using hxd)
  have habs : |deriv f root| ≤ |deriv f x - deriv f root| + |deriv f x| := by
    simpa [sub_add_cancel, abs_sub_comm] using
      (abs_add_le (deriv f root - deriv f x) (deriv f x))
  have hlower : |deriv f root| / 2 ≤ |deriv f x| := by linarith
  have hdx : deriv f x ≠ 0 := by
    intro h
    simp [h] at hlower
    linarith
  have hsub : uIcc x root ⊆ Icc (root - 1) (root + 1) := by
    intro y hy
    have xx := abs_le.mp hx1
    rcases le_total x root with hxr | hrx
    · rw [uIcc_of_le hxr] at hy
      constructor <;> linarith [hy.1, hy.2]
    · rw [uIcc_of_ge hrx] at hy
      constructor <;> linarith [hy.1, hy.2]
  exact ⟨hdx, actual_derivative_lipschitz_control_gives_the_newton_quadratic_error
    f root x (|deriv f root| / 2) L (fun y _ => hf.differentiable (by norm_num) y)
    hroot hm hlower (hlip.mono hsub)⟩

theorem actual_exact_positive_geometric_errors_have_an_affine_logarithmic_plot
    (q initial : ℝ) (hq : 0 < q) (hi : 0 < initial) (n : ℕ) :
    Real.log (q ^ n * initial) = (n : ℝ) * Real.log q + Real.log initial := by
  rw [Real.log_mul (pow_ne_zero n hq.ne') hi.ne', Real.log_pow]

theorem actual_positive_reciprocal_power_logarithmic_slope_flattens
    (power : ℝ) (hp : 0 < power) :
    Tendsto (fun x : ℝ => deriv (fun t : ℝ => Real.log (t ^ (-power))) x)
      atTop (𝓝 0) := by
  have eq : ∀ᶠ x : ℝ in atTop,
      deriv (fun t : ℝ => Real.log (t ^ (-power))) x = -power / x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have h := ((hasDerivAt_id x).rpow_const (Or.inl hx.ne')).log
      (Real.rpow_pos_of_pos hx (-power)).ne'
    rw [show deriv (fun t : ℝ => Real.log (t ^ (-power))) x =
      (1 * -power * x ^ (-power - 1)) / x ^ (-power) from by simpa only [id_eq] using h.deriv]
    rw [Real.rpow_sub hx, Real.rpow_one]
    field_simp [hx.ne', (Real.rpow_pos_of_pos hx (-power)).ne']
  have hlim : Tendsto (fun x : ℝ => -power / x) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using tendsto_inv_atTop_zero.const_mul (-power)
  apply hlim.congr'
  filter_upwards [eq] with x hx
  exact hx.symm

theorem actual_geometric_tolerance_formula_is_a_sufficient_certificate_for_bounded_errors
    (error : ℕ → ℝ) (q initial epsilon : ℝ) (n : ℕ)
    (hq0 : 0 < q) (hq1 : q < 1) (hi : 0 < initial) (he : 0 < epsilon)
    (hbound : error n ≤ q ^ n * initial)
    (hindex : Real.log (initial / epsilon) / Real.log (1 / q) ≤ (n : ℝ)) :
    error n ≤ epsilon :=
  hbound.trans ((SafeLearning.CompleteFoundationsConvergenceRates.actual_positive_geometric_certificate_is_equivalent_to_the_printed_logarithmic_cutoff
      q initial epsilon n hq0 hq1 hi he).mpr hindex)

theorem actual_faster_errors_do_not_need_the_geometric_envelope_first_index :
    (∀ n : ℕ, (if n = 0 then (1 : ℝ) else 0) ≤ (1 / 2 : ℝ) ^ n) ∧
      (if (1 : ℕ) = 0 then (1 : ℝ) else 0) ≤ 1 / 1000000 ∧
      ¬ ((1 / 2 : ℝ) ^ 1 ≤ 1 / 1000000) := by
  refine ⟨?_, by norm_num, by norm_num⟩
  intro n
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn]

theorem actual_polynomial_upper_bound_alone_does_not_classify_an_error_as_sublinear :
    (∀ n : ℕ, (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹) ∧
      ((fun _ : ℕ => (0 : ℝ)) =O[atTop] (fun n : ℕ => (1 / 2 : ℝ) ^ n)) := by
  exact ⟨fun n => inv_nonneg.mpr (by positivity), isBigO_zero _ _⟩



theorem actual_C2_regular_newton_has_an_invariant_quadratic_neighborhood_and_converges
    (f : ℝ → ℝ) (root : ℝ) (hf : ContDiff ℝ 2 f)
    (hroot : f root = 0) (hregular : deriv f root ≠ 0) :
    ∃ radius coefficient : ℝ, 0 < radius ∧ 0 < coefficient ∧
      ∀ initial, |initial - root| ≤ radius →
        (∀ n : ℕ, |(newtonStep f)^[n] initial - root| ≤ radius) ∧
        (∀ n : ℕ, deriv f ((newtonStep f)^[n] initial) ≠ 0 ∧
          |(newtonStep f)^[n + 1] initial - root| ≤
            coefficient * |(newtonStep f)^[n] initial - root| ^ 2) ∧
        Tendsto (fun n : ℕ => (newtonStep f)^[n] initial) atTop (𝓝 root) := by
  obtain ⟨R, C, hR, hC, hlocal⟩ :=
    actual_C2_and_a_nonzero_root_derivative_supply_a_local_quadratic_bound
      f root hf hroot hregular
  let radius : ℝ := min R ((1 / 2) / C)
  have hr : 0 < radius := lt_min hR (div_pos (by norm_num) hC)
  have hrR : radius ≤ R := min_le_left _ _
  have hCr : C * radius ≤ 1 / 2 := by
    have h := (le_div_iff₀ hC).mp (min_le_right R ((1 / 2) / C))
    simpa only [mul_comm] using h
  refine ⟨radius, C, hr, hC, ?_⟩
  intro initial hi
  have hcontract : ∀ x, |x - root| ≤ radius →
      |newtonStep f x - root| ≤ (1 / 2) * |x - root| := by
    intro x hx
    have hq := (hlocal x (hx.trans hrR)).2
    have hc : C * |x - root| ≤ 1 / 2 :=
      (mul_le_mul_of_nonneg_left hx hC.le).trans hCr
    have hmul := mul_le_mul_of_nonneg_right hc (abs_nonneg (x - root))
    nlinarith
  have hstay : ∀ n : ℕ, |(newtonStep f)^[n] initial - root| ≤ radius := by
    intro n
    induction n with
    | zero => simpa using hi
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      have hc := hcontract ((newtonStep f)^[n] initial) ih
      nlinarith [abs_nonneg ((newtonStep f)^[n] initial - root)]
  refine ⟨hstay, ?_, ?_⟩
  · intro n
    simpa only [Function.iterate_succ_apply'] using
      hlocal ((newtonStep f)^[n] initial) ((hstay n).trans hrR)
  · apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [Real.norm_eq_abs]
    apply SafeLearning.CompleteFoundationsConvergenceRates.actual_nonnegative_geometrically_bounded_errors_converge_to_zero
        (fun n : ℕ => |(newtonStep f)^[n] initial - root|) (1 / 2)
        (by norm_num) (by norm_num) (fun n => abs_nonneg _)
    intro n
    simpa only [Function.iterate_succ_apply'] using
      hcontract ((newtonStep f)^[n] initial) (hstay n)



theorem actual_geometric_cutoff_has_the_precise_logarithmic_growth_constant
    (q initial : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (hi : 0 < initial) :
    Tendsto (fun t : ℝ =>
      (Real.log (initial * t) / Real.log (1 / q)) / Real.log t)
      atTop (𝓝 (1 / Real.log (1 / q))) := by
  have hlog : 0 < Real.log (1 / q) := by
    rw [one_div, Real.log_inv]
    exact neg_pos.mpr (Real.log_neg hq0 hq1)
  have ht : Tendsto (fun t : ℝ => Real.log initial / Real.log t) atTop (𝓝 0) :=
    Real.isLittleO_const_log_atTop.tendsto_div_nhds_zero
  have hlim : Tendsto (fun t : ℝ =>
      (Real.log initial / Real.log t + 1) / Real.log (1 / q))
      atTop (𝓝 (1 / Real.log (1 / q))) := by
    simpa using (ht.add_const 1).div_const (Real.log (1 / q))
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  have hp : 0 < t := lt_trans (by norm_num) ht
  have hlt : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  rw [Real.log_mul hi.ne' hp.ne']
  field_simp [hlt, hlog.ne']

theorem actual_positive_tolerance_cutoff_is_asymptotically_log_one_over_tolerance
    (q initial : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (hi : 0 < initial) :
    Tendsto (fun epsilon : ℝ =>
      (Real.log (initial / epsilon) / Real.log (1 / q)) / Real.log (1 / epsilon))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / Real.log (1 / q))) := by
  simpa only [Function.comp_def, one_div, div_eq_mul_inv, one_mul] using
    (actual_geometric_cutoff_has_the_precise_logarithmic_growth_constant
      q initial hq0 hq1 hi).comp tendsto_inv_nhdsGT_zero

end SafeLearning.CompleteFoundationsRegularNewtonAndRateInterpretation31

namespace SafeLearning.CompleteFoundationsRegularNewtonAndRateInterpretation31

theorem actual_positive_scaled_reciprocal_errors_converge_and_have_no_geometric_big_o_bound
    (coefficient power q : ℝ) (hc : 0 < coefficient) (hp : 0 < power)
    (hq0 : 0 < q) (hq1 : q < 1) :
    Tendsto (fun n : ℕ => coefficient * (n : ℝ) ^ (-power)) atTop (𝓝 0) ∧
      ¬ ((fun n : ℕ => coefficient * (n : ℝ) ^ (-power)) =O[atTop]
        (fun n : ℕ => q ^ n)) := by
  constructor
  · simpa using (SafeLearning.CompleteFoundationsConvergenceRateExamples.actual_polynomial_reciprocal_errors_converge_to_zero power hp).const_mul coefficient
  · rw [isBigO_const_mul_left_iff hc.ne']
    exact SafeLearning.CompleteFoundationsConvergenceRateExamples.actual_polynomial_reciprocal_errors_have_no_geometric_big_o_bound q power hq0 hq1

theorem actual_positive_scaled_power_curve_has_the_true_flattening_logarithmic_slope
    (coefficient power : ℝ) (hc : 0 < coefficient) (hp : 0 < power) :
    Tendsto (fun x : ℝ => deriv (fun t : ℝ => Real.log (coefficient * t ^ (-power))) x)
      atTop (𝓝 0) := by
  have eq : ∀ᶠ x : ℝ in atTop,
      deriv (fun t : ℝ => Real.log (coefficient * t ^ (-power))) x = -power / x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have h := (((hasDerivAt_id x).rpow_const (Or.inl hx.ne')).const_mul coefficient).log
      (mul_pos hc (Real.rpow_pos_of_pos hx (-power))).ne'
    rw [show deriv (fun t : ℝ => Real.log (coefficient * t ^ (-power))) x =
      (coefficient * (1 * -power * x ^ (-power - 1))) / (coefficient * x ^ (-power)) from by
        simpa only [id_eq] using h.deriv]
    rw [Real.rpow_sub hx, Real.rpow_one]
    field_simp [hc.ne', hx.ne', (Real.rpow_pos_of_pos hx (-power)).ne']
  have hlim : Tendsto (fun x : ℝ => -power / x) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using tendsto_inv_atTop_zero.const_mul (-power)
  apply hlim.congr'
  filter_upwards [eq] with x hx
  exact hx.symm

end SafeLearning.CompleteFoundationsRegularNewtonAndRateInterpretation31
