import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory Function
open scoped Topology NNReal Nat

namespace SafeLearning.CompleteAppliedGlobalLipschitzPicard

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {lower upper : ℝ} (origin : Icc lower upper)

def extendPath (path : C(Icc lower upper, E)) (time : ℝ) : E :=
  path (projIcc lower upper (origin.2.1.trans origin.2.2) time)

@[simp] theorem extendPath_of_mem (path : C(Icc lower upper, E))
    (time : ℝ) (ht : time ∈ Icc lower upper) :
    extendPath origin path time = path ⟨time, ht⟩ := by
  unfold extendPath
  rw [projIcc_of_mem _ ht]

@[fun_prop] theorem extendPath_continuous (path : C(Icc lower upper, E)) :
    Continuous (extendPath origin path) :=
  path.continuous.comp continuous_projIcc

def next (field : E → E) (initial : E) (K : ℝ≥0) (hfield : LipschitzWith K field)
    (path : C(Icc lower upper, E)) : C(Icc lower upper, E) where
  toFun time := initial + ∫ t in origin.1..time.1, field (extendPath origin path t)
  continuous_toFun := by
    have hc : Continuous (fun t => field (extendPath origin path t)) :=
      hfield.continuous.comp (extendPath_continuous origin path)
    exact continuous_const.add
      ((intervalIntegral.continuous_primitive (fun a b => hc.intervalIntegrable a b) origin.1).comp
        continuous_subtype_val)

theorem actual_picard_iterate_pointwise_difference_bound
    (field : E → E) (initial : E) (K : ℝ≥0) (hfield : LipschitzWith K field)
    (path other : C(Icc lower upper, E)) (n : ℕ) (time : Icc lower upper) :
    dist ((next origin field initial K hfield)^[n] path time)
      ((next origin field initial K hfield)^[n] other time) ≤
      (K * |time.1 - origin.1|) ^ n / n ! * dist path other := by
  induction n generalizing time with
  | zero => simpa using ContinuousMap.dist_apply_le_dist (f := path) (g := other) time
  | succ n ih =>
    let f := next origin field initial K hfield
    have hc (path : C(Icc lower upper, E)) :
        Continuous (fun t => field (extendPath origin path t)) :=
      hfield.continuous.comp (extendPath_continuous origin path)
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', dist_eq_norm]
    change ‖(initial + ∫ t in origin.1..time.1, field (extendPath origin (f^[n] path) t)) -
      (initial + ∫ t in origin.1..time.1, field (extendPath origin (f^[n] other) t))‖ ≤ _
    rw [add_sub_add_left_eq_sub,
      ← intervalIntegral.integral_sub ((hc _).intervalIntegrable _ _) ((hc _).intervalIntegrable _ _)]
    calc
      _ ≤ ∫ t in uIoc origin.1 time.1,
          K ^ (n + 1) * |t - origin.1| ^ n / n ! * dist path other := by
        rw [intervalIntegral.norm_intervalIntegral_eq]
        apply norm_integral_le_of_norm_le (Continuous.integrableOn_uIoc (by fun_prop))
        apply ae_restrict_mem measurableSet_Ioc |>.mono
        intro t ht
        have ht' : t ∈ Icc lower upper :=
          (uIoc_subset_uIcc.trans (uIcc_subset_Icc origin.2 time.2)) ht
        rw [← dist_eq_norm, extendPath_of_mem origin _ t ht', extendPath_of_mem origin _ t ht']
        calc
          _ ≤ K * dist (f^[n] path ⟨t, ht'⟩) (f^[n] other ⟨t, ht'⟩) :=
            hfield.dist_le_mul _ _
          _ ≤ K ^ (n + 1) * |t - origin.1| ^ n / n ! * dist path other := by
            rw [pow_succ', mul_assoc, mul_div_assoc, mul_assoc]
            gcongr
            simpa only [← mul_pow] using ih ⟨t, ht'⟩
      _ ≤ (K * |time.1 - origin.1|) ^ (n + 1) / (n + 1) ! * dist path other := by
        apply le_of_abs_le
        rw [← intervalIntegral.abs_intervalIntegral_eq, intervalIntegral.integral_mul_const,
          intervalIntegral.integral_div, intervalIntegral.integral_const_mul, abs_mul, abs_div,
          abs_mul, intervalIntegral.abs_intervalIntegral_eq, integral_pow_abs_sub_uIoc, abs_div,
          abs_pow, abs_pow, abs_dist, NNReal.abs_eq, abs_abs, mul_div, div_div, ← abs_mul,
          ← Nat.cast_succ, ← Nat.cast_mul, ← Nat.factorial_succ, Nat.abs_cast, ← mul_pow]

theorem actual_picard_has_an_actual_fixed_point_on_any_finite_interval
    (field : E → E) (initial : E) (K : ℝ≥0) (hfield : LipschitzWith K field) :
    ∃ path : C(Icc lower upper, E), IsFixedPt (next origin field initial K hfield) path := by
  let duration : ℝ := max (upper - origin.1) (origin.1 - lower)
  have hd : 0 ≤ duration := le_max_of_le_left (sub_nonneg.mpr origin.2.2)
  obtain ⟨n, hn⟩ := FloorSemiring.tendsto_pow_div_factorial_atTop ((K : ℝ) * duration)
    |>.eventually (gt_mem_nhds zero_lt_one) |>.exists
  have hn0 : 0 ≤ ((K : ℝ) * duration) ^ n / n ! := by positivity
  let bound : ℝ≥0 := ⟨_, hn0⟩
  have hcontract : ContractingWith bound (next origin field initial K hfield)^[n] := by
    refine ⟨hn, LipschitzWith.of_dist_le_mul (fun path other => ?_)⟩
    apply (ContinuousMap.dist_le (by positivity)).mpr
    intro time
    apply (actual_picard_iterate_pointwise_difference_bound origin field initial K hfield
        path other n time).trans
    change (K * |time.1 - origin.1|) ^ n / n ! * dist path other ≤
      ((K : ℝ) * duration) ^ n / n ! * dist path other
    dsimp only [duration]
    gcongr
    exact abs_sub_le_max_sub time.2.1 time.2.2 origin.1
  exact ⟨_, hcontract.isFixedPt_fixedPoint_iterate⟩

theorem actual_globally_lipschitz_field_has_a_genuine_finite_interval_integral_solution
    (field : E → E) (initial : E) (K : ℝ≥0) (hfield : LipschitzWith K field) :
    ∃ path : ℝ → E, Continuous path ∧ path origin.1 = initial ∧
      (∀ time ∈ Icc lower upper,
        path time = initial + ∫ t in origin.1..time, field (path t)) ∧
      ∀ time ∈ Ioo lower upper, HasDerivAt path (field (path time)) time := by
  obtain ⟨path, hfixed⟩ := actual_picard_has_an_actual_fixed_point_on_any_finite_interval
    origin field initial K hfield
  let extension := extendPath origin path
  have hEq : ∀ time ∈ Icc lower upper,
      extension time = initial + ∫ t in origin.1..time, field (extension t) := by
    intro time ht
    have h := congrArg (fun path : C(Icc lower upper, E) => path ⟨time, ht⟩) hfixed
    change extendPath origin path time = _
    rw [extendPath_of_mem origin path time ht]
    simpa only [next, ContinuousMap.coe_mk] using h.symm
  refine ⟨extension, extendPath_continuous origin path, ?_, hEq, ?_⟩
  · simpa using hEq origin.1 origin.2
  · intro time ht
    have hc : Continuous (fun t => field (extension t)) := hfield.continuous.comp
      (extendPath_continuous origin path)
    have hd : HasDerivAt
        (fun t => initial + ∫ s in origin.1..t, field (extension s))
        (field (extension time)) time :=
      (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable origin.1 time)
        hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add initial
    apply hd.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with t ht
    exact hEq t (Ioo_subset_Icc_self ht)

end SafeLearning.CompleteAppliedGlobalLipschitzPicard
