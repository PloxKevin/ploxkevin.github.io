import SafeLearning.CompleteAppliedScalarClamping
import SafeLearning.CompleteAppliedGlobalLipschitzTrajectory

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace SafeLearning.CompleteAppliedSectorGlobal
open CompleteAppliedScalarClamping CompleteAppliedGlobalLipschitzTrajectory
open CompleteAppliedSmallGainStorage

def sourceField (phi : ℝ → ℝ) (state : ℝ) : ℝ := -state-phi state

theorem actual_clamp_cannot_increase_the_magnitude (radius state : ℝ) (hr : 0 ≤ radius) :
    |clamp radius state| ≤ |state| := by
  by_cases hlo : state < -radius
  · have hc : clamp radius state = -radius := by
      simp [clamp, min_eq_right (by linarith : state ≤ radius), max_eq_left hlo.le]
    rw [hc, abs_neg, abs_of_nonneg hr, abs_of_nonpos (by linarith : state ≤ 0)]
    linarith
  · by_cases hhi : radius < state
    · have hc : clamp radius state = radius := by
        simp [clamp, min_eq_left hhi.le, max_eq_right (by linarith : -radius ≤ radius)]
      rw [hc, abs_of_nonneg hr, abs_of_nonneg (by linarith : 0 ≤ state)]
      exact hhi.le
    · rw [actual_clamp_fixes_every_point_in_the_closed_interval radius state
        ⟨le_of_not_gt hlo, le_of_not_gt hhi⟩]

theorem actual_clamping_preserves_the_source_sector_for_every_real_state
    (phi : ℝ → ℝ) (hz : phi 0 = 0)
    (hsector : ∀ state, 0 ≤ state*phi state ∧ state*phi state ≤ 3*state^2)
    (radius : ℝ) (hr : 0 < radius) :
    ∀ state, 0 ≤ state*phi (clamp radius state) ∧ state*phi (clamp radius state) ≤ 3*state^2 := by
  intro state
  have hgain := actual_sector_zero_nonlinearity_has_the_true_origin_gain_at_most_three phi hz hsector
  have hbound : |phi (clamp radius state)| ≤ 3*|state| :=
    (hgain _).trans (mul_le_mul_of_nonneg_left (actual_clamp_cannot_increase_the_magnitude radius state hr.le) (by norm_num))
  have hupper : state*phi (clamp radius state) ≤ 3*state^2 := by
    calc
      _ ≤ |state*phi (clamp radius state)| := le_abs_self _
      _ = |state| *|phi (clamp radius state)| := abs_mul _ _
      _ ≤ |state| *(3*|state|) := mul_le_mul_of_nonneg_left hbound (abs_nonneg _)
      _ = 3*state^2 := by rw [mul_left_comm, ←pow_two, sq_abs]
  refine ⟨?_, hupper⟩
  by_cases hlo : state < -radius
  · have hc : clamp radius state = -radius := by
      simp [clamp, min_eq_right (by linarith : state ≤ radius), max_eq_left hlo.le]
    rw [hc]
    have hp : phi (-radius) ≤ 0 := nonpos_of_mul_nonpos_right
      (by nlinarith [(hsector (-radius)).1] : radius*phi (-radius) ≤ 0) hr
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) hp
  · by_cases hhi : radius < state
    · have hc : clamp radius state = radius := by
        simp [clamp, min_eq_left hhi.le, max_eq_right (by linarith : -radius ≤ radius)]
      rw [hc]
      have hp : 0 ≤ phi radius := (mul_nonneg_iff_of_pos_left hr).mp (hsector radius).1
      exact mul_nonneg (by linarith) hp
    · rw [actual_clamp_fixes_every_point_in_the_closed_interval radius state
        ⟨le_of_not_gt hlo, le_of_not_gt hhi⟩]
      exact (hsector state).1

theorem actual_source_sector_field_is_locally_lipschitz
    (phi : ℝ → ℝ) (hl : LocallyLipschitz phi) : LocallyLipschitz (sourceField phi) :=
  (LocallyLipschitz.id.neg).sub hl

theorem actual_sector_feedback_has_derived_global_existence_and_the_literal_exponential_bound
    (phi : ℝ → ℝ) (hl : LocallyLipschitz phi) (hz : phi 0 = 0)
    (hsector : ∀ state, 0 ≤ state*phi state ∧ state*phi state ≤ 3*state^2)
    (initial : ℝ) : ∃ path : ℝ → ℝ,
      path 0 = initial ∧ (∀ a b : ℝ, AbsolutelyContinuousOnInterval path a b) ∧
      (∀ time : ℝ, 0 ≤ time → HasDerivAt path (sourceField phi (path time)) time) ∧
      (∀ time : ℝ, 0 ≤ time → |path time| ≤ |initial| *Real.exp (-time)) ∧
      Tendsto path atTop (𝓝 0) := by
  let radius := |initial|+1
  have hr : 0 < radius := by dsimp [radius]; positivity
  obtain ⟨K, hK⟩ := actual_locally_lipschitz_function_composed_with_clamp_is_globally_lipschitz
    phi hl radius hr.le
  let clampedField : ℝ → ℝ := fun state => -state-phi (clamp radius state)
  have hf : LipschitzWith (1+K) clampedField := LipschitzWith.id.neg.sub hK
  let path := globalSolution clampedField initial (1+K) hf
  have h0 : path 0 = initial := actual_global_solution_initial_condition _ _ _ _
  have hac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval path a b :=
    (actual_global_solution_is_c1_and_locally_absolutely_continuous _ _ _ _).2
  have hode : ∀ time : ℝ, HasDerivAt path (clampedField (path time)) time :=
    actual_global_solution_has_the_true_ode_at_every_real_time _ _ _ _
  have hs := actual_clamping_preserves_the_source_sector_for_every_real_state phi hz hsector radius hr
  have hb : ∀ time : ℝ, 0 ≤ time → |path time| ≤ |initial| *Real.exp (-time) := by
    intro time ht
    have h := actual_source_sector_negative_feedback_ac_ode_has_the_literal_exponential_bound
      (fun state => phi (clamp radius state)) hs path time ht (hac 0 time)
      (Filter.Eventually.of_forall (fun t _ => hode t)) time ⟨ht, le_rfl⟩
    simpa only [h0] using h
  have hmem : ∀ time : ℝ, 0 ≤ time → path time ∈ Icc (-radius) radius := by
    intro time ht
    have he : Real.exp (-time) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hi := (hb time ht).trans (mul_le_mul_of_nonneg_left he (abs_nonneg initial))
    simp only [mul_one] at hi
    apply abs_le.mp
    exact hi.trans (by dsimp [radius]; linarith)
  have hd : ∀ time : ℝ, 0 ≤ time → HasDerivAt path (sourceField phi (path time)) time := by
    intro time ht
    simpa only [clampedField, sourceField,
      actual_clamp_fixes_every_point_in_the_closed_interval radius _ (hmem time ht)] using hode time
  have he : Tendsto (fun time : ℝ => |initial| *Real.exp (-time)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot)
  have hlim : Tendsto path atTop (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    apply squeeze_zero' (Filter.Eventually.of_forall (fun time => abs_nonneg _)) _ he
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with time ht
    exact hb time ht
  exact ⟨path, h0, hac, hd, hb, hlim⟩

theorem actual_every_existing_finite_sector_solution_has_a_genuine_global_continuation
    (phi : ℝ → ℝ) (hl : LocallyLipschitz phi) (hz : phi 0 = 0)
    (hsector : ∀ state, 0 ≤ state*phi state ∧ state*phi state ≤ 3*state^2)
    (x : ℝ → ℝ) (horizon : ℝ) (hT : 0 ≤ horizon)
    (hc : AbsolutelyContinuousOnInterval x 0 horizon)
    (hd : ∀ᵐ time ∂volume, time ∈ Icc 0 horizon → HasDerivAt x (sourceField phi (x time)) time) :
    ∃ path : ℝ → ℝ, EqOn x path (Icc 0 horizon) ∧ path 0 = x 0 ∧
      (∀ a b : ℝ, AbsolutelyContinuousOnInterval path a b) ∧
      (∀ time : ℝ, 0 ≤ time → HasDerivAt path (sourceField phi (path time)) time) ∧
      (∀ time : ℝ, 0 ≤ time → |path time| ≤ |x 0| *Real.exp (-time)) ∧
      Tendsto path atTop (𝓝 0) := by
  obtain ⟨path, h0, hac, hode, hb, hlim⟩ :=
    actual_sector_feedback_has_derived_global_existence_and_the_literal_exponential_bound phi hl hz hsector (x 0)
  have heq := actual_locally_lipschitz_field_has_unique_existing_ac_solutions
    (sourceField phi) (actual_source_sector_field_is_locally_lipschitz phi hl)
    x path horizon hT hc (hac 0 horizon) hd
    (Filter.Eventually.of_forall (fun time ht => hode time ht.1)) h0.symm
  exact ⟨path, heq, h0, hac, hode, hb, hlim⟩

theorem actual_source_sector_storage_derivative_is_the_literal_trajectory_chain_rule
    (phi x : ℝ → ℝ)
    (hsector : ∀ state, 0 ≤ state*phi state ∧ state*phi state ≤ 3*state^2)
    (time : ℝ) (hd : HasDerivAt x (sourceField phi (x time)) time) :
    HasDerivAt (fun t => (x t)^2) (-2*(x time)^2-2*(x time)*phi (x time)) time ∧
      -2*(x time)^2-2*(x time)*phi (x time) ≤ -2*(x time)^2 := by
  constructor
  · convert hd.pow 2 using 1 <;> dsimp [sourceField] <;> ring
  · nlinarith [(hsector (x time)).1]

end SafeLearning.CompleteAppliedSectorGlobal
