import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteModulesLandscapeModelError

def barrier (x : ℝ) : ℝ := -x
def nominalController (x : ℝ) : ℝ := -x
def robustController (x : ℝ) : ℝ := -x-1
def nominalClosedField (x : ℝ) : ℝ := nominalController x
def wrongClosedField (x : ℝ) : ℝ := 1+nominalController x
def robustClosedField (x : ℝ) : ℝ := 1+robustController x
def unsafeActualPath (t : ℝ) : ℝ := 1-Real.exp (-t)

theorem actual_nominal_barrier_and_controller_have_true_C1_and_Lipschitz_regularities :
    ContDiff ℝ 1 barrier ∧ LipschitzWith 1 nominalController ∧
      LipschitzWith 1 robustController ∧ StrictMono (fun h : ℝ => h) := by
  refine ⟨?_,?_,?_,?_⟩
  · simpa [barrier] using (contDiff_id.neg : ContDiff ℝ 1 (fun x : ℝ => -x))
  · simpa [nominalController] using (LipschitzWith.id.neg : LipschitzWith 1 (fun x : ℝ => -x))
  · simpa [robustController] using
      ((LipschitzWith.id.neg).sub_const (1:ℝ) : LipschitzWith 1 (fun x : ℝ => -x-1))
  · exact strictMono_id

theorem actual_nominal_control_affine_barrier_residual_vanishes_everywhere (x : ℝ) :
    HasDerivAt barrier (-1) x ∧
      deriv barrier x * nominalClosedField x + barrier x = 0 := by
  have hd : HasDerivAt barrier (-1) x := by simpa [barrier] using (hasDerivAt_id x).neg
  refine ⟨hd,?_⟩
  rw [hd.deriv]
  simp [nominalClosedField,nominalController,barrier]

theorem actual_nominal_safe_equilibrium_is_a_classical_closed_loop_trajectory :
    ∀t : ℝ, HasDerivAt (fun _ : ℝ => (0:ℝ)) (nominalClosedField 0) t ∧
      0 ≤ barrier 0 := by
  intro t
  simp only [nominalClosedField,nominalController,barrier,neg_zero]
  exact ⟨hasDerivAt_const t 0,le_rfl⟩

theorem actual_wrong_model_has_the_true_source_safe_initial_condition_and_unsafe_trajectory :
    unsafeActualPath 0 = 0 ∧
      (∀t : ℝ, HasDerivAt unsafeActualPath (wrongClosedField (unsafeActualPath t)) t) ∧
      ∀t : ℝ, 0 < t → barrier (unsafeActualPath t) < 0 := by
  refine ⟨by simp [unsafeActualPath],?_,?_⟩
  · intro t
    have hd := (((hasDerivAt_id t).neg).exp).const_sub (1:ℝ)
    convert hd using 1 <;> simp [unsafeActualPath,wrongClosedField,nominalController]
  · intro t ht
    have he : Real.exp (-t) < 1 := by simpa using (Real.exp_lt_exp.mpr (neg_neg_of_pos ht))
    dsimp [barrier,unsafeActualPath]
    linarith

theorem actual_uncertainty_margin_transfers_the_nominal_barrier_residual
    (x u disturbance allowance : ℝ) (hmargin : allowance ≤ -u-x)
    (herr : disturbance ≤ allowance) :
    0 ≤ -(u+disturbance)-x := by linarith

theorem actual_one_unit_robust_margin_repairs_the_wrong_drift_with_a_safe_classical_trajectory :
    (∀x : ℝ, deriv barrier x * robustController x + barrier x = 1) ∧
      (∀x : ℝ, deriv barrier x * robustClosedField x + barrier x = 0) ∧
      ∀t : ℝ, HasDerivAt (fun _ : ℝ => (0:ℝ)) (robustClosedField 0) t ∧
        0 ≤ barrier 0 := by
  have hd : ∀x : ℝ, deriv barrier x = -1 := fun x =>
    (actual_nominal_control_affine_barrier_residual_vanishes_everywhere x).1.deriv
  refine ⟨?_,?_,?_⟩
  · intro x
    rw [hd x]
    dsimp [robustController,barrier]
    ring
  · intro x
    rw [hd x]
    dsimp [robustClosedField,robustController,barrier]
    ring
  · intro t
    norm_num [robustClosedField,robustController,barrier]
    exact hasDerivAt_const t 0

end SafeLearning.CompleteModulesLandscapeModelError
