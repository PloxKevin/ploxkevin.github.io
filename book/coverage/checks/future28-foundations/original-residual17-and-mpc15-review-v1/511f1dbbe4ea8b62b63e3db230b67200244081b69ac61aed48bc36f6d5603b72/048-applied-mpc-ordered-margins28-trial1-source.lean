import SafeLearning.CompleteCoreMPCFirstSuccessor27

set_option autoImplicit false
noncomputable section


namespace SafeLearning.CompleteCoreMPCOrderedMargins28
open scoped Matrix
attribute [local instance] Matrix.linftyOpNormedAddCommGroup

theorem actual_nonzero_local_quadratic_tracking_bounds_order_the_constants
    {S : Type*} [NormedAddCommGroup S] (x z : S) (value cL cU : ℝ)
    (hne : x ≠ z) (hlower : cL * ‖x-z‖^2 ≤ value)
    (hupper : value ≤ cU * ‖x-z‖^2) : cL ≤ cU := by
  have hpositive : 0 < ‖x-z‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
  exact (mul_le_mul_iff_left₀ hpositive).mp (hlower.trans hupper)

/-- The actual epsilon formula supplies the first state-row margin once the
original positive quadratic constants are ordered. No margin conclusion is
put into a certificate premise. Deriving that order from arbitrary state-set
geometry remains a separate issue for the full theorem. -/
theorem actual_original_epsilon_formula_covers_the_first_state_row_radius
    {I J K L : Type*} [Fintype I] [Fintype J] [Fintype K] [Fintype L]
    (H : Matrix J I ℝ) (Lt : Matrix L K ℝ) (lambda eta cL cU kmax : ℝ)
    (hlambda : 0 ≤ lambda) (heta : 0 ≤ eta) (hcL : 0 < cL)
    (horder : cL ≤ cU) :
    ‖H‖ * (lambda*eta) ≤ eta*lambda*Real.sqrt (cU/cL)*max ‖H‖ (‖Lt‖*kmax) := by
  have hratio : 1 ≤ cU/cL := (le_div_iff₀ hcL).2 (by simpa using horder)
  have hnonneg : 0 ≤ cU/cL := le_trans (by norm_num) hratio
  have hscale : 1 ≤ Real.sqrt (cU/cL) := by
    nlinarith [Real.sqrt_nonneg (cU/cL),Real.sq_sqrt hnonneg]
  have hrow : ‖H‖ ≤ ‖H‖*Real.sqrt (cU/cL) := by
    nlinarith [norm_nonneg H]
  have hmax : ‖H‖*Real.sqrt (cU/cL) ≤ max ‖H‖ (‖Lt‖*kmax)*Real.sqrt (cU/cL) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
  calc
    ‖H‖*(lambda*eta) ≤ (max ‖H‖ (‖Lt‖*kmax)*Real.sqrt (cU/cL))*(lambda*eta) :=
      mul_le_mul_of_nonneg_right (hrow.trans hmax) (mul_nonneg hlambda heta)
    _ = eta*lambda*Real.sqrt (cU/cL)*max ‖H‖ (‖Lt‖*kmax) := by ring
end SafeLearning.CompleteCoreMPCOrderedMargins28
