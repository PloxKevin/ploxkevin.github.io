import SafeLearning.CompleteBarrierAEComparison

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
namespace SafeLearning.CompleteBarrierDiscontinuousSign

/-- This is exactly -sgn with the source's convention sgn(0)=1. -/
def field (x : ℝ) : ℝ := if x < 0 then 1 else -1

theorem field_at_zero : field 0 = -1 := by simp [field]

theorem genuine_measurable_field : Measurable field := by
  apply Measurable.ite (measurableSet_lt measurable_id measurable_const)
    measurable_const measurable_const

/-- A hypothetical Caratheodory solution from zero must remain zero, by
applying the a.e. one-sided comparison argument in both directions. -/
theorem hypothetical_solution_zero (x : ℝ → ℝ) (T : ℝ)
    (hT : 0 ≤ T) (hx : AbsolutelyContinuousOnInterval x 0 T) (h0 : x 0 = 0)
    (hd : ∀ᵐ t ∂volume, t ∈ Icc 0 T → HasDerivAt x (field (x t)) t) :
    ∀ t ∈ Icc 0 T, x t = 0 := by
  have hu : ∀ᵐ t ∂volume, t ∈ Icc 0 T → 0 < x t →
      field (x t) ≤ 0 * x t := by
    exact Eventually.of_forall fun t _ hp => by simp [field, not_lt.mpr hp.le]
  have hupper := CompleteBarrierAEComparison.genuine_ae_one_sided_invariance
    x (fun t => field (x t)) 0 T 0 hT hx hd hu (by simp [h0])
  have hdn : ∀ᵐ t ∂volume, t ∈ Icc 0 T →
      HasDerivAt (fun s => -x s) (-field (x t)) t := by
    filter_upwards [hd] with t hd ht
    exact (hd ht).neg
  have hl : ∀ᵐ t ∂volume, t ∈ Icc 0 T → 0 < -x t →
      -field (x t) ≤ 0 * (-x t) := by
    exact Eventually.of_forall fun t _ hp => by
      have hn : x t < 0 := by linarith
      simp [field, hn]
  have hlower := CompleteBarrierAEComparison.genuine_ae_one_sided_invariance
    (fun t => -x t) (fun t => -field (x t)) 0 T 0 hT hx.neg hdn hl (by simp [h0])
  intro t ht
  linarith [hupper t ht, hlower t ht]

/-- No actual absolutely continuous solution of this measurable ODE starts at
zero on any interval of positive length. The contradiction uses the actual
ODE derivative and the fundamental theorem of calculus. -/
theorem genuine_no_caratheodory_solution (x : ℝ → ℝ) (T : ℝ)
    (hT : 0 < T) (hx : AbsolutelyContinuousOnInterval x 0 T) (h0 : x 0 = 0)
    (hd : ∀ᵐ t ∂volume, t ∈ Icc 0 T → HasDerivAt x (field (x t)) t) : False := by
  have hz := hypothetical_solution_zero x T hT.le hx h0 hd
  have hder : ∀ᵐ t ∂volume, t ∈ uIoc 0 T → deriv x t = (-1 : ℝ) := by
    filter_upwards [hd] with t hd ht
    have ht' : t ∈ Icc 0 T := by
      rw [uIoc_of_le hT.le] at ht
      exact ⟨ht.1.le, ht.2⟩
    rw [(hd ht').deriv, hz t ht', field_at_zero]
  have hi := intervalIntegral.integral_congr_ae hder
  rw [hx.integral_deriv_eq_sub, intervalIntegral.integral_const] at hi
  have hzero : x T = 0 := hz T ⟨hT.le, le_rfl⟩
  simp only [hzero, h0, sub_self, sub_zero, smul_eq_mul, mul_neg_one] at hi
  linarith

end SafeLearning.CompleteBarrierDiscontinuousSign
