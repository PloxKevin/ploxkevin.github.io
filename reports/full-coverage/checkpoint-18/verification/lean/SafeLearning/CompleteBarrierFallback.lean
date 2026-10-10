import Mathlib

set_option autoImplicit false
noncomputable section
open Set
open scoped RealInnerProductSpace

namespace SafeLearning.CompleteBarrierFallback

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def lieObjective (a : ℝ) (b u : E) : ℝ := a + ⟪b, u⟫

def cbfInputs (a : ℝ) (b : E) : Set E := {u | 0 ≤ lieObjective a b u}

theorem zero_coefficient_every_input_maximizes (a : ℝ) (u : E) :
    IsMaxOn (lieObjective a (0 : E)) univ u := by
  intro v hv
  simp [lieObjective]

theorem nonzero_coefficient_no_maximum (a : ℝ) (b : E) (hb : b ≠ 0) :
    ¬ ∃ u : E, IsMaxOn (lieObjective a b) univ u := by
  rintro ⟨u, hu⟩
  have hle := hu (mem_univ (u + b))
  have hpos := (real_inner_self_pos (x := b)).mpr hb
  change a + ⟪b, u + b⟫ ≤ a + ⟪b, u⟫ at hle
  rw [inner_add_right] at hle
  linarith

theorem compact_maximizing_fallback (a : ℝ) (b : E) (U : Set E)
    (hc : IsCompact U) (hne : U.Nonempty)
    (hfeasible : ∃ u ∈ U, u ∈ cbfInputs a b) :
    ∃ u ∈ U, IsMaxOn (lieObjective a b) U u ∧ u ∈ cbfInputs a b := by
  have hcont : Continuous (lieObjective a b) :=
    continuous_const.add (continuous_const.inner continuous_id)
  obtain ⟨u, hu, hmax⟩ := hc.exists_isMaxOn hne hcont.continuousOn
  obtain ⟨v, hv, hsafe⟩ := hfeasible
  refine ⟨u, hu, hmax, ?_⟩
  change 0 ≤ lieObjective a b u
  have hle : lieObjective a b v ≤ lieObjective a b u := hmax hv
  exact le_trans hsafe hle

theorem cbf_inputs_closed (a : ℝ) (b : E) : IsClosed (cbfInputs a b) := by
  exact isClosed_le continuous_const
    (continuous_const.add (continuous_const.inner continuous_id))

theorem cbf_inputs_convex (a : ℝ) (b : E) : Convex ℝ (cbfInputs a b) := by
  intro u hu v hv r s hr hs hrs
  change 0 ≤ a + ⟪b, r • u + s • v⟫
  change 0 ≤ a + ⟪b, u⟫ at hu
  change 0 ≤ a + ⟪b, v⟫ at hv
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  nlinarith [mul_nonneg hr hu, mul_nonneg hs hv,
    congrArg (fun z : ℝ => z * a) hrs]

theorem actual_minimum_norm_fallback [CompleteSpace E] (a : ℝ) (b : E)
    (hne : (cbfInputs a b).Nonempty) :
    ∃ u ∈ cbfInputs a b, ∀ v ∈ cbfInputs a b, ‖u‖ ≤ ‖v‖ := by
  obtain ⟨u, hu, heq⟩ := exists_norm_eq_iInf_of_complete_convex hne
    (cbf_inputs_closed a b).isComplete (cbf_inputs_convex a b) (0 : E)
  refine ⟨u, hu, ?_⟩
  intro v hv
  have hle : (⨅ w : cbfInputs a b, ‖(0 : E) - w‖) ≤ ‖(0 : E) - v‖ :=
    ciInf_le (f := fun w : cbfInputs a b => ‖(0 : E) - w‖)
      ⟨0, Set.forall_mem_range.mpr (fun _ => norm_nonneg _)⟩ (⟨v, hv⟩ : cbfInputs a b)
  simpa only [zero_sub, norm_neg] using heq.trans_le hle

end SafeLearning.CompleteBarrierFallback
