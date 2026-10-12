import SafeLearning.CompleteChowLP21

noncomputable section
namespace SafeLearning.CompleteChowConstantLP21
open SafeLearning.CompleteChowLP21

theorem actual_constant_lp_feasibility_iff (q : ℝ) :
    lpFeasible (fun _ => q) ↔ 0 ≤ q ∧ q ≤ 13/142 := by
  constructor
  · intro h
    refine ⟨h.1 0,?_⟩
    have hb := h.2
    dsimp [weightedSlack] at hb
    linarith
  · rintro ⟨h0,hq⟩
    refine ⟨fun _ => h0,?_⟩
    dsimp [weightedSlack]
    linarith

theorem actual_constant_is_the_global_constant_class_optimum
    (q : ℝ) (hq : lpFeasible (fun _ => q)) :
    objective (fun _ => q) ≤ objective constantSlack := by
  have hb := (actual_constant_lp_feasibility_iff q).mp hq
  dsimp [objective,constantSlack]
  linarith

theorem actual_constant_class_optimum_is_unique
    (q : ℝ) (hq : lpFeasible (fun _ => q)) :
    objective (fun _ => q)=objective constantSlack ↔ q=13/142 := by
  dsimp [objective,constantSlack]
  constructor <;> intro h <;> linarith

end SafeLearning.CompleteChowConstantLP21
