import SafeLearning.CompleteModulesTheory

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace SafeLearning.CompleteModulesVerificationPlannerFeasibility20

theorem actual_conditional_event_probability_formula
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (feasible failure : Set Ω) (hF : MeasurableSet feasible) :
    (cond P feasible).real failure = P.real (failure ∩ feasible) / P.real feasible := by
  unfold Measure.real
  rw [cond_apply hF, ENNReal.toReal_mul, ENNReal.toReal_inv, Set.inter_comm]
  ring

theorem actual_source_feasibility_bound_gives_conditional_failure_and_safety
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F U : Set Ω) (hF : MeasurableSet F) (hU : MeasurableSet U)
    (hprob : P.real F = (1/2 : ℝ)) (hbad : P.real (U ∩ F) ≤ (1/25 : ℝ)) :
    (cond P F).real U ≤ (2/25 : ℝ) ∧
      (23/25 : ℝ) ≤ (cond P F).real Uᶜ := by
  have hsplit : P.real F = P.real (U ∩ F) + P.real (Uᶜ ∩ F) := by
    have he : F = (U ∩ F) ∪ (Uᶜ ∩ F) := by ext x; simp; tauto
    calc
      P.real F = P.real ((U ∩ F) ∪ (Uᶜ ∩ F)) := congrArg P.real he
      _ = _ := measureReal_union
        (Set.disjoint_left.mpr (fun x hx hy => hy.1 hx.1)) (hU.compl.inter hF)
  rw [actual_conditional_event_probability_formula P F U hF,
    actual_conditional_event_probability_formula P F Uᶜ hF, hprob]
  constructor <;> linarith

theorem actual_unspecified_infeasible_runs_give_only_point_four_six_safety
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F U : Set Ω) (hF : MeasurableSet F) (hU : MeasurableSet U)
    (hprob : P.real F = (1/2 : ℝ)) (hbad : P.real (U ∩ F) ≤ (1/25 : ℝ)) :
    P.real U ≤ (27/50 : ℝ) ∧ (23/50 : ℝ) ≤ P.real Uᶜ := by
  have hcomp : P.real Fᶜ = (1/2 : ℝ) := by
    rw [probReal_compl_eq_one_sub hF, hprob]; norm_num
  have hout : P.real (U ∩ Fᶜ) ≤ (1/2 : ℝ) := by
    simpa [hcomp] using measureReal_mono (μ := P)
      (show U ∩ Fᶜ ⊆ Fᶜ from inter_subset_right)
  have hsplit : P.real U = P.real (U ∩ F) + P.real (U ∩ Fᶜ) := by
    have he : U = (U ∩ F) ∪ (U ∩ Fᶜ) := by ext x; simp
    calc
      P.real U = P.real ((U ∩ F) ∪ (U ∩ Fᶜ)) := congrArg P.real he
      _ = _ := measureReal_union
        (Set.disjoint_left.mpr (fun x hx hy => hy.2 hx.2)) (hU.inter hF.compl)
  constructor
  · linarith
  · rw [probReal_compl_eq_one_sub hU]; linarith

def plannerLaw : PMF (Fin 3) := PMF.ofFintype
  (fun i => ((![(1/25 : ℝ≥0),23/50,1/2] : Fin 3 → ℝ≥0) i : ℝ≥0∞))
  (by norm_cast; norm_num [Fin.sum_univ_succ])
def plannerFeasible : Set (Fin 3) := {i | i = 0 ∨ i = 1}
def plannerUnsafe : Set (Fin 3) := {i | i = 0 ∨ i = 2}

theorem actual_normalized_planner_model_attains_all_source_bounds :
    plannerLaw.toMeasure.real plannerFeasible = (1/2 : ℝ) ∧
      plannerLaw.toMeasure.real (plannerUnsafe ∩ plannerFeasible) = (1/25 : ℝ) ∧
      plannerLaw.toMeasure.real plannerUnsafe = (27/50 : ℝ) ∧
      plannerLaw.toMeasure.real plannerUnsafeᶜ = (23/50 : ℝ) := by
  have he : ∀ E : Set (Fin 3), plannerLaw.toMeasure.real E =
      (plannerLaw.toOuterMeasure E).toReal := by
    intro E
    unfold Measure.real
    rw [PMF.toMeasure_apply_eq_toOuterMeasure_apply _ (Set.toFinite E).measurableSet]
  simp only [he]
  norm_num [plannerLaw,plannerFeasible,plannerUnsafe,
    PMF.toOuterMeasure_ofFintype_apply,tsum_fintype,Fin.sum_univ_succ,Set.indicator]
  all_goals simp (disch := finiteness) only [ENNReal.toReal_add]
  all_goals norm_num

theorem actual_planner_conditional_law_is_safe_point_nine_two_while_original_is_point_four_six :
    (cond plannerLaw.toMeasure plannerFeasible).real plannerUnsafe = (2/25 : ℝ) ∧
      (cond plannerLaw.toMeasure plannerFeasible).real plannerUnsafeᶜ = (23/25 : ℝ) ∧
      plannerLaw.toMeasure.real plannerUnsafeᶜ < (24/25 : ℝ) := by
  have hF := (Set.toFinite plannerFeasible).measurableSet
  have hcomp : plannerLaw.toMeasure.real (plannerUnsafeᶜ ∩ plannerFeasible) = (23/50 : ℝ) := by
    have he : plannerUnsafeᶜ ∩ plannerFeasible = plannerUnsafeᶜ := by
      ext i; fin_cases i <;> norm_num [plannerUnsafe,plannerFeasible]
    rw [he,actual_normalized_planner_model_attains_all_source_bounds.2.2.2]
  rw [actual_conditional_event_probability_formula _ _ _ hF,
    actual_conditional_event_probability_formula _ _ _ hF,
    actual_normalized_planner_model_attains_all_source_bounds.1,
    actual_normalized_planner_model_attains_all_source_bounds.2.1,
    actual_normalized_planner_model_attains_all_source_bounds.2.2.2,hcomp]
  norm_num

theorem actual_safe_fallback_or_almost_sure_feasibility_restores_the_unconditional_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F U : Set Ω) (hF : MeasurableSet F) (hU : MeasurableSet U)
    (hbad : P.real (U ∩ F) ≤ (1/25 : ℝ))
    (hcoverage : U ⊆ F ∨ P.real F = 1) :
    (24/25 : ℝ) ≤ P.real Uᶜ := by
  have hout : P.real (U ∩ Fᶜ) = 0 := by
    rcases hcoverage with hs | hp
    · have he : U ∩ Fᶜ = ∅ := by
        ext x; simp only [mem_inter_iff,mem_compl_iff,mem_empty_iff_false]
        exact ⟨fun h => h.2 (hs h.1),False.elim⟩
      simp [he]
    · have hcomp : P.real Fᶜ = 0 := by rw [probReal_compl_eq_one_sub hF,hp]; norm_num
      have hm : P.real (U ∩ Fᶜ) ≤ P.real Fᶜ :=
        measureReal_mono (μ := P) inter_subset_right
      rw [hcomp] at hm
      exact le_antisymm hm (measureReal_nonneg (μ := P) (s := U ∩ Fᶜ))
  have hsplit : P.real U = P.real (U ∩ F) + P.real (U ∩ Fᶜ) := by
    have he : U = (U ∩ F) ∪ (U ∩ Fᶜ) := by ext x; simp
    calc
      P.real U = P.real ((U ∩ F) ∪ (U ∩ Fᶜ)) := congrArg P.real he
      _ = _ := measureReal_union
        (Set.disjoint_left.mpr (fun x hx hy => hy.2 hx.2)) (hU.inter hF.compl)
  rw [probReal_compl_eq_one_sub hU]
  linarith

end SafeLearning.CompleteModulesVerificationPlannerFeasibility20
