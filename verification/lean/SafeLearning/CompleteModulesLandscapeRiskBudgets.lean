import SafeLearning.CompleteModulesTheory

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace SafeLearning.CompleteModulesLandscapeRiskBudgets

theorem actual_four_step_union_and_joint_success
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (failure : Fin 4 → Set Ω) (hmeas : ∀ i,MeasurableSet (failure i))
    (hbound : ∀ i,μ.real (failure i) ≤ (0.01:ℝ)) :
    μ.real (⋃ i,failure i) ≤ (0.04:ℝ) ∧
    (0.96:ℝ) ≤ μ.real (⋂ i,(failure i)ᶜ) := by
  constructor
  · have h := CompleteModulesTheory.finite_failure_union μ failure (fun _ => (0.01:ℝ)) hbound
    norm_num at h ⊢;exact h
  · have h := CompleteModulesTheory.simultaneous_success μ failure (fun _ => (0.01:ℝ)) hmeas hbound
    norm_num at h ⊢;exact h

theorem actual_independent_failure_complements_have_the_product_probability
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (failure : ι → Set Ω)
    (hind : iIndepSet failure μ) :
    μ.real (⋂ i,(failure i)ᶜ)=∏ i,μ.real ((failure i)ᶜ) := by
  have hm : ∀ i,MeasurableSet[MeasurableSpace.generateFrom {failure i}] ((failure i)ᶜ) :=
    fun i => (MeasurableSpace.measurableSet_generateFrom (Set.mem_singleton (failure i))).compl
  have h := (iIndepSet_iff failure μ).mp hind Finset.univ (fun i _ => hm i)
  simp only [Finset.mem_univ,iInter_true] at h
  simp only [Measure.real,h,ENNReal.toReal_prod]

theorem actual_independent_four_step_safe_probability
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (failure : Fin 4 → Set Ω) (hmeas : ∀ i,MeasurableSet (failure i))
    (hind : iIndepSet failure μ) (hexact : ∀ i,μ.real (failure i)=(0.01:ℝ)) :
    μ.real (⋂ i,(failure i)ᶜ)=(0.99:ℝ)^4 ∧
    μ.real (⋂ i,(failure i)ᶜ)=(0.96059601:ℝ) := by
  have hs : ∀ i,μ.real ((failure i)ᶜ)=(0.99:ℝ) := by
    intro i;rw [probReal_compl_eq_one_sub (μ := μ) (hmeas i),hexact i];norm_num
  have h : μ.real (⋂ i,(failure i)ᶜ)=(0.99:ℝ)^4 := by
    rw [actual_independent_failure_complements_have_the_product_probability μ failure hind]
    simp only [hs];norm_num
  exact ⟨h,by rw [h];norm_num⟩

theorem actual_twenty_step_total_risk_budget
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (failure : Fin 20 → Set Ω) (hmeas : ∀ i,MeasurableSet (failure i))
    (hbound : ∀ i,μ.real (failure i) ≤ (0.001:ℝ)) :
    (20:ℝ)*0.001=0.02 ∧ μ.real (⋃ i,failure i) ≤ (0.02:ℝ) ∧
    (0.98:ℝ) ≤ μ.real (⋂ i,(failure i)ᶜ) := by
  refine ⟨by norm_num,?_,?_⟩
  · have h := CompleteModulesTheory.finite_failure_union μ failure (fun _ => (0.001:ℝ)) hbound
    norm_num at h ⊢;exact h
  · have h := CompleteModulesTheory.simultaneous_success μ failure (fun _ => (0.001:ℝ)) hmeas hbound
    norm_num at h ⊢;exact h

theorem actual_reused_twenty_step_budget_is_only_sixty_percent
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (failure : Fin 20 → Set Ω) (hmeas : ∀ i,MeasurableSet (failure i))
    (hbound : ∀ i,μ.real (failure i) ≤ (0.02:ℝ)) :
    (20:ℝ)*0.02=0.4 ∧ μ.real (⋃ i,failure i) ≤ (0.4:ℝ) ∧
    (0.6:ℝ) ≤ μ.real (⋂ i,(failure i)ᶜ) := by
  refine ⟨by norm_num,?_,?_⟩
  · have h := CompleteModulesTheory.finite_failure_union μ failure (fun _ => (0.02:ℝ)) hbound
    norm_num at h ⊢;exact h
  · have h := CompleteModulesTheory.simultaneous_success μ failure (fun _ => (0.02:ℝ)) hmeas hbound
    norm_num at h ⊢;exact h

theorem actual_independent_fleet_sufficient_lower_probability
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (success : Fin 20 → Set Ω) (hind : iIndepSet success μ)
    (hbound : ∀ i,(0.9975:ℝ) ≤ μ.real (success i)) :
    (0.9975:ℝ)^20 ≤ μ.real (⋂ i,success i) ∧
    |(0.9975:ℝ)^20-(0.95117:ℝ)|<0.000005 ∧
    (0.95:ℝ)<(0.9975:ℝ)^20 := by
  refine ⟨CompleteModulesTheory.independent_success_lower μ 20 success hind _ (by norm_num) hbound,?_,?_⟩
  · norm_num
  · norm_num


theorem actual_independent_fleet_failure_budget_implies_the_source_product_lower_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (failure : Fin 20 → Set Ω) (hmeas : ∀ i,MeasurableSet (failure i))
    (hind : iIndepSet failure μ) (hbound : ∀ i,μ.real (failure i) ≤ (0.0025:ℝ)) :
    (0.9975:ℝ)^20 ≤ μ.real (⋂ i,(failure i)ᶜ) := by
  rw [actual_independent_failure_complements_have_the_product_probability μ failure hind]
  have hs : ∀ i,(0.9975:ℝ) ≤ μ.real ((failure i)ᶜ) := by
    intro i
    rw [probReal_compl_eq_one_sub (μ := μ) (hmeas i)]
    linarith [hbound i]
  calc
    (0.9975:ℝ)^20=∏ _i : Fin 20,(0.9975:ℝ) := by simp
    _ ≤ ∏ i,μ.real ((failure i)ᶜ) :=
      Finset.prod_le_prod₀ (fun _ _ => by norm_num) (fun i _ => hs i)

/-- A shared failure event exhibits dependence under the source marginal bounds. -/
theorem actual_shared_four_step_failure_has_a_different_probability_than_multiplication
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (failure : Set Ω) (hmeas : MeasurableSet failure) (hexact : μ.real failure=(0.01:ℝ)) :
    μ.real (⋂ _i : Fin 4,failureᶜ)=(0.99:ℝ) ∧
    μ.real (⋂ _i : Fin 4,failureᶜ)≠(0.99:ℝ)^4 ∧
    ¬iIndepSet (fun _i : Fin 4 => failure) μ := by
  have he : μ.real (⋂ _i : Fin 4,failureᶜ)=(0.99:ℝ) := by
    simp only [iInter_const]
    rw [probReal_compl_eq_one_sub (μ := μ) hmeas,hexact]
    norm_num
  refine ⟨he,by rw [he];norm_num,?_⟩
  intro hind
  have h := actual_independent_four_step_safe_probability μ (fun _ => failure)
    (fun _ => hmeas) hind (fun _ => hexact)
  rw [he] at h
  norm_num at h

/-- A repeated event makes the union-bound allocation strictly conservative. -/
theorem actual_shared_twenty_step_failure_can_make_the_total_budget_conservative
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (failure : Set Ω) (hmeas : MeasurableSet failure) (hexact : μ.real failure=(0.001:ℝ)) :
    (∀ _i : Fin 20,μ.real failure ≤ (0.001:ℝ)) ∧
    μ.real (⋂ _i : Fin 20,failureᶜ)=(0.999:ℝ) ∧
    (0.98:ℝ)<μ.real (⋂ _i : Fin 20,failureᶜ) := by
  have he : μ.real (⋂ _i : Fin 20,failureᶜ)=(0.999:ℝ) := by
    simp only [iInter_const]
    rw [probReal_compl_eq_one_sub (μ := μ) hmeas,hexact]
    norm_num
  refine ⟨fun _ => hexact.le,he,?_⟩
  rw [he];norm_num

end SafeLearning.CompleteModulesLandscapeRiskBudgets
