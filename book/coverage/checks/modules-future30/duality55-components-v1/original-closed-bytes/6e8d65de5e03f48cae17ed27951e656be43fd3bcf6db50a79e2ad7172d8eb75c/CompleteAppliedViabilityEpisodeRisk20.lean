import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Set
namespace SafeLearning.CompleteAppliedViabilityEpisodeRisk20

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Integrating a history-conditional action probability over the safe prefix gives the
actual joint probability of that prefix and that critical action. -/
theorem actual_history_conditional_bound_gives_joint_action_bound
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (safe action : Set Ω) (hs : MeasurableSet[m] safe) (ha : MeasurableSet[mΩ] action)
    (δ : ℝ) (hconditional : ∀ᵐ ω ∂μ.restrict safe,
      (μ[action.indicator (fun _ => (1 : ℝ)) | m]) ω ≤ δ) :
    μ.real (safe ∩ action) ≤ δ * μ.real safe := by
  letI : MeasurableSpace Ω := mΩ
  have hi : Integrable (action.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator ha
  have hce := setIntegral_condExp hm hi hs
  have heq : (∫ ω in safe, (μ[action.indicator (fun _ => (1 : ℝ)) | m]) ω ∂μ) =
      μ.real (safe ∩ action) := by
    rw [hce,setIntegral_indicator ha,setIntegral_const,smul_eq_mul,mul_one]
  have hb := setIntegral_mono_ae_restrict (integrable_condExp.integrableOn)
    ((integrable_const δ).integrableOn) hconditional
  rw [heq,setIntegral_const,smul_eq_mul] at hb
  simpa [mul_comm] using hb

def pastCritical (bad : ℕ → Set Ω) (t : ℕ) : Set Ω := ⋃ s ∈ Finset.range t, bad s
def firstCritical (bad : ℕ → Set Ω) (t : ℕ) : Set Ω := (pastCritical bad t)ᶜ ∩ bad t

theorem actual_any_critical_choice_has_a_first_critical_time
    (bad : ℕ → Set Ω) (N : ℕ) :
    pastCritical bad N = ⋃ t ∈ Finset.range N, firstCritical bad t := by
  classical
  induction N with
  | zero => simp [pastCritical]
  | succ N ih =>
    have hl : pastCritical bad (N+1) = bad N ∪ pastCritical bad N := by
      simp [pastCritical,Finset.range_add_one]
    have hr : (⋃ t ∈ Finset.range (N+1), firstCritical bad t) =
        firstCritical bad N ∪ (⋃ t ∈ Finset.range N, firstCritical bad t) := by
      simp [Finset.range_add_one]
    rw [hl,hr,← ih]
    change bad N ∪ pastCritical bad N = ((pastCritical bad N)ᶜ ∩ bad N) ∪ pastCritical bad N
    ext ω
    simp only [mem_union,mem_inter_iff,mem_compl_iff]
    tauto

theorem actual_conditional_three_action_bound_gives_first_time_bound
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (safe : Set Ω) (hs : MeasurableSet[m] safe) (action : Fin 3 → Set Ω)
    (ha : ∀ j, MeasurableSet[mΩ] (action j)) (δ : ℝ) (hδ : 0 ≤ δ)
    (hconditional : ∀ j, ∀ᵐ ω ∂μ.restrict safe,
      (μ[(action j).indicator (fun _ => (1 : ℝ)) | m]) ω ≤ δ) :
    μ.real (safe ∩ ⋃ j, action j) ≤ 3*δ := by
  letI : MeasurableSpace Ω := mΩ
  have heq : safe ∩ (⋃ j, action j) = ⋃ j, safe ∩ action j := by
    ext ω
    simp
  rw [heq]
  calc
    μ.real (⋃ j, safe ∩ action j) ≤ ∑ j, μ.real (safe ∩ action j) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j : Fin 3, δ * μ.real safe :=
      Finset.sum_le_sum (fun j _ => actual_history_conditional_bound_gives_joint_action_bound
        μ m hm safe (action j) hs (ha j) δ (hconditional j))
    _ = 3*δ*μ.real safe := by simp; ring
    _ ≤ 3*δ := by
      have hu : μ.real safe ≤ 1 := by
        simpa using measureReal_mono (subset_univ safe) (μ := μ)
      nlinarith

theorem actual_fifty_history_conditioned_decisions_have_episode_risk_at_most_three_tenths
    (μ : Measure Ω) [IsProbabilityMeasure μ] (action : ℕ → Fin 3 → Set Ω)
    (ha : ∀ t j, MeasurableSet (action t j))
    (history : ℕ → MeasurableSpace Ω) (hhistory : ∀ t, history t ≤ mΩ)
    (hsafe : ∀ t, MeasurableSet[history t]
      (pastCritical (fun s => ⋃ j, action s j) t)ᶜ)
    (hconditional : ∀ t < 50, ∀ j, ∀ᵐ ω ∂μ.restrict
      (pastCritical (fun s => ⋃ j, action s j) t)ᶜ,
      (μ[(action t j).indicator (fun _ => (1 : ℝ)) | history t]) ω ≤ 2/1000) :
    μ.real (pastCritical (fun t => ⋃ j, action t j) 50) ≤ 3/10 ∧
      7/10 ≤ μ.real (pastCritical (fun t => ⋃ j, action t j) 50)ᶜ := by
  have hb : ∀ t ∈ Finset.range 50,
      μ.real (firstCritical (fun s => ⋃ j, action s j) t) ≤ 6/1000 := by
    intro t ht
    convert actual_conditional_three_action_bound_gives_first_time_bound μ (history t)
      (hhistory t) _ (hsafe t) (action t) (ha t) (2/1000) (by norm_num)
      (hconditional t (Finset.mem_range.mp ht)) using 1 <;> norm_num [firstCritical]
  have hu : μ.real (pastCritical (fun t => ⋃ j, action t j) 50) ≤ 3/10 := by
    rw [actual_any_critical_choice_has_a_first_critical_time]
    calc
      μ.real (⋃ t ∈ Finset.range 50, firstCritical (fun s => ⋃ j, action s j) t) ≤
          ∑ t ∈ Finset.range 50, μ.real (firstCritical (fun s => ⋃ j, action s j) t) :=
        measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _t ∈ Finset.range 50, (6/1000 : ℝ) := Finset.sum_le_sum hb
      _ = 3/10 := by norm_num
  refine ⟨hu,?_⟩
  have hm : MeasurableSet (pastCritical (fun t => ⋃ j, action t j) 50) := by
    unfold pastCritical
    exact Finset.measurableSet_biUnion _ (fun t _ => MeasurableSet.iUnion (ha t))
  rw [measureReal_compl hm]
  have hu1 : μ.real univ = 1 := by simp
  rw [hu1]
  linarith

end SafeLearning.CompleteAppliedViabilityEpisodeRisk20
