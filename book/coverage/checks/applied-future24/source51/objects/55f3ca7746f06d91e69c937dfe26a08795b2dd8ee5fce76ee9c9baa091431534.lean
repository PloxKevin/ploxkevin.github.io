import SafeLearning.CompleteAppliedProbabilityModel
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedFailureCounts
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

def failurePattern {Ω : Type*} {n : ℕ} (A : Fin n → Set Ω)
    (S : Finset (Fin n)) : Set Ω := {omega | ∀ i,omega∈A i ↔ i∈S}

def failedTrials {Ω : Type*} {n : ℕ} (A : Fin n → Set Ω) (omega : Ω) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => omega∈A i)

def failureCount {Ω : Type*} {n : ℕ} (A : Fin n → Set Ω) (omega : Ω) : ℕ :=
  (failedTrials A omega).card

theorem pattern_iff_failed_trials {Ω : Type*} {n : ℕ}
    (A : Fin n → Set Ω) (S : Finset (Fin n)) (omega : Ω) :
    omega∈failurePattern A S ↔ failedTrials A omega=S := by
  classical
  change (∀ i,omega∈A i ↔ i∈S) ↔ _
  constructor
  · intro h
    ext i
    simpa only [failedTrials,Finset.mem_filter,Finset.mem_univ,true_and] using h i
  · intro h i
    have hi := Finset.ext_iff.mp h i
    simpa only [failedTrials,Finset.mem_filter,Finset.mem_univ,true_and] using hi

theorem actual_pattern_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (A : Fin n → Set Ω)
    (hA : ∀ i,MeasurableSet (A i)) (hind : iIndepSet A μ)
    (q : ℝ) (hq : ∀ i,μ.real (A i)=q) (S : Finset (Fin n)) :
    MeasurableSet (failurePattern A S) ∧
      μ.real (failurePattern A S)=∏ i,if i∈S then q else 1-q := by
  classical
  let B : Fin n → Set Ω := fun i => if i∈S then A i else (A i)ᶜ
  have hB : ∀ i,MeasurableSet (B i) := by
    intro i
    by_cases hi : i∈S <;> simp only [B,hi,ite_true,ite_false]
    · exact hA i
    · exact (hA i).compl
  have he : failurePattern A S=⋂ i,B i := by
    ext omega
    simp only [failurePattern,Set.mem_setOf_eq,Set.mem_iInter]
    constructor
    · intro h i
      by_cases hi : i∈S
      · simpa only [B,hi,ite_true] using (h i).mpr hi
      · simpa only [B,hi,ite_false,Set.mem_compl_iff] using
          (fun ha => hi ((h i).mp ha))
    · intro h i
      by_cases hi : i∈S
      · have ha : omega∈A i := by simpa only [B,hi,ite_true] using h i
        exact ⟨fun _ => hi,fun _ => ha⟩
      · have ha : omega∉A i := by simpa only [B,hi,ite_false,Set.mem_compl_iff] using h i
        exact ⟨fun hmem => False.elim (ha hmem),fun hmem => False.elim (hi hmem)⟩
  have hprod := (iIndepSet_iff A μ).mp hind Finset.univ
    (f := B) (fun i _ => by
      have hm : MeasurableSet[MeasurableSpace.generateFrom {A i}] (A i) :=
        MeasurableSpace.measurableSet_generateFrom (by simp)
      by_cases hi : i∈S <;> simp only [B,hi,ite_true,ite_false]
      · exact hm
      · exact hm.compl)
  have hp : μ (⋂ i,B i)=∏ i,μ (B i) := by simpa using hprod
  refine ⟨he ▸ MeasurableSet.iInter hB,?_⟩
  have hpr := congrArg ENNReal.toReal hp
  simp only [ENNReal.toReal_prod] at hpr
  change μ.real (⋂ i,B i)=∏ i,μ.real (B i) at hpr
  rw [he,hpr]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hs : i∈S
  · simpa only [B,hs,ite_true] using hq i
  · simp only [B,hs,ite_false]
    rw [SafeLearning.CompleteAppliedProbability.complement_probability μ _ (hA i),hq i]

def twoPatterns : Fin 6 → Finset (Fin 4) := ![{0,1},{0,2},{0,3},{1,2},{1,3},{2,3}]

theorem all_pairs_listed (S : Finset (Fin 4)) :
    S.card=2 ↔ ∃ j,twoPatterns j=S := by
  have h : ∀ T:Finset (Fin 4),T.card=2 ↔ ∃ j,twoPatterns j=T := by decide
  exact h S

theorem distinct_listed_pairs : Function.Injective twoPatterns := by decide

theorem exactly_two_is_disjoint_union {Ω : Type*} (A : Fin 4 → Set Ω) :
    {omega | failureCount A omega=2}=⋃ j,failurePattern A (twoPatterns j) ∧
      Pairwise (fun j k => Disjoint (failurePattern A (twoPatterns j))
        (failurePattern A (twoPatterns k))) := by
  constructor
  · ext omega
    simp only [Set.mem_setOf_eq,Set.mem_iUnion,failureCount]
    rw [all_pairs_listed]
    constructor
    · rintro ⟨j,hj⟩
      exact ⟨j,(pattern_iff_failed_trials A _ omega).mpr hj.symm⟩
    · rintro ⟨j,hj⟩
      exact ⟨j,((pattern_iff_failed_trials A _ omega).mp hj).symm⟩
  · intro j k hjk
    apply Set.disjoint_left.mpr
    intro omega hj hk
    have he := ((pattern_iff_failed_trials A _ omega).mp hj).symm.trans
      ((pattern_iff_failed_trials A _ omega).mp hk)
    exact hjk (distinct_listed_pairs he)

theorem actual_four_trial_probabilities {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Fin 4 → Set Ω)
    (hA : ∀ i,MeasurableSet (A i)) (hind : iIndepSet A μ)
    (hq : ∀ i,μ.real (A i)=(1/10:ℝ)) :
    (∀ j,μ.real (failurePattern A (twoPatterns j))=(81/10000:ℝ)) ∧
      μ.real {omega | failureCount A omega=2}=(243/5000:ℝ) ∧
      μ.real {omega | failureCount A omega=0}=(6561/10000:ℝ) ∧
      μ.real {omega | 1≤failureCount A omega}=(3439/10000:ℝ) := by
  classical
  have hpair (j : Fin 6) : μ.real (failurePattern A (twoPatterns j))=(81/10000:ℝ) := by
    rw [(actual_pattern_probability μ 4 A hA hind (1/10) hq _).2]
    fin_cases j <;> norm_num [twoPatterns,Fin.prod_univ_succ]
  have hunion := exactly_two_is_disjoint_union A
  have htwo : μ.real {omega | failureCount A omega=2}=(243/5000:ℝ) := by
    rw [hunion.1,measureReal_iUnion_fintype hunion.2
      (fun j => (actual_pattern_probability μ 4 A hA hind (1/10) hq _).1)]
    simp only [hpair]
    norm_num
  have hzeroSet : {omega | failureCount A omega=0}=failurePattern A ∅ := by
    ext omega
    rw [pattern_iff_failed_trials]
    simp only [Set.mem_setOf_eq,failureCount,Finset.card_eq_zero]
  have hzero : μ.real {omega | failureCount A omega=0}=(6561/10000:ℝ) := by
    rw [hzeroSet,(actual_pattern_probability μ 4 A hA hind (1/10) hq ∅).2]
    norm_num [Fin.prod_univ_succ]
  have hcomp : {omega | 1≤failureCount A omega}={omega | failureCount A omega=0}ᶜ := by
    ext omega
    simp only [Set.mem_setOf_eq,Set.mem_compl_iff]
    omega
  have hatleast : μ.real {omega | 1≤failureCount A omega}=(3439/10000:ℝ) := by
    rw [hcomp,probReal_compl_eq_one_sub
      (hzeroSet ▸ (actual_pattern_probability μ 4 A hA hind (1/10) hq ∅).1),hzero]
    norm_num
  exact ⟨hpair,htwo,hzero,hatleast⟩

end SafeLearning.CompleteAppliedFailureCounts
