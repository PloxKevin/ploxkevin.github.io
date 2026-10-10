import SafeLearning.CompleteAppliedFailureCounts
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedBinomialModel
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open SafeLearning.CompleteAppliedFailureCounts

theorem actual_pattern_card_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (A : Fin n → Set Ω)
    (hA : ∀ i,MeasurableSet (A i)) (hind : iIndepSet A μ)
    (q : ℝ) (hq : ∀ i,μ.real (A i)=q) (S : Finset (Fin n)) :
    μ.real (failurePattern A S)=q^S.card*(1-q)^(n-S.card) := by
  classical
  rw [(actual_pattern_probability μ n A hA hind q hq S).2,Finset.prod_ite]
  have he : Finset.univ.filter (fun i:Fin n => i∈S)=S := by ext i;simp
  have hc : Finset.univ.filter (fun i:Fin n => i∉S)=Sᶜ := by ext i;simp
  rw [he,hc,Finset.prod_const,Finset.prod_const]
  simp only [Finset.card_compl,Fintype.card_fin]

theorem count_event_is_pattern_union {Ω : Type*} {n : ℕ}
    (A : Fin n → Set Ω) (k : ℕ) :
    {omega | failureCount A omega=k}=
      ⋃ S∈Finset.univ.powersetCard k,failurePattern A S := by
  classical
  ext omega
  simp only [Set.mem_setOf_eq,Set.mem_iUnion,Finset.mem_powersetCard,
    Finset.subset_univ,true_and,pattern_iff_failed_trials,failureCount]
  constructor
  · intro h
    exact ⟨failedTrials A omega,h,rfl⟩
  · rintro ⟨S,hS,he⟩
    simpa only [he] using hS

theorem patterns_pairwise_disjoint {Ω : Type*} {n : ℕ} (A : Fin n → Set Ω)
    (T : Finset (Finset (Fin n))) :
    Set.PairwiseDisjoint (T: Set (Finset (Fin n))) (failurePattern A) := by
  intro S hS R hR hne
  apply Set.disjoint_left.mpr
  intro omega hs hr
  exact hne (((pattern_iff_failed_trials A S omega).mp hs).symm.trans
    ((pattern_iff_failed_trials A R omega).mp hr))

/-- A count of genuinely independent equal-probability events has the binomial masses. -/
theorem actual_binomial_count_mass {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (A : Fin n → Set Ω)
    (hA : ∀ i,MeasurableSet (A i)) (hind : iIndepSet A μ)
    (q : ℝ) (hq : ∀ i,μ.real (A i)=q) (k : ℕ) :
    μ.real {omega | failureCount A omega=k}=
      (n.choose k:ℝ)*q^k*(1-q)^(n-k) := by
  classical
  rw [count_event_is_pattern_union,
    measureReal_biUnion_finset (patterns_pairwise_disjoint A _)
      (fun S hS => (actual_pattern_probability μ n A hA hind q hq S).1)]
  have he : (∑ S∈Finset.univ.powersetCard k,μ.real (failurePattern A S))=
      ∑ S∈(Finset.univ:Finset (Fin n)).powersetCard k,q^k*(1-q)^(n-k) := by
    apply Finset.sum_congr rfl
    intro S hS
    rw [actual_pattern_card_probability μ n A hA hind q hq S,
      (Finset.mem_powersetCard.mp hS).2]
  rw [he]
  simp only [Finset.sum_const,Finset.card_powersetCard,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul]
  ring

theorem failure_count_measurable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (A : Fin n → Set Ω) (hA : ∀ i,MeasurableSet (A i)) : Measurable (failureCount A) := by
  classical
  have hm : Measurable (fun omega => ∑ i:Fin n,if omega∈A i then (1:ℕ) else 0) :=
    Finset.measurable_sum Finset.univ (fun i _ =>
      Measurable.ite (hA i) measurable_const measurable_const)
  have he : (fun omega => ∑ i:Fin n,if omega∈A i then (1:ℕ) else 0)=failureCount A := by
    funext omega
    simp only [Finset.sum_boole,failureCount,failedTrials,Nat.cast_id]
  exact he ▸ hm

theorem actual_choose_factorial_formula (n k : ℕ) (hk : k≤n) :
    (n.choose k:ℝ)=(n.factorial:ℝ)/((k.factorial:ℝ)*((n-k).factorial:ℝ)) := by
  have hf : (n.choose k:ℝ)*(k.factorial:ℝ)*((n-k).factorial:ℝ)=(n.factorial:ℝ) :=
    by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  have hkpos : (k.factorial:ℝ)≠0 := by positivity
  have hnpos : ((n-k).factorial:ℝ)≠0 := by positivity
  apply (eq_div_iff (mul_ne_zero hkpos hnpos)).mpr
  nlinarith [hf]

/-- The count law is derived from independence, rather than assumed to be binomial. -/
theorem actual_count_has_binomial_law {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (A : Fin n → Set Ω)
    (hA : ∀ i,MeasurableSet (A i)) (hind : iIndepSet A μ)
    (p : unitInterval) (hp : ∀ i,μ.real (A i)=(p:ℝ)) :
    HasLaw (failureCount A) (binomial n p) μ := by
  have hm := failure_count_measurable A hA
  refine ⟨hm.aemeasurable,?_⟩
  letI : IsProbabilityMeasure (μ.map (failureCount A)) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
  apply Measure.ext_of_measureReal_singleton
  intro k
  rw [map_measureReal_apply hm (measurableSet_singleton k),binomial_real_singleton]
  exact actual_binomial_count_mass μ n A hA hind p hp k

theorem real_count_is_sum_of_indicators {Ω : Type*} {n : ℕ}
    (A : Fin n → Set Ω) :
    (fun omega => (failureCount A omega:ℝ))=
      ∑ i:Fin n,(A i).indicator (fun _ => (1:ℝ)) := by
  classical
  funext omega
  simp [failureCount,failedTrials,Set.indicator,Finset.sum_boole]

theorem actual_indicator_mean_and_variance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Set Ω) (hA : MeasurableSet A) :
    (∫ omega,A.indicator (fun _ => (1:ℝ)) omega ∂μ)=μ.real A ∧
      variance (A.indicator (fun _ => (1:ℝ))) μ=μ.real A*(1-μ.real A) := by
  have hLp : MemLp (A.indicator (fun _ => (1:ℝ))) 2 μ :=
    (memLp_const (1:ℝ)).indicator hA
  have hs : (A.indicator (fun _ => (1:ℝ)))^2=A.indicator (fun _ => (1:ℝ)) := by
    classical
    funext omega
    by_cases ha : omega∈A <;> simp [Set.indicator,ha]
  have hi : (∫ omega,A.indicator (fun _ => (1:ℝ)) omega ∂μ)=μ.real A := by
    simpa using integral_indicator_const (μ := μ) (1:ℝ) hA
  refine ⟨hi,?_⟩
  rw [variance_eq_sub hLp,hs,hi]
  ring

theorem actual_binomial_count_mean_and_variance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (A : Fin n → Set Ω)
    (hA : ∀ i,MeasurableSet (A i)) (hind : iIndepSet A μ)
    (q : ℝ) (hq : ∀ i,μ.real (A i)=q) :
    (∫ omega,(failureCount A omega:ℝ) ∂μ)=(n:ℝ)*q ∧
      variance (fun omega => (failureCount A omega:ℝ)) μ=(n:ℝ)*q*(1-q) := by
  have hLp (i : Fin n) : MemLp ((A i).indicator (fun _ => (1:ℝ))) 2 μ :=
    (memLp_const (1:ℝ)).indicator (hA i)
  have hi : iIndepFun (fun i:Fin n => (A i).indicator (fun _ => (1:ℝ))) μ :=
    hind.iIndepFun_indicator
  have hm (i : Fin n) : (∫ omega,(A i).indicator (fun _ => (1:ℝ)) omega ∂μ)=q := by
    rw [(actual_indicator_mean_and_variance μ (A i) (hA i)).1,hq i]
  have hv (i : Fin n) : variance ((A i).indicator (fun _ => (1:ℝ))) μ=q*(1-q) := by
    rw [(actual_indicator_mean_and_variance μ (A i) (hA i)).2,hq i]
  rw [real_count_is_sum_of_indicators]
  constructor
  · change (∫ omega,(∑ i:Fin n,(A i).indicator (fun _ => (1:ℝ))) omega ∂μ)=_
    simp only [Finset.sum_apply]
    rw [integral_finsetSum _ (fun i _ => (hLp i).integrable (by norm_num))]
    simp only [hm,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  · rw [IndepFun.variance_sum (fun i _ => hLp i)
      (fun i _ j _ hij => hi.indepFun hij)]
    simp only [hv,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    ring

end SafeLearning.CompleteAppliedBinomialModel
