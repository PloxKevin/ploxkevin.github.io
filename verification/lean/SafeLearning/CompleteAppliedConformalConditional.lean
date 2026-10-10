import SafeLearning.CompleteAppliedConformalConsequences

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedConformalConditional
open MeasureTheory ProbabilityTheory Set Function
open scoped BigOperators
open SafeLearning.CompleteAppliedConformalRanks
open SafeLearning.CompleteAppliedConformalConsequences

abbrev Permutation := Equiv.Perm (Fin 20)
local instance : MeasurableSpace Permutation := ⊤
local instance : DiscreteMeasurableSpace Permutation := ⟨fun _ => trivial⟩

def permutationLaw : Measure Permutation := (PMF.uniformOfFintype Permutation).toMeasure
instance : IsProbabilityMeasure permutationLaw := by unfold permutationLaw;infer_instance

def scoreVector (permutation : Permutation) : Fin 20 → ℝ :=
  fun i => (permutation i).val

def scoreLaw : Measure (Fin 20 → ℝ) := permutationLaw.map scoreVector
instance : IsProbabilityMeasure scoreLaw := by
  unfold scoreLaw
  infer_instance

def reindexPermutation (e : Permutation) : Equiv.Perm Permutation where
  toFun p := e.trans p
  invFun p := e.symm.trans p
  left_inv p := by ext i;simp
  right_inv p := by ext i;simp

theorem actual_uniform_permutations_are_invariant_under_reindexing (e : Permutation) :
    permutationLaw.map (reindexPermutation e)=permutationLaw := by
  have hp : (PMF.uniformOfFintype Permutation).map (reindexPermutation e)=
      PMF.uniformOfFintype Permutation := by
    ext p
    rw [PMF.map_apply,tsum_fintype]
    have he (q : Permutation) : p=reindexPermutation e q ↔
        q=(reindexPermutation e).symm p := by
      constructor
      · intro h;rw [h];simp
      · intro h;rw [h];simp
    simp_rw [he]
    simp
  rw [permutationLaw,PMF.toMeasure_map _ _ (measurable_of_countable _),hp]

theorem actual_permuted_score_model_is_tie_free (p : Permutation) :
    Injective (scoreVector p) := by
  intro i j he
  apply p.injective
  apply Fin.ext
  change (p i).val=(p j).val
  change ((p i).val:ℝ)=((p j).val:ℝ) at he
  exact_mod_cast he

theorem actual_permuted_score_model_is_exchangeable : exchangeable scoreLaw := by
  intro e
  have hm : Measurable scoreVector := measurable_of_countable _
  have he : permutedScores e ∘ scoreVector=scoreVector ∘ reindexPermutation e := rfl
  unfold scoreLaw
  rw [Measure.map_map (actual_permuted_scores_are_measurable e) hm,he,
    ←Measure.map_map hm (measurable_of_countable _),
    actual_uniform_permutations_are_invariant_under_reindexing]

theorem actual_score_law_is_almost_surely_tie_free :
    ∀ᵐ scores ∂scoreLaw,Injective scores := by
  rw [scoreLaw,ae_map_iff (measurable_of_countable _).aemeasurable]
  · exact Filter.Eventually.of_forall actual_permuted_score_model_is_tie_free
  · have hm : MeasurableSet {scores : Fin 20 → ℝ | Injective scores} := by
      have he : {scores : Fin 20 → ℝ | Injective scores}=
          ⋂ i : Fin 20,⋂ j : Fin 20,{scores | i=j ∨ scores i≠scores j} := by
        ext scores
        simp only [Set.mem_ofPred_eq,Set.mem_iInter]
        constructor
        · intro hi i j;by_cases hij : i=j
          · exact Or.inl hij
          · exact Or.inr (fun he => hij (hi he))
        · intro hi i j he;rcases hi i j with hij|hij
          · exact hij
          · exact False.elim (hij he)
      rw [he]
      apply MeasurableSet.iInter
      intro i
      apply MeasurableSet.iInter
      intro j
      by_cases h : i=j
      · simp [h]
      · have hh := (measurableSet_eq_fun (show Measurable (fun scores : Fin 20 → ℝ => scores i) from measurable_pi_apply i)
          (show Measurable (fun scores : Fin 20 → ℝ => scores j) from measurable_pi_apply j)).compl
        convert hh using 1
        ext scores
        simp only [Set.mem_ofPred_eq,Set.mem_compl_iff,h,false_or]
    exact hm

def observedCalibration : Set Permutation :=
  {p | ∀ i : Fin 19,scoreVector p i.castSucc=(i.val:ℝ)}

theorem actual_calibration_observation_identifies_the_remaining_future_score :
    observedCalibration={Equiv.refl (Fin 20)} := by
  ext p
  simp only [observedCalibration,Set.mem_ofPred_eq,Set.mem_singleton_iff]
  constructor
  · intro h
    have hfix (i : Fin 19) : p i.castSucc=i.castSucc := by
      apply Fin.ext
      change (p i.castSucc).val=i.val
      have hi := h i
      change ((p i.castSucc).val:ℝ)=(i.val:ℝ) at hi
      exact_mod_cast hi
    have hlast : p (Fin.last 19)=Fin.last 19 := by
      by_contra hn
      have hv : (p (Fin.last 19)).val<19 := by
        have hb := (p (Fin.last 19)).isLt
        have he : (p (Fin.last 19)).val≠19 := fun he => hn (Fin.ext he)
        omega
      let i : Fin 19 := ⟨(p (Fin.last 19)).val,hv⟩
      have hi : i.castSucc=p (Fin.last 19) := Fin.ext rfl
      have he : p i.castSucc=p (Fin.last 19) := (hfix i).trans hi
      have hc := congrArg Fin.val (p.injective he)
      change i.val=19 at hc
      omega
    apply Equiv.ext
    intro i
    change p i=i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact hlast
    · exact hfix j
  · intro h
    subst p
    intro i
    rfl

theorem actual_observed_calibration_has_positive_probability :
    0<permutationLaw.real observedCalibration := by
  rw [actual_calibration_observation_identifies_the_remaining_future_score]
  simp only [permutationLaw,Measure.real,PMF.toMeasure_apply_singleton (PMF.uniformOfFintype Permutation) (Equiv.refl (Fin 20)) MeasurableSet.of_discrete,
    PMF.uniformOfFintype_apply,ENNReal.toReal_inv,ENNReal.toReal_natCast]
  have hp : 0<Fintype.card Permutation := Fintype.card_pos_iff.mpr inferInstance
  exact inv_pos.mpr (by exact_mod_cast hp)

def accepted : Set Permutation := scoreVector ⁻¹' actualAcceptance

theorem actual_fixed_observed_calibration_conditional_coverage_is_zero :
    (cond permutationLaw observedCalibration).real accepted=0 := by
  have hi : scoreVector (Equiv.refl (Fin 20))∉actualAcceptance := by
    change ¬scoreVector (Equiv.refl (Fin 20)) (Fin.last 19) ≤ calibrationThreshold (scoreVector (Equiv.refl (Fin 20)))
    rw [actual_acceptance_is_exactly_overall_rank_at_most_eighteen _
      (actual_permuted_score_model_is_tie_free _)]
    norm_num [rankNat,scoreVector,Fin.card_filter_val_lt]
  have he : observedCalibration ∩ accepted=∅ := by
    rw [actual_calibration_observation_identifies_the_remaining_future_score]
    ext p
    simp only [Set.mem_inter_iff,Set.mem_singleton_iff,accepted,Set.mem_preimage,
      Set.mem_empty_iff_false,iff_false,not_and]
    intro h
    subst p
    exact hi
  change ((cond permutationLaw observedCalibration) accepted).toReal=0
  rw [cond_apply (by measurability),he]
  simp

theorem actual_marginal_conformal_coverage_is_point_nine :
    permutationLaw.real accepted=(0.9:ℝ) := by
  have he : accepted=scoreVector ⁻¹' rankBelowEvent (Fin.last 19) 18 := by
    ext p
    exact actual_acceptance_is_exactly_overall_rank_at_most_eighteen _
      (actual_permuted_score_model_is_tie_free p)
  have hm : MeasurableSet (rankBelowEvent (Fin.last 19) 18) :=
    measurableSet_lt (actual_rank_is_measurable _) measurable_const
  rw [he,←map_measureReal_apply (measurable_of_countable _) hm]
  change scoreLaw.real (rankBelowEvent (Fin.last 19) 18)=(0.9:ℝ)
  rw [actual_rank_below_event_probability _ actual_permuted_score_model_is_exchangeable
    actual_score_law_is_almost_surely_tie_free _ _ (by norm_num)]
  norm_num

end SafeLearning.CompleteAppliedConformalConditional
