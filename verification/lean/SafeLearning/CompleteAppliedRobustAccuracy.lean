import SafeLearning.CompleteModulesGeneralMargin

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators
namespace SafeLearning.CompleteAppliedRobustAccuracy
open CompleteModulesGeneralMargin

def sourceRadius : ℝ := 1/(2*Real.sqrt 2)

theorem actual_margin_one_gain_two_radius_has_the_printed_rounding :
    |sourceRadius-(353553/1000000:ℝ)|<1/2000000 ∧ 0<sourceRadius := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hp := Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)
  have hd : 0<2*Real.sqrt 2 := by positivity
  have hl : (14142135/10000000:ℝ)<Real.sqrt 2 := by nlinarith
  have hu : Real.sqrt 2<(14142136/10000000:ℝ) := by nlinarith
  refine ⟨?_,by unfold sourceRadius;positivity⟩
  rw [abs_lt]
  have hb : (3535525/10000000:ℝ)<sourceRadius ∧ sourceRadius<(3535535/10000000:ℝ) := by
    constructor
    · rw [sourceRadius,lt_div_iff₀ hd];nlinarith
    · rw [sourceRadius,div_lt_iff₀ hd];nlinarith
  constructor <;> linarith [hb.1,hb.2]

theorem actual_margin_one_gain_two_certifies_every_strictly_smaller_perturbation
    {O X : Type*} [Fintype O] [DecidableEq O] [PseudoMetricSpace X]
    (logits : X→O→ℝ) (winner : O) (original perturbed : X)
    (hcompetitors : (Finset.univ.erase winner).Nonempty)
    (hmargin : actualLogitMargin logits winner original (Finset.univ.erase winner) hcompetitors=1)
    (hlogits : ∀x y,‖WithLp.toLp 2 (logits x-logits y)‖≤(2:ℝ)*dist x y)
    (hperturbation : dist original perturbed<sourceRadius) :
    ∀other,other≠winner → logits perturbed other<logits perturbed winner := by
  apply actual_arbitrary_global_margin_radius_preserves_unique_prediction logits winner original perturbed 2
    (by norm_num) hcompetitors hlogits
  simpa only [hmargin,sourceRadius,mul_comm] using hperturbation

def robustCorrect {I X C : Type*} [PseudoMetricSpace X]
    (inputs : I→X) (labels : I→C) (classifier : X→C) (radius : ℝ) (index : I) : Prop :=
  ∀point,dist (inputs index) point≤radius → classifier point=labels index

theorem actual_certificates_and_attack_witnesses_bound_the_true_robust_count
    {I X C : Type*} [Fintype I] [DecidableEq I] [PseudoMetricSpace X]
    (inputs : I→X) (labels : I→C) (classifier : X→C) (radius : ℝ) (hradius : 0≤radius)
    (clean certified attacked : Finset I)
    (hclean : ∀index,index∈clean ↔ classifier (inputs index)=labels index)
    (hcertificate : ∀index∈certified,robustCorrect inputs labels classifier radius index)
    (hattackclean : attacked⊆clean)
    (hattack : ∀index∈attacked,∃point,dist (inputs index) point≤radius ∧ classifier point≠labels index) :
    ∃robust : Finset I,
      (∀index,index∈robust ↔ robustCorrect inputs labels classifier radius index) ∧
      certified.card≤robust.card ∧ robust.card≤clean.card-attacked.card := by
  classical
  let robust := Finset.univ.filter (robustCorrect inputs labels classifier radius)
  have hrobust : ∀index,index∈robust ↔ robustCorrect inputs labels classifier radius index := by
    intro index;simp [robust]
  have hc : certified⊆robust := by
    intro index hindex;exact (hrobust index).mpr (hcertificate index hindex)
  have hu : robust⊆clean\attacked := by
    intro index hindex
    have hr := (hrobust index).mp hindex
    apply Finset.mem_sdiff.mpr
    constructor
    · exact (hclean index).mpr (hr (inputs index) (by simpa using hradius))
    · intro hattacked
      obtain ⟨point,hpoint,hwrong⟩ := hattack index hattacked
      exact hwrong (hr point hpoint)
  refine ⟨robust,hrobust,Finset.card_le_card hc,?_⟩
  have hcard := Finset.card_le_card hu
  rw [Finset.card_sdiff_of_subset hattackclean] at hcard
  exact hcard

theorem actual_source_hundred_example_robust_accuracy_is_between_half_and_seven_tenths
    {X C : Type*} [PseudoMetricSpace X]
    (inputs : Fin 100→X) (labels : Fin 100→C) (classifier : X→C)
    (radius : ℝ) (hradius : 0≤radius) (clean certified attacked : Finset (Fin 100))
    (hclean : ∀index,index∈clean ↔ classifier (inputs index)=labels index)
    (hcertificate : ∀index∈certified,robustCorrect inputs labels classifier radius index)
    (hattackclean : attacked⊆clean)
    (hattack : ∀index∈attacked,∃point,dist (inputs index) point≤radius ∧ classifier point≠labels index)
    (hcleanCount : clean.card=80) (hcertifiedCount : certified.card=50) (hattackCount : attacked.card=10) :
    ∃robust : Finset (Fin 100),
      (∀index,index∈robust ↔ robustCorrect inputs labels classifier radius index) ∧
      (1/2:ℝ)≤(robust.card:ℝ)/100 ∧ (robust.card:ℝ)/100≤7/10 := by
  obtain ⟨robust,hr,hl,hu⟩ := actual_certificates_and_attack_witnesses_bound_the_true_robust_count
    inputs labels classifier radius hradius clean certified attacked hclean hcertificate hattackclean hattack
  rw [hcertifiedCount] at hl
  rw [hcleanCount,hattackCount] at hu
  have hlreal : (50:ℝ)≤(robust.card:ℝ) := by exact_mod_cast hl
  have hureal : (robust.card:ℝ)≤70 := by exact_mod_cast hu
  refine ⟨robust,hr,?_,?_⟩ <;> linarith

def undiscoveredFailureClassifier (point : ℝ) : Fin 2 := if point≤1/2 then 0 else 1

theorem actual_unsuccessful_attack_at_the_clean_point_does_not_certify_robust_correctness :
    undiscoveredFailureClassifier 0=0 ∧
      ¬robustCorrect (fun _ : Unit=>(0:ℝ)) (fun _ : Unit=>(0:Fin 2))
        undiscoveredFailureClassifier 1 () := by
  refine ⟨by norm_num [undiscoveredFailureClassifier],?_⟩
  intro h
  have hwrong := h 1 (by norm_num [Real.dist_eq])
  norm_num [undiscoveredFailureClassifier] at hwrong

end SafeLearning.CompleteAppliedRobustAccuracy
