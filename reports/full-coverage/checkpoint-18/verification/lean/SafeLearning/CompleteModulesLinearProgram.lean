import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Set
namespace SafeLearning.CompleteModulesLinearProgram

def actualNonnegativeDomainAffineInfimum (constant firstCoefficient secondCoefficient : ℝ) : EReal :=
  sInf {value | ∃ first second : ℝ,0 ≤ first ∧ 0 ≤ second ∧
    value=((constant+firstCoefficient*first+secondCoefficient*second : ℝ) : EReal)}

theorem actual_nonnegative_affine_domain_has_the_true_infimum
    (constant firstCoefficient secondCoefficient : ℝ) :
    actualNonnegativeDomainAffineInfimum constant firstCoefficient secondCoefficient=
      if 0 ≤ firstCoefficient ∧ 0 ≤ secondCoefficient then (constant : EReal) else ⊥ := by
  by_cases h : 0 ≤ firstCoefficient ∧ 0 ≤ secondCoefficient
  · rw [ite_eq_left h]
    apply le_antisymm
    · exact sInf_le ⟨0,0,by norm_num,by norm_num,by norm_num⟩
    · apply le_sInf
      rintro value ⟨first,second,hfirst,hsecond,rfl⟩
      apply EReal.coe_le_coe
      nlinarith [mul_nonneg h.1 hfirst,mul_nonneg h.2 hsecond]
  · rw [ite_eq_right h]
    apply (EReal.eq_bot_iff_forall_lt _).mpr
    intro bound
    rcases lt_or_ge firstCoefficient 0 with hfirst | hfirst
    · let first := max 0 ((bound-constant-1)/firstCoefficient)
      have hp : 0 ≤ first := le_max_left _ _
      have hl : firstCoefficient*first ≤ bound-constant-1 := by
        have hg := mul_le_mul_of_nonpos_left
          (le_max_right 0 ((bound-constant-1)/firstCoefficient)) (le_of_lt hfirst)
        have he : firstCoefficient*((bound-constant-1)/firstCoefficient)=bound-constant-1 := by
          field_simp [ne_of_lt hfirst]
        rw [he] at hg
        exact hg
      have hi : actualNonnegativeDomainAffineInfimum constant firstCoefficient secondCoefficient ≤
          ((constant+firstCoefficient*first+secondCoefficient*0 : ℝ) : EReal) :=
        sInf_le ⟨first,0,hp,le_rfl,rfl⟩
      apply lt_of_le_of_lt hi
      apply EReal.coe_lt_coe_iff.mpr
      linarith
    · have hsecond : secondCoefficient<0 := by exact lt_of_not_ge (fun hs => h ⟨hfirst,hs⟩)
      let second := max 0 ((bound-constant-1)/secondCoefficient)
      have hp : 0 ≤ second := le_max_left _ _
      have hl : secondCoefficient*second ≤ bound-constant-1 := by
        have hg := mul_le_mul_of_nonpos_left
          (le_max_right 0 ((bound-constant-1)/secondCoefficient)) (le_of_lt hsecond)
        have he : secondCoefficient*((bound-constant-1)/secondCoefficient)=bound-constant-1 := by
          field_simp [ne_of_lt hsecond]
        rw [he] at hg
        exact hg
      have hi : actualNonnegativeDomainAffineInfimum constant firstCoefficient secondCoefficient ≤
          ((constant+firstCoefficient*0+secondCoefficient*second : ℝ) : EReal) :=
        sInf_le ⟨0,second,le_rfl,hp,rfl⟩
      apply lt_of_le_of_lt hi
      apply EReal.coe_lt_coe_iff.mpr
      linarith

def actualLPPrimalFeasible (first second : ℝ) : Prop :=
  0 ≤ first ∧ 0 ≤ second ∧ 4 ≤ first+second ∧ 6 ≤ first+3*second
def actualLPDualFeasible (firstPrice secondPrice : ℝ) : Prop :=
  0 ≤ firstPrice ∧ 0 ≤ secondPrice ∧ firstPrice+secondPrice ≤ 2 ∧ firstPrice+3*secondPrice ≤ 3
def actualLPLagrangian (first second firstPrice secondPrice : ℝ) : ℝ :=
  2*first+3*second+firstPrice*(4-first-second)+secondPrice*(6-first-3*second)
def actualLPDualFunction (firstPrice secondPrice : ℝ) : EReal :=
  sInf {value | ∃ first second : ℝ,0 ≤ first ∧ 0 ≤ second ∧
    value=((actualLPLagrangian first second firstPrice secondPrice : ℝ) : EReal)}

theorem actual_source_lp_lagrangian_expansion (first second firstPrice secondPrice : ℝ) :
    actualLPLagrangian first second firstPrice secondPrice=
      4*firstPrice+6*secondPrice+(2-firstPrice-secondPrice)*first+
        (3-firstPrice-3*secondPrice)*second := by
  unfold actualLPLagrangian
  ring

theorem actual_source_lp_dual_function_true_extended_infimum (firstPrice secondPrice : ℝ) :
    actualLPDualFunction firstPrice secondPrice=
      if firstPrice+secondPrice ≤ 2 ∧ firstPrice+3*secondPrice ≤ 3 then
        ((4*firstPrice+6*secondPrice : ℝ) : EReal) else ⊥ := by
  have he : actualLPDualFunction firstPrice secondPrice=
      actualNonnegativeDomainAffineInfimum (4*firstPrice+6*secondPrice)
        (2-firstPrice-secondPrice) (3-firstPrice-3*secondPrice) := by
    unfold actualLPDualFunction actualNonnegativeDomainAffineInfimum
    simp only [actual_source_lp_lagrangian_expansion]
  rw [he,actual_nonnegative_affine_domain_has_the_true_infimum]
  have hc : (0 ≤ 2-firstPrice-secondPrice ∧ 0 ≤ 3-firstPrice-3*secondPrice) ↔
      (firstPrice+secondPrice ≤ 2 ∧ firstPrice+3*secondPrice ≤ 3) := by
    constructor <;> rintro ⟨ha,hb⟩ <;> constructor <;> linarith
  simp only [hc]

theorem actual_source_lp_weak_duality (first second firstPrice secondPrice : ℝ)
    (hprimal : actualLPPrimalFeasible first second) (hdual : actualLPDualFeasible firstPrice secondPrice) :
    4*firstPrice+6*secondPrice ≤ 2*first+3*second := by
  rcases hprimal with ⟨hf,hs,hone,htwo⟩
  rcases hdual with ⟨hp,hq,hleone,hletwo⟩
  have ha := mul_nonneg hp (show 0 ≤ first+second-4 by linarith)
  have hb := mul_nonneg hq (show 0 ≤ first+3*second-6 by linarith)
  have hc := mul_nonneg hf (show 0 ≤ 2-firstPrice-secondPrice by linarith)
  have hd := mul_nonneg hs (show 0 ≤ 3-firstPrice-3*secondPrice by linarith)
  nlinarith

theorem actual_source_lp_primal_unique_global_minimum (first second : ℝ)
    (hprimal : actualLPPrimalFeasible first second) :
    9 ≤ 2*first+3*second ∧ (2*first+3*second=9 ↔ first=3 ∧ second=1) := by
  rcases hprimal with ⟨hf,hs,hfirst,hsecond⟩
  constructor
  · linarith
  · constructor
    · intro he
      constructor <;> linarith
    · rintro ⟨rfl,rfl⟩;norm_num

theorem actual_source_lp_dual_unique_global_maximum (firstPrice secondPrice : ℝ)
    (hdual : actualLPDualFeasible firstPrice secondPrice) :
    4*firstPrice+6*secondPrice ≤ 9 ∧
      (4*firstPrice+6*secondPrice=9 ↔ firstPrice=3/2 ∧ secondPrice=1/2) := by
  rcases hdual with ⟨hf,hs,hfirst,hsecond⟩
  constructor
  · linarith
  · constructor
    · intro he
      constructor <;> linarith
    · rintro ⟨rfl,rfl⟩;norm_num

theorem actual_source_lp_optimal_points_zero_gap_and_complementarity :
    actualLPPrimalFeasible 3 1 ∧ actualLPDualFeasible (3/2) (1/2) ∧
    (2*3+3*1:ℝ)=9 ∧ (4*(3/2)+6*(1/2):ℝ)=9 ∧
    (3/2:ℝ)*(4-3-1)=0 ∧ (1/2:ℝ)*(6-3-3*1)=0 ∧
    (2-(3/2)-(1/2):ℝ)=0 ∧ (3-(3/2)-3*(1/2):ℝ)=0 ∧
    (0:ℝ)<3 ∧ (0:ℝ)<1 ∧ (0:ℝ)<3/2 ∧ (0:ℝ)<1/2 := by
  norm_num [actualLPPrimalFeasible,actualLPDualFeasible]

theorem actual_source_optimal_prices_make_every_domain_point_a_lagrangian_minimizer
    (first second : ℝ) : actualLPLagrangian first second (3/2) (1/2)=9 := by
  rw [actual_source_lp_lagrangian_expansion]
  ring

theorem actual_source_lp_reported_feasible_points_and_values :
    actualLPPrimalFeasible 6 0 ∧ actualLPPrimalFeasible 0 4 ∧
    (2*6+3*0:ℝ)=12 ∧ (2*0+3*4:ℝ)=12 ∧
    actualLPDualFeasible 2 0 ∧ actualLPDualFeasible 0 1 ∧ actualLPDualFeasible 0 0 ∧
    (4*2+6*0:ℝ)=8 ∧ (4*0+6*1:ℝ)=6 ∧ (4*0+6*0:ℝ)=0 := by
  norm_num [actualLPPrimalFeasible,actualLPDualFeasible]

theorem actual_general_rhs_primal_optimum_and_price_values (firstRequirement secondRequirement : ℝ)
    (hfirst : firstRequirement ≤ secondRequirement) (hsecond : secondRequirement ≤ 3*firstRequirement) :
    let first := (3*firstRequirement-secondRequirement)/2
    let second := (secondRequirement-firstRequirement)/2
    0 ≤ first ∧ 0 ≤ second ∧ first+second=firstRequirement ∧
      first+3*second=secondRequirement ∧
      2*first+3*second=(3/2)*firstRequirement+(1/2)*secondRequirement ∧
      ∀ otherFirst otherSecond : ℝ,0 ≤ otherFirst → 0 ≤ otherSecond →
        firstRequirement ≤ otherFirst+otherSecond → secondRequirement ≤ otherFirst+3*otherSecond →
          2*first+3*second ≤ 2*otherFirst+3*otherSecond := by
  dsimp only
  refine ⟨by linarith,by linarith,by ring,by ring,by ring,?_⟩
  intro otherFirst otherSecond _ _ hone htwo
  linarith

theorem actual_source_one_unit_requirement_price_changes :
    ((3/2)*5+(1/2)*6:ℝ)-9=3/2 ∧
      ((3/2)*4+(1/2)*7:ℝ)-9=1/2 ∧
      (5:ℝ) ≤ 6 ∧ (6:ℝ) ≤ 3*5 ∧ (4:ℝ) ≤ 7 ∧ (7:ℝ) ≤ 3*4 := by
  norm_num

end SafeLearning.CompleteModulesLinearProgram
