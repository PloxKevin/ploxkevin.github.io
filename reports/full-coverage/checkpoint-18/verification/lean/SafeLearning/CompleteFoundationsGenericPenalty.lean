import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Set
open scoped BigOperators
namespace SafeLearning.CompleteFoundationsGenericPenalty
variable {X I : Type*} [Fintype I]

def feasible (g : I → X → ℝ) : Set X := {x | ∀ i,g i x ≤ 0}
def lagrangian (f : X → ℝ) (g : I → X → ℝ) (multiplier : I → ℝ) (x : X) : ℝ :=
  f x+∑ i,multiplier i*g i x
def primalValues (f : X → ℝ) (g : I → X → ℝ) : Set ℝ := f '' feasible g
def primalValue (f : X → ℝ) (g : I → X → ℝ) : ℝ := sInf (primalValues f g)
def dualValue (f : X → ℝ) (g : I → X → ℝ) (multiplier : I → ℝ) : ℝ :=
  sInf (range (lagrangian f g multiplier))
def admissibleMultiplier (f : X → ℝ) (g : I → X → ℝ) (multiplier : I → ℝ) : Prop :=
  (∀ i,0 ≤ multiplier i) ∧ BddBelow (range (lagrangian f g multiplier))
def dualValues (f : X → ℝ) (g : I → X → ℝ) : Set ℝ :=
  {value | ∃ multiplier,admissibleMultiplier f g multiplier ∧ value=dualValue f g multiplier}
def dualSupremum (f : X → ℝ) (g : I → X → ℝ) : ℝ := sSup (dualValues f g)
def attainedOptimalMultiplier (f : X → ℝ) (g : I → X → ℝ) (multiplier : I → ℝ) : Prop :=
  admissibleMultiplier f g multiplier ∧ dualValue f g multiplier=dualSupremum f g
def exactPenalty (f : X → ℝ) (g : I → X → ℝ) (rho : ℝ) (x : X) : ℝ :=
  f x+rho*∑ i,max (g i x) 0

theorem actual_dual_value_lower_bounds_lagrangian (f : X → ℝ) (g : I → X → ℝ)
    (multiplier : I → ℝ) (hb : BddBelow (range (lagrangian f g multiplier))) (x : X) :
    dualValue f g multiplier ≤ lagrangian f g multiplier x :=
  csInf_le hb (mem_range_self x)

theorem actual_feasible_lagrangian_is_below_objective (f : X → ℝ) (g : I → X → ℝ)
    (multiplier : I → ℝ) (hm : ∀ i,0 ≤ multiplier i) (x : X) (hx : x ∈ feasible g) :
    lagrangian f g multiplier x ≤ f x := by
  have hs : (∑ i,multiplier i*g i x) ≤ 0 :=
    Finset.sum_nonpos (fun i _ => mul_nonpos_of_nonneg_of_nonpos (hm i) (hx i))
  dsimp [lagrangian]
  linarith

theorem actual_weak_duality (f : X → ℝ) (g : I → X → ℝ)
    (hfeasible : (feasible g).Nonempty) (multiplier : I → ℝ)
    (hm : admissibleMultiplier f g multiplier) : dualValue f g multiplier ≤ primalValue f g := by
  apply le_csInf (hfeasible.image f)
  rintro value ⟨x,hx,rfl⟩
  exact (actual_dual_value_lower_bounds_lagrangian f g multiplier hm.2 x).trans
    (actual_feasible_lagrangian_is_below_objective f g multiplier hm.1 x hx)

theorem actual_dual_supremum_weak_bound (f : X → ℝ) (g : I → X → ℝ)
    (hfeasible : (feasible g).Nonempty) (hdual : (dualValues f g).Nonempty) :
    dualSupremum f g ≤ primalValue f g := by
  apply csSup_le hdual
  rintro value ⟨multiplier,hm,rfl⟩
  exact actual_weak_duality f g hfeasible multiplier hm

theorem actual_strong_duality_and_attainment (f : X → ℝ) (g : I → X → ℝ)
    (multiplier : I → ℝ) (hm : attainedOptimalMultiplier f g multiplier)
    (hstrong : primalValue f g=dualSupremum f g) :
    dualValue f g multiplier=primalValue f g := hm.2.trans hstrong.symm

theorem actual_component_penalty_gap_nonnegative (rho multiplier violation : ℝ)
    (hm : 0 ≤ multiplier) (hr : multiplier ≤ rho) :
    0 ≤ rho*max violation 0-multiplier*violation := by
  by_cases hv : 0 ≤ violation
  · rw [max_eq_left hv]
    have hp := mul_nonneg (show 0 ≤ rho-multiplier by linarith) hv
    nlinarith
  · rw [max_eq_right (by linarith)]
    have hp := mul_nonneg hm (show 0 ≤ -violation by linarith)
    nlinarith

theorem actual_component_penalty_gap_positive (rho multiplier violation : ℝ)
    (hr : multiplier < rho) (hv : 0 < violation) :
    0 < rho*max violation 0-multiplier*violation := by
  rw [max_eq_left hv.le]
  have hp := mul_pos (sub_pos.mpr hr) hv
  nlinarith

theorem actual_sup_norm_weight_bounds_every_multiplier (multiplier : I → ℝ)
    (rho : ℝ) (hr : ‖multiplier‖ < rho) : ∀ i,multiplier i < rho := by
  intro i
  have hn : |multiplier i| ≤ ‖multiplier‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm multiplier i
  exact (le_abs_self (multiplier i)).trans_lt (hn.trans_lt hr)

theorem actual_penalty_lagrangian_gap (f : X → ℝ) (g : I → X → ℝ)
    (multiplier : I → ℝ) (rho : ℝ) (x : X) :
    exactPenalty f g rho x-lagrangian f g multiplier x=
      ∑ i,(rho*max (g i x) 0-multiplier i*g i x) := by
  simp only [exactPenalty,lagrangian,Finset.mul_sum,Finset.sum_sub_distrib]
  ring

theorem actual_penalty_dominates_lagrangian (f : X → ℝ) (g : I → X → ℝ)
    (multiplier : I → ℝ) (hm : ∀ i,0 ≤ multiplier i) (rho : ℝ)
    (hr : ‖multiplier‖ < rho) (x : X) :
    lagrangian f g multiplier x ≤ exactPenalty f g rho x := by
  have hs : 0 ≤ ∑ i,(rho*max (g i x) 0-multiplier i*g i x) :=
    Finset.sum_nonneg (fun i _ => actual_component_penalty_gap_nonnegative rho (multiplier i)
      (g i x) (hm i) (actual_sup_norm_weight_bounds_every_multiplier multiplier rho hr i).le)
  rw [← actual_penalty_lagrangian_gap] at hs
  linarith

theorem actual_infeasible_penalty_strictly_dominates_lagrangian (f : X → ℝ) (g : I → X → ℝ)
    (multiplier : I → ℝ) (hm : ∀ i,0 ≤ multiplier i) (rho : ℝ)
    (hr : ‖multiplier‖ < rho) (x : X) (hx : x ∉ feasible g) :
    lagrangian f g multiplier x < exactPenalty f g rho x := by
  classical
  have hex : ∃ i,0 < g i x := by
    change ¬ ∀ i,g i x ≤ 0 at hx
    push_neg at hx
    exact hx
  have hs : 0 < ∑ i,(rho*max (g i x) 0-multiplier i*g i x) := by
    apply Finset.sum_pos'
    · intro i _
      exact actual_component_penalty_gap_nonnegative rho (multiplier i) (g i x) (hm i)
        (actual_sup_norm_weight_bounds_every_multiplier multiplier rho hr i).le
    · obtain ⟨i,hi⟩ := hex
      exact ⟨i,Finset.mem_univ i,actual_component_penalty_gap_positive rho (multiplier i) (g i x)
        (actual_sup_norm_weight_bounds_every_multiplier multiplier rho hr i) hi⟩
  rw [← actual_penalty_lagrangian_gap] at hs
  linarith

theorem actual_feasible_penalty_equals_original (f : X → ℝ) (g : I → X → ℝ)
    (rho : ℝ) (x : X) (hx : x ∈ feasible g) : exactPenalty f g rho x=f x := by
  have hs : (∑ i,max (g i x) 0)=0 := Finset.sum_eq_zero (fun i _ => by
    rw [max_eq_right (hx i)])
  simp [exactPenalty,hs]

theorem actual_exact_penalty_optimal_value_and_feasibility (f : X → ℝ) (g : I → X → ℝ)
    (multiplier : I → ℝ) (hm : attainedOptimalMultiplier f g multiplier)
    (hstrong : primalValue f g=dualSupremum f g) (rho : ℝ) (hr : ‖multiplier‖ < rho) (x : X) :
    primalValue f g ≤ exactPenalty f g rho x ∧
    (x ∉ feasible g → primalValue f g < exactPenalty f g rho x) ∧
    (exactPenalty f g rho x=primalValue f g ↔ x ∈ feasible g ∧ f x=primalValue f g) := by
  have hd : primalValue f g ≤ lagrangian f g multiplier x := by
    rw [← actual_strong_duality_and_attainment f g multiplier hm hstrong]
    exact actual_dual_value_lower_bounds_lagrangian f g multiplier hm.1.2 x
  have hstrict : x ∉ feasible g → primalValue f g < exactPenalty f g rho x := fun hx =>
    hd.trans_lt (actual_infeasible_penalty_strictly_dominates_lagrangian f g multiplier hm.1.1 rho hr x hx)
  refine ⟨hd.trans (actual_penalty_dominates_lagrangian f g multiplier hm.1.1 rho hr x),hstrict,?_⟩
  constructor
  · intro he
    have hx : x ∈ feasible g := by
      by_contra hx
      have hs := hstrict hx
      linarith
    refine ⟨hx,?_⟩
    rw [actual_feasible_penalty_equals_original f g rho x hx] at he
    exact he
  · rintro ⟨hx,he⟩
    rw [actual_feasible_penalty_equals_original f g rho x hx,he]

theorem actual_exact_penalty_infimum_and_argmin (f : X → ℝ) (g : I → X → ℝ)
    (hfeasible : (feasible g).Nonempty) (multiplier : I → ℝ)
    (hm : attainedOptimalMultiplier f g multiplier)
    (hstrong : primalValue f g=dualSupremum f g) (rho : ℝ) (hr : ‖multiplier‖ < rho) :
    sInf (range (exactPenalty f g rho))=primalValue f g ∧
    {x | exactPenalty f g rho x=sInf (range (exactPenalty f g rho))}=
      {x | x ∈ feasible g ∧ f x=primalValue f g} := by
  have hb : BddBelow (range (exactPenalty f g rho)) := by
    refine ⟨primalValue f g,?_⟩
    rintro value ⟨x,rfl⟩
    exact (actual_exact_penalty_optimal_value_and_feasibility f g multiplier hm hstrong rho hr x).1
  have hn : (range (exactPenalty f g rho)).Nonempty := by
    obtain ⟨x,hx⟩ := hfeasible
    exact ⟨_,mem_range_self x⟩
  have he : sInf (range (exactPenalty f g rho))=primalValue f g := by
    apply le_antisymm
    · apply le_csInf (hfeasible.image f)
      rintro value ⟨x,hx,rfl⟩
      have hi := csInf_le hb (mem_range_self x)
      simpa only [actual_feasible_penalty_equals_original f g rho x hx] using hi
    · apply le_csInf hn
      rintro value ⟨x,rfl⟩
      exact (actual_exact_penalty_optimal_value_and_feasibility f g multiplier hm hstrong rho hr x).1
  refine ⟨he,?_⟩
  ext x
  rw [he]
  exact (actual_exact_penalty_optimal_value_and_feasibility f g multiplier hm hstrong rho hr x).2.2

end SafeLearning.CompleteFoundationsGenericPenalty
