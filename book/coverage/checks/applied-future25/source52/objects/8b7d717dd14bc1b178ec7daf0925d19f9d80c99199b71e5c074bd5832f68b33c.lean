import Mathlib
import SafeLearning.CoreModules

set_option autoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace SafeLearning.CompleteDuality

def rewardLagrangian {I K : Type*} [Fintype K]
    (reward : I → ℝ) (cost : I → K → ℝ) (budget lambda : K → ℝ) (policy : I) : ℝ :=
  reward policy - ∑ k, lambda k * (cost policy k - budget k)

def rewardDual {I K : Type*} [Fintype K]
    (reward : I → ℝ) (cost : I → K → ℝ) (budget lambda : K → ℝ) : ℝ :=
  ⨆ policy, rewardLagrangian reward cost budget lambda policy

theorem bounded_lagrangian_from_bounded_returns {I K : Type*} [Fintype K]
    (reward : I → ℝ) (cost : I → K → ℝ) (budget lambda : K → ℝ)
    (rewardBound : ℝ) (costBound : K → ℝ)
    (hr : ∀ policy, |reward policy| ≤ rewardBound)
    (hc : ∀ policy k, |cost policy k| ≤ costBound k) (policy : I) :
    |rewardLagrangian reward cost budget lambda policy| ≤
      rewardBound+∑ k, |lambda k| * (costBound k+|budget k|) := by
  have hs : |∑ k,lambda k*(cost policy k-budget k)| ≤
      ∑ k,|lambda k| * (costBound k+|budget k|) := by
    calc
      _ ≤ ∑ k,|lambda k*(cost policy k-budget k)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro k hk
        rw [abs_mul]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact (abs_sub (cost policy k) (budget k)).trans (add_le_add (hc policy k) le_rfl)
  unfold rewardLagrangian
  exact (abs_sub _ _).trans (add_le_add (hr policy) hs)

theorem reward_lagrangian_bounded_above {I K : Type*} [Fintype K]
    (reward : I → ℝ) (cost : I → K → ℝ) (budget lambda : K → ℝ)
    (rewardBound : ℝ) (costBound : K → ℝ)
    (hr : ∀ policy, |reward policy| ≤ rewardBound)
    (hc : ∀ policy k, |cost policy k| ≤ costBound k) :
    BddAbove (range (rewardLagrangian reward cost budget lambda)) := by
  refine ⟨rewardBound+∑ k, |lambda k| * (costBound k+|budget k|),?_⟩
  rintro value ⟨policy,rfl⟩
  exact (le_abs_self _).trans
    (bounded_lagrangian_from_bounded_returns reward cost budget lambda rewardBound costBound hr hc policy)

theorem lagrangian_affine {I K : Type*} [Fintype K]
    (reward : I → ℝ) (cost : I → K → ℝ) (budget x y : K → ℝ)
    (policy : I) (a b : ℝ) (hab : a+b=1) :
    rewardLagrangian reward cost budget (a • x+b • y) policy =
      a*rewardLagrangian reward cost budget x policy+
        b*rewardLagrangian reward cost budget y policy := by
  simp only [rewardLagrangian,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  simp_rw [add_mul,Finset.sum_add_distrib,mul_assoc,← Finset.mul_sum]
  linear_combination -(reward policy) * hab

theorem reward_dual_convex {I K : Type*} [Nonempty I] [Fintype K]
    (reward : I → ℝ) (cost : I → K → ℝ) (budget : K → ℝ)
    (hbounded : ∀ lambda : K → ℝ,
      BddAbove (range (rewardLagrangian reward cost budget lambda))) :
    ConvexOn ℝ univ (rewardDual reward cost budget) := by
  refine ⟨convex_univ,?_⟩
  intro x hx y hy a b ha hb hab
  apply ciSup_le
  intro policy
  rw [lagrangian_affine reward cost budget x y policy a b hab]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (le_ciSup (hbounded x) policy) ha)
    (mul_le_mul_of_nonneg_left (le_ciSup (hbounded y) policy) hb)

theorem feasible_reward_le_dual {I K : Type*} [Fintype K]
    (reward : I → ℝ) (cost : I → K → ℝ) (budget lambda : K → ℝ) (policy : I)
    (hbounded : BddAbove (range (rewardLagrangian reward cost budget lambda)))
    (hlambda : ∀ k, 0 ≤ lambda k) (hfeasible : ∀ k, cost policy k ≤ budget k) :
    reward policy ≤ rewardDual reward cost budget lambda := by
  have hsum : (∑ k, lambda k*(cost policy k-budget k)) ≤ 0 :=
    Finset.sum_nonpos (fun k _ => mul_nonpos_of_nonneg_of_nonpos
      (hlambda k) (sub_nonpos.mpr (hfeasible k)))
  apply le_trans (show reward policy ≤ rewardLagrangian reward cost budget lambda policy by
    unfold rewardLagrangian; linarith)
  exact le_ciSup hbounded policy

theorem exact_maximizer_subgradient {I K : Type*} [Fintype K]
    (reward : I → ℝ) (cost : I → K → ℝ) (budget x y : K → ℝ) (policy : I)
    (hbounded : BddAbove (range (rewardLagrangian reward cost budget y)))
    (hmax : rewardLagrangian reward cost budget x policy=rewardDual reward cost budget x) :
    rewardDual reward cost budget x+∑ k, (y k-x k)*(budget k-cost policy k) ≤
      rewardDual reward cost budget y := by
  have hle := le_ciSup hbounded policy
  change rewardLagrangian reward cost budget y policy ≤ rewardDual reward cost budget y at hle
  have hs : (∑ k, (y k-x k)*(budget k-cost policy k)) =
      (∑ k, x k*(cost policy k-budget k))-(∑ k, y k*(cost policy k-budget k)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  calc
    _ = rewardLagrangian reward cost budget y policy := by
      rw [← hmax,hs]
      unfold rewardLagrangian
      ring
    _ ≤ _ := hle

def costLagrangian {I K : Type*} [Fintype K]
    (objective : I → ℝ) (cost : I → K → ℝ) (budget lambda : K → ℝ) (policy : I) : ℝ :=
  objective policy+∑ k, lambda k*(cost policy k-budget k)

def costDual {I K : Type*} [Fintype K]
    (objective : I → ℝ) (cost : I → K → ℝ) (budget lambda : K → ℝ) : ℝ :=
  ⨅ policy, costLagrangian objective cost budget lambda policy

theorem cost_lagrangian_bounded_below {I K : Type*} [Fintype K]
    (objective : I → ℝ) (cost : I → K → ℝ) (budget lambda : K → ℝ)
    (objectiveBound : ℝ) (costBound : K → ℝ)
    (hr : ∀ policy, |objective policy| ≤ objectiveBound)
    (hc : ∀ policy k, |cost policy k| ≤ costBound k) :
    BddBelow (range (costLagrangian objective cost budget lambda)) := by
  refine ⟨-(objectiveBound+∑ k, |lambda k| * (costBound k+|budget k|)),?_⟩
  rintro value ⟨policy,rfl⟩
  have hrneg : ∀ policy, |(-objective policy)| ≤ objectiveBound := by simpa using hr
  have hh := bounded_lagrangian_from_bounded_returns
    (fun policy => -objective policy) cost budget lambda objectiveBound costBound hrneg hc policy
  have hneg := (le_abs_self (rewardLagrangian (fun policy => -objective policy) cost budget lambda policy)).trans hh
  unfold costLagrangian rewardLagrangian at *
  linarith

theorem cost_dual_mirror {I K : Type*} [Nonempty I] [Fintype K]
    (objective : I → ℝ) (cost : I → K → ℝ) (budget lambda : K → ℝ)
    (habove : BddAbove (range (rewardLagrangian (fun p => -objective p) cost budget lambda)))
    (hbelow : BddBelow (range (costLagrangian objective cost budget lambda))) :
    costDual objective cost budget lambda = -rewardDual (fun p => -objective p) cost budget lambda := by
  apply le_antisymm
  · have h : rewardDual (fun p => -objective p) cost budget lambda ≤
        -costDual objective cost budget lambda := by
      apply ciSup_le
      intro policy
      have hh := ciInf_le hbelow policy
      change costDual objective cost budget lambda ≤ costLagrangian objective cost budget lambda policy at hh
      unfold costLagrangian rewardLagrangian at *
      linarith
    linarith
  · apply le_ciInf
    intro policy
    have hh := le_ciSup habove policy
    change rewardLagrangian (fun p => -objective p) cost budget lambda policy ≤
      rewardDual (fun p => -objective p) cost budget lambda at hh
    unfold costLagrangian rewardLagrangian at *
    linarith

theorem cost_lagrangian_affine {I K : Type*} [Fintype K]
    (objective : I → ℝ) (cost : I → K → ℝ) (budget x y : K → ℝ)
    (policy : I) (a b : ℝ) (hab : a+b=1) :
    costLagrangian objective cost budget (a • x+b • y) policy =
      a*costLagrangian objective cost budget x policy+
        b*costLagrangian objective cost budget y policy := by
  simp only [costLagrangian,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  simp_rw [add_mul,Finset.sum_add_distrib,mul_assoc,← Finset.mul_sum]
  linear_combination -(objective policy) * hab

theorem cost_dual_concave {I K : Type*} [Nonempty I] [Fintype K]
    (objective : I → ℝ) (cost : I → K → ℝ) (budget : K → ℝ)
    (hbounded : ∀ lambda : K → ℝ,
      BddBelow (range (costLagrangian objective cost budget lambda))) :
    ConcaveOn ℝ univ (costDual objective cost budget) := by
  refine ⟨convex_univ,?_⟩
  intro x hx y hy a b ha hb hab
  apply le_ciInf
  intro policy
  rw [cost_lagrangian_affine objective cost budget x y policy a b hab]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (ciInf_le (hbounded x) policy) ha)
    (mul_le_mul_of_nonneg_left (ciInf_le (hbounded y) policy) hb)

theorem cost_dual_le_feasible_cost {I K : Type*} [Fintype K]
    (objective : I → ℝ) (cost : I → K → ℝ) (budget lambda : K → ℝ) (policy : I)
    (hbounded : BddBelow (range (costLagrangian objective cost budget lambda)))
    (hlambda : ∀ k, 0 ≤ lambda k) (hfeasible : ∀ k, cost policy k ≤ budget k) :
    costDual objective cost budget lambda ≤ objective policy := by
  have hsum : (∑ k, lambda k*(cost policy k-budget k)) ≤ 0 :=
    Finset.sum_nonpos (fun k _ => mul_nonpos_of_nonneg_of_nonpos
      (hlambda k) (sub_nonpos.mpr (hfeasible k)))
  apply le_trans (ciInf_le hbounded policy)
  unfold costLagrangian
  linarith

theorem reward_primal_le_each_dual {I K : Type*} [Fintype K]
    (reward : I → ℝ) (cost : I → K → ℝ) (budget lambda : K → ℝ)
    [Nonempty {policy : I // ∀ k, cost policy k ≤ budget k}]
    (hbounded : BddAbove (range (rewardLagrangian reward cost budget lambda)))
    (hlambda : ∀ k, 0 ≤ lambda k) :
    (⨆ policy : {policy : I // ∀ k, cost policy k ≤ budget k}, reward policy.val) ≤
      rewardDual reward cost budget lambda := by
  apply ciSup_le
  intro policy
  exact feasible_reward_le_dual reward cost budget lambda policy.val hbounded hlambda policy.property

theorem reward_weak_duality {I K : Type*} [Fintype K]
    (reward : I → ℝ) (cost : I → K → ℝ) (budget : K → ℝ)
    [Nonempty {policy : I // ∀ k, cost policy k ≤ budget k}]
    (hbounded : ∀ lambda : K → ℝ,
      BddAbove (range (rewardLagrangian reward cost budget lambda))) :
    (⨆ policy : {policy : I // ∀ k, cost policy k ≤ budget k}, reward policy.val) ≤
      ⨅ lambda : {lambda : K → ℝ // ∀ k, 0 ≤ lambda k},
        rewardDual reward cost budget lambda.val := by
  letI : Nonempty {lambda : K → ℝ // ∀ k, 0 ≤ lambda k} := ⟨⟨0,fun _ => le_rfl⟩⟩
  apply le_ciInf
  intro lambda
  exact reward_primal_le_each_dual reward cost budget lambda.val (hbounded lambda.val) lambda.property

theorem cost_each_dual_le_primal {I K : Type*} [Fintype K]
    (objective : I → ℝ) (cost : I → K → ℝ) (budget lambda : K → ℝ)
    [Nonempty {policy : I // ∀ k, cost policy k ≤ budget k}]
    (hbounded : BddBelow (range (costLagrangian objective cost budget lambda)))
    (hlambda : ∀ k, 0 ≤ lambda k) :
    costDual objective cost budget lambda ≤
      ⨅ policy : {policy : I // ∀ k, cost policy k ≤ budget k}, objective policy.val := by
  apply le_ciInf
  intro policy
  exact cost_dual_le_feasible_cost objective cost budget lambda policy.val hbounded hlambda policy.property

theorem cost_weak_duality {I K : Type*} [Fintype K]
    (objective : I → ℝ) (cost : I → K → ℝ) (budget : K → ℝ)
    [Nonempty {policy : I // ∀ k, cost policy k ≤ budget k}]
    (hbounded : ∀ lambda : K → ℝ,
      BddBelow (range (costLagrangian objective cost budget lambda))) :
    (⨆ lambda : {lambda : K → ℝ // ∀ k, 0 ≤ lambda k},
      costDual objective cost budget lambda.val) ≤
        ⨅ policy : {policy : I // ∀ k, cost policy k ≤ budget k}, objective policy.val := by
  letI : Nonempty {lambda : K → ℝ // ∀ k, 0 ≤ lambda k} := ⟨⟨0,fun _ => le_rfl⟩⟩
  apply ciSup_le
  intro lambda
  exact cost_each_dual_le_primal objective cost budget lambda.val (hbounded lambda.val) lambda.property

def walkLagrangian (p lambda : ℝ) : ℝ := p-lambda*(2*p-1)

def walkDual (lambda : ℝ) : ℝ := max lambda (1-lambda)

theorem walk_lagrangian_bound (p lambda : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    walkLagrangian p lambda ≤ walkDual lambda := by
  have h0 := le_max_left lambda (1-lambda)
  have h1 := le_max_right lambda (1-lambda)
  unfold walkLagrangian walkDual
  by_cases hs : 0 ≤ 1-2*lambda
  · have hh := mul_le_mul_of_nonneg_left hp1 hs
    nlinarith
  · have hh := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hs) hp0
    nlinarith

theorem walk_dual_attained (lambda : ℝ) :
    ∃ p : ℝ, p ∈ Icc 0 1 ∧ walkLagrangian p lambda=walkDual lambda := by
  by_cases hs : lambda ≤ 1/2
  · refine ⟨1,⟨by norm_num,by norm_num⟩,?_⟩
    rw [walkDual,max_eq_right (by linarith)]
    unfold walkLagrangian
    ring
  · refine ⟨0,⟨by norm_num,by norm_num⟩,?_⟩
    rw [walkDual,max_eq_left (by linarith)]
    unfold walkLagrangian
    ring

theorem walk_dual_actual_supremum (lambda : ℝ) :
    sSup ((fun p => walkLagrangian p lambda) '' Icc 0 1)=walkDual lambda := by
  obtain ⟨p,hp,heq⟩ := walk_dual_attained lambda
  have hmem : walkDual lambda ∈ ((fun p => walkLagrangian p lambda) '' Icc 0 1) := ⟨p,hp,heq⟩
  have hbound : ∀ value ∈ ((fun p => walkLagrangian p lambda) '' Icc 0 1),value ≤ walkDual lambda := by
    rintro value ⟨q,hq,rfl⟩
    exact walk_lagrangian_bound q lambda hq.1 hq.2
  exact le_antisymm (csSup_le ⟨_,hmem⟩ hbound) (le_csSup ⟨_,hbound⟩ hmem)

theorem walk_dual_minimum (lambda : ℝ) : 1/2 ≤ walkDual lambda := by
  have h0 := le_max_left lambda (1-lambda)
  have h1 := le_max_right lambda (1-lambda)
  unfold walkDual
  linarith

theorem walk_dual_unique_minimum (lambda : ℝ) : walkDual lambda=1/2 ↔ lambda=1/2 := by
  constructor
  · intro h
    have h0 := le_max_left lambda (1-lambda)
    have h1 := le_max_right lambda (1-lambda)
    unfold walkDual at h
    linarith
  · rintro rfl
    norm_num [walkDual]

theorem walk_dual_piecewise (lambda : ℝ) :
    walkDual lambda=if lambda ≤ 1/2 then 1-lambda else lambda := by
  unfold walkDual
  split_ifs with h
  · exact max_eq_right (by linarith)
  · exact max_eq_left (by linarith)

theorem walk_dual_max_formula (lambda : ℝ) :
    walkDual lambda=lambda+max 0 (1-2*lambda) := by
  rw [walk_dual_piecewise]
  split_ifs with h
  · rw [max_eq_right (by linarith)]
    ring
  · rw [max_eq_left (by linarith)]
    ring

theorem walk_dual_abs_form (lambda : ℝ) : walkDual lambda=1/2+|lambda-1/2| := by
  by_cases h : 1/2 ≤ lambda
  · rw [walkDual,max_eq_left (by linarith),abs_of_nonneg (by linarith)]
    ring
  · rw [walkDual,max_eq_right (by linarith),abs_of_nonpos (by linarith)]
    ring

theorem walk_dual_kink : ¬ DifferentiableAt ℝ walkDual (1/2) := by
  intro h
  have h' : DifferentiableAt ℝ walkDual ((fun x : ℝ => x+1/2) 0) := by simpa using h
  have hadd : DifferentiableAt ℝ (fun x : ℝ => x+1/2) 0 := differentiableAt_id.add_const (1/2)
  have ht := (h'.comp 0 hadd).sub_const (1/2)
  apply not_differentiableAt_abs_zero
  convert ht using 1
  ext x
  simp [Function.comp_def,walk_dual_abs_form]

theorem walk_dual_convex : ConvexOn ℝ univ walkDual := by
  refine ⟨convex_univ,?_⟩
  intro x hx y hy a b ha hb hab
  change max (a*x+b*y) (1-(a*x+b*y)) ≤ a*max x (1-x)+b*max y (1-y)
  apply max_le
  · exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
      (mul_le_mul_of_nonneg_left (le_max_left _ _) hb)
  · have hh := add_le_add (mul_le_mul_of_nonneg_left (le_max_right x (1-x)) ha)
      (mul_le_mul_of_nonneg_left (le_max_right y (1-y)) hb)
    have he : 1-(a*x+b*y)=a*(1-x)+b*(1-y) := by linear_combination -hab
    rw [he]
    exact hh

theorem walk_primal_optimum (p : ℝ) (hcost : 2*p ≤ 1) : p ≤ 1/2 := by linarith

theorem walk_primal_attained_and_all_lagrangian_maximizers :
    (1/2 : ℝ) ∈ Icc 0 1 ∧ 2*(1/2 : ℝ)=1 ∧
      (∀ p : ℝ, walkLagrangian p (1/2)=1/2) ∧
        walkLagrangian 1 (1/2)=walkDual (1/2) ∧ ¬ 2*(1 : ℝ) ≤ 1 := by
  refine ⟨⟨by norm_num,by norm_num⟩,by norm_num,?_,?_,by norm_num⟩
  · intro p
    unfold walkLagrangian
    ring
  · norm_num [walkLagrangian,walkDual]

theorem scalar_lagrangian_derivative (reward cost budget lambda : ℝ) :
    HasDerivAt (fun l : ℝ => reward-l*(cost-budget)) (budget-cost) lambda := by
  convert (hasDerivAt_const lambda reward).sub
    ((hasDerivAt_id lambda).mul_const (cost-budget)) using 1 <;>
      (try ext l) <;> simp [id_eq] <;> ring

theorem projected_descent_sign (lambda eta cost budget : ℝ) :
    max 0 (lambda-eta*(budget-cost))=max 0 (lambda+eta*(cost-budget)) := by
  congr 1
  ring

theorem orthant_scalar_projection (x y : ℝ) (hy : 0 ≤ y) :
    0 ≤ max 0 x ∧ (max 0 x-x)^2 ≤ (y-x)^2 := by
  refine ⟨le_max_left _ _,?_⟩
  by_cases hx : 0 ≤ x
  · rw [max_eq_right hx]
    simpa using sq_nonneg (y-x)
  · rw [max_eq_left (le_of_not_ge hx)]
    have hprod := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hx) hy
    nlinarith [sq_nonneg y]

theorem orthant_projection_global_minimum {K : Type*} [Fintype K]
    (x y : K → ℝ) (hy : ∀ k, 0 ≤ y k) :
    (∀ k,0 ≤ max 0 (x k)) ∧
      (∑ k,(max 0 (x k)-x k)^2) ≤ ∑ k,(y k-x k)^2 := by
  refine ⟨fun k => (orthant_scalar_projection (x k) (y k) (hy k)).1,?_⟩
  exact Finset.sum_le_sum (fun k _ => (orthant_scalar_projection (x k) (y k) (hy k)).2)

theorem violation_increases_multiplier (lambda eta cost budget : ℝ)
    (he : 0 ≤ eta) (hv : budget ≤ cost) :
    lambda ≤ max 0 (lambda+eta*(cost-budget)) := by
  have hh := mul_nonneg he (sub_nonneg.mpr hv)
  exact (by linarith : lambda ≤ lambda+eta*(cost-budget)).trans (le_max_right _ _)

theorem strict_violation_strictly_increases_multiplier (lambda eta cost budget : ℝ)
    (he : 0 < eta) (hv : budget < cost) :
    lambda < max 0 (lambda+eta*(cost-budget)) := by
  have hh := mul_pos he (sub_pos.mpr hv)
  exact (by linarith : lambda < lambda+eta*(cost-budget)).trans_le (le_max_right _ _)

theorem attained_reward_dual {I K : Type*} [Nonempty I] [Fintype K]
    (reward : I → ℝ) (cost : I → K → ℝ) (budget lambda : K → ℝ) (policy : I)
    (hmax : ∀ other, rewardLagrangian reward cost budget lambda other ≤
      rewardLagrangian reward cost budget lambda policy) :
    rewardDual reward cost budget lambda=rewardLagrangian reward cost budget lambda policy := by
  have hb : BddAbove (range (rewardLagrangian reward cost budget lambda)) :=
    ⟨_,by rintro value ⟨other,rfl⟩;exact hmax other⟩
  exact le_antisymm (ciSup_le hmax) (le_ciSup hb policy)

theorem attained_cost_dual {I K : Type*} [Nonempty I] [Fintype K]
    (objective : I → ℝ) (cost : I → K → ℝ) (budget lambda : K → ℝ) (policy : I)
    (hmin : ∀ other, costLagrangian objective cost budget lambda policy ≤
      costLagrangian objective cost budget lambda other) :
    costDual objective cost budget lambda=costLagrangian objective cost budget lambda policy := by
  have hb : BddBelow (range (costLagrangian objective cost budget lambda)) :=
    ⟨_,by rintro value ⟨other,rfl⟩;exact hmin other⟩
  exact le_antisymm (ciInf_le hb policy) (le_ciInf hmin)

theorem slack_decreases_projected_multiplier (lambda eta cost budget : ℝ)
    (hl : 0 ≤ lambda) (he : 0 ≤ eta) (hs : cost ≤ budget) :
    max 0 (lambda+eta*(cost-budget)) ≤ lambda := by
  have hh := mul_nonpos_of_nonneg_of_nonpos he (sub_nonpos.mpr hs)
  exact max_le hl (by linarith)

end SafeLearning.CompleteDuality
