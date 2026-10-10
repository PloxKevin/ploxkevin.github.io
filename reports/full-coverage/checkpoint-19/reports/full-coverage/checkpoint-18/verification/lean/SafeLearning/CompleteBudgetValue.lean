import Mathlib
import SafeLearning.CompleteCoreBook

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace SafeLearning.CompleteBudgetValue

def feasibleRewards (budget : ℝ) : Set ℝ :=
  {value | ∃ p : ℝ, 0 ≤ p ∧ p ≤ 1 ∧ BookApplications.mixCost p ≤ budget ∧
    value=BookApplications.mixReward p}

def optimalReward (budget : ℝ) : ℝ := sSup (feasibleRewards budget)

theorem feasible_reward_bound (budget value : ℝ) (hv : value ∈ feasibleRewards budget) :
    value ≤ (50/3)*budget+50/3 := by
  rcases hv with ⟨p,hp0,hp1,hc,rfl⟩
  unfold BookApplications.mixCost at hc
  unfold BookApplications.mixReward
  linarith

theorem feasible_rewards_bounded (budget : ℝ) : BddAbove (feasibleRewards budget) :=
  ⟨(50/3)*budget+50/3,fun value hv => feasible_reward_bound budget value hv⟩

theorem interior_attainer (budget : ℝ) (hlo : 1/5 ≤ budget) (hhi : budget ≤ 2) :
    (50/3)*budget+50/3 ∈ feasibleRewards budget := by
  refine ⟨(budget-1/5)/(9/5),?_,?_,?_,?_⟩
  · apply div_nonneg <;> linarith
  · apply (div_le_iff₀ (by norm_num : (0 : ℝ)<9/5)).mpr
    linarith
  · unfold BookApplications.mixCost
    linarith
  · unfold BookApplications.mixReward
    ring

theorem actual_interior_optimal_value (budget : ℝ) (hlo : 1/5 ≤ budget) (hhi : budget ≤ 2) :
    optimalReward budget=(50/3)*budget+50/3 := by
  apply le_antisymm
  · exact csSup_le ⟨_,interior_attainer budget hlo hhi⟩
      (fun value hv => feasible_reward_bound budget value hv)
  · exact le_csSup (feasible_rewards_bounded budget) (interior_attainer budget hlo hhi)

theorem actual_optimal_value_derivative (budget : ℝ) (hlo : 1/5 < budget) (hhi : budget < 2) :
    HasDerivAt optimalReward (50/3) budget := by
  have hlinear : HasDerivAt (fun d : ℝ => (50/3)*d+50/3) (50/3) budget := by
    convert ((hasDerivAt_id budget).const_mul (50/3)).add_const (50/3) using 1 <;>
      simp [id_eq]
  apply hlinear.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds (show budget ∈ Ioo (1/5 : ℝ) 2 from ⟨hlo,hhi⟩)]
    with d hd
  exact actual_interior_optimal_value d hd.1.le hd.2.le

theorem budget_value_at_tighter_budget : optimalReward (13/20)=55/2 := by
  rw [actual_interior_optimal_value _ (by norm_num) (by norm_num)]
  norm_num

theorem tighter_budget_multiplier_derivative : HasDerivAt optimalReward (50/3) (13/20) :=
  actual_optimal_value_derivative _ (by norm_num) (by norm_num)

def mixtureLagrangian (p budget lambda : ℝ) : ℝ :=
  BookApplications.mixReward p-lambda*(BookApplications.mixCost p-budget)

def mixtureDual (budget lambda : ℝ) : ℝ :=
  max (mixtureLagrangian 0 budget lambda) (mixtureLagrangian 1 budget lambda)

theorem mixture_lagrangian_bound (p budget lambda : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    mixtureLagrangian p budget lambda ≤ mixtureDual budget lambda := by
  have h0 := le_max_left (mixtureLagrangian 0 budget lambda) (mixtureLagrangian 1 budget lambda)
  have h1 := le_max_right (mixtureLagrangian 0 budget lambda) (mixtureLagrangian 1 budget lambda)
  unfold mixtureDual at *
  unfold mixtureLagrangian BookApplications.mixReward BookApplications.mixCost at *
  by_cases hs : 0 ≤ 30-(9/5)*lambda
  · have hh := mul_le_mul_of_nonneg_left hp1 hs
    nlinarith
  · have hh := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hs) hp0
    nlinarith

theorem mixture_dual_attained (budget lambda : ℝ) :
    ∃ p ∈ Icc (0 : ℝ) 1, mixtureLagrangian p budget lambda=mixtureDual budget lambda := by
  by_cases h : mixtureLagrangian 0 budget lambda ≤ mixtureLagrangian 1 budget lambda
  · exact ⟨1,⟨by norm_num,by norm_num⟩,(max_eq_right h).symm⟩
  · exact ⟨0,⟨by norm_num,by norm_num⟩,(max_eq_left (le_of_not_ge h)).symm⟩

theorem mixture_dual_actual_supremum (budget lambda : ℝ) :
    sSup ((fun p => mixtureLagrangian p budget lambda) '' Icc 0 1)=mixtureDual budget lambda := by
  obtain ⟨p,hp,heq⟩ := mixture_dual_attained budget lambda
  have hmem : mixtureDual budget lambda ∈ ((fun p => mixtureLagrangian p budget lambda) '' Icc 0 1) := ⟨p,hp,heq⟩
  have hbound : ∀ value ∈ ((fun p => mixtureLagrangian p budget lambda) '' Icc 0 1),
      value ≤ mixtureDual budget lambda := by
    rintro value ⟨q,hq,rfl⟩
    exact mixture_lagrangian_bound q budget lambda hq.1 hq.2
  exact le_antisymm (csSup_le ⟨_,hmem⟩ hbound) (le_csSup ⟨_,hbound⟩ hmem)

theorem actual_dual_price_attained (budget : ℝ) :
    mixtureDual budget (50/3)=(50/3)*budget+50/3 := by
  unfold mixtureDual
  have h0 : mixtureLagrangian 0 budget (50/3)=(50/3)*budget+50/3 := by
    unfold mixtureLagrangian BookApplications.mixReward BookApplications.mixCost
    ring
  have h1 : mixtureLagrangian 1 budget (50/3)=(50/3)*budget+50/3 := by
    unfold mixtureLagrangian BookApplications.mixReward BookApplications.mixCost
    ring
  rw [h0,h1,max_self]

theorem actual_dual_price_optimal (budget lambda : ℝ) (hlo : 1/5 ≤ budget)
    (hhi : budget ≤ 2) (hlambda : 0 ≤ lambda) :
    optimalReward budget ≤ mixtureDual budget lambda := by
  rw [actual_interior_optimal_value budget hlo hhi]
  have hp0 : 0 ≤ (budget-1/5)/(9/5) := div_nonneg (by linarith) (by norm_num)
  have hp1 : (budget-1/5)/(9/5) ≤ 1 := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ)<9/5)).mpr
    linarith
  have hh := mixture_lagrangian_bound ((budget-1/5)/(9/5)) budget lambda hp0 hp1
  have heq : mixtureLagrangian ((budget-1/5)/(9/5)) budget lambda=(50/3)*budget+50/3 := by
    unfold mixtureLagrangian BookApplications.mixReward BookApplications.mixCost
    ring
  rw [heq] at hh
  exact hh

theorem actual_dual_price_unique (budget lambda : ℝ) (hlo : 1/5 < budget)
    (hhi : budget < 2) :
    mixtureDual budget lambda=optimalReward budget ↔ lambda=50/3 := by
  rw [actual_interior_optimal_value budget hlo.le hhi.le]
  constructor
  · intro heq
    have h0 := le_max_left (mixtureLagrangian 0 budget lambda) (mixtureLagrangian 1 budget lambda)
    have h1 := le_max_right (mixtureLagrangian 0 budget lambda) (mixtureLagrangian 1 budget lambda)
    change mixtureLagrangian 0 budget lambda ≤ mixtureDual budget lambda at h0
    change mixtureLagrangian 1 budget lambda ≤ mixtureDual budget lambda at h1
    rw [heq] at h0 h1
    unfold mixtureLagrangian BookApplications.mixReward BookApplications.mixCost at h0 h1
    have hleft : lambda ≤ 50/3 := by nlinarith
    have hright : 50/3 ≤ lambda := by nlinarith
    exact le_antisymm hleft hright
  · rintro rfl
    exact actual_dual_price_attained budget

end SafeLearning.CompleteBudgetValue
