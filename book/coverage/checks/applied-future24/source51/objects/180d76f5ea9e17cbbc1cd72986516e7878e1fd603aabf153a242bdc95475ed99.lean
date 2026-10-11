import Mathlib
import SafeLearning.BookApplications
import SafeLearning.CoreAnalysis

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology ENNReal NNReal

namespace SafeLearning.CompleteCoreBook

def modeLaw (p : ℝ≥0) (hp : p ≤ 1) : PMF (Fin 2) :=
  PMF.ofFintype (fun i => (((![1-p,p] : Fin 2 → ℝ≥0) i) : ℝ≥0∞))
    (by norm_cast; simp [Fin.sum_univ_succ,tsub_add_cancel_of_le hp])

def expectedMode (p : ℝ≥0) (hp : p ≤ 1) (slow fast : ℝ) : ℝ :=
  ∑ i : Fin 2, (modeLaw p hp i).toReal*(![slow,fast] : Fin 2 → ℝ) i

theorem mode_expectation (p : ℝ≥0) (hp : p ≤ 1) (slow fast : ℝ) :
    expectedMode p hp slow fast=(1-(p : ℝ))*slow+(p : ℝ)*fast := by
  simp [expectedMode,modeLaw,Fin.sum_univ_succ,NNReal.coe_sub hp]

def modeReturn (p : ℝ≥0) (hp : p ≤ 1) (gamma slow fast : ℝ) : ℝ :=
  ∑' n : ℕ, gamma^n*expectedMode p hp slow fast

theorem mode_discounted_return (p : ℝ≥0) (hp : p ≤ 1) (gamma slow fast : ℝ)
    (hg : |gamma| < 1) :
    modeReturn p hp gamma slow fast=((1-(p : ℝ))*slow+(p : ℝ)*fast)/(1-gamma) := by
  rw [modeReturn,CoreModules.discounted_constant _ _ hg,mode_expectation]

theorem original_reward_semantics (p : ℝ≥0) (hp : p ≤ 1) :
    modeReturn p hp (9/10) 2 5=BookApplications.mixReward p := by
  rw [mode_discounted_return p hp _ _ _ (by norm_num)]
  unfold BookApplications.mixReward
  ring

theorem original_cost_semantics (p : ℝ≥0) (hp : p ≤ 1) :
    modeReturn p hp (9/10) (1/50) (1/5)=BookApplications.mixCost p := by
  rw [mode_discounted_return p hp _ _ _ (by norm_num)]
  unfold BookApplications.mixCost
  ring

theorem tighter_budget_optimum (p : ℝ≥0) (hp : p ≤ 1)
    (hc : modeReturn p hp (9/10) (1/50) (1/5) ≤ 13/20) :
    (p : ℝ) ≤ 1/4 ∧ modeReturn p hp (9/10) 2 5 ≤ 55/2 := by
  rw [original_cost_semantics] at hc
  rw [original_reward_semantics]
  unfold BookApplications.mixCost at hc
  unfold BookApplications.mixReward
  constructor <;> linarith

theorem tighter_budget_attained :
    modeReturn (1/4) (by rw [← NNReal.coe_le_coe]; norm_num) (9/10) (1/50) (1/5)=13/20 ∧
    modeReturn (1/4) (by rw [← NNReal.coe_le_coe]; norm_num) (9/10) 2 5=55/2 := by
  rw [original_cost_semantics,original_reward_semantics]
  norm_num [BookApplications.mixReward,BookApplications.mixCost]

theorem tighter_budget_unique_reward (p : ℝ≥0) (hp : p ≤ 1) :
    modeReturn p hp (9/10) 2 5=55/2 ↔ p=1/4 := by
  rw [original_reward_semantics]
  unfold BookApplications.mixReward
  constructor
  · intro h
    apply NNReal.coe_injective
    norm_num
    linarith
  · intro h
    subst p
    norm_num

theorem interior_budget_multiplier (budget p : ℝ) :
    BookApplications.mixReward p-(50/3)*(BookApplications.mixCost p-budget)=
      50/3*budget+50/3 := by
  unfold BookApplications.mixReward BookApplications.mixCost
  ring

theorem changed_discount_reward (p : ℝ≥0) (hp : p ≤ 1) :
    modeReturn p hp (19/20) 2 5=40+60*(p : ℝ) := by
  rw [mode_discounted_return p hp _ _ _ (by norm_num)]
  ring

theorem changed_discount_cost (p : ℝ≥0) (hp : p ≤ 1) :
    modeReturn p hp (19/20) (1/50) (1/5)=2/5+(18/5)*(p : ℝ) := by
  rw [mode_discounted_return p hp _ _ _ (by norm_num)]
  ring

theorem changed_discount_optimum (p : ℝ≥0) (hp : p ≤ 1)
    (hc : modeReturn p hp (19/20) (1/50) (1/5) ≤ 1) :
    (p : ℝ) ≤ 1/6 ∧ modeReturn p hp (19/20) 2 5 ≤ 50 := by
  rw [changed_discount_cost] at hc
  rw [changed_discount_reward]
  constructor <;> linarith

theorem changed_discount_attainer_and_reuse :
    modeReturn (1/6) (by rw [← NNReal.coe_le_coe]; norm_num) (19/20) (1/50) (1/5)=1 ∧
    modeReturn (1/6) (by rw [← NNReal.coe_le_coe]; norm_num) (19/20) 2 5=50 ∧
    modeReturn (4/9) (by rw [← NNReal.coe_le_coe]; norm_num) (19/20) (1/50) (1/5)=2 := by
  rw [changed_discount_cost,changed_discount_reward,changed_discount_cost]
  norm_num

theorem monitoring_next_action (cost : ℝ) (h : cost=1/2 ∨ cost=3/5) :
    (0 ≤ (14/27-cost)/(9/10) ↔ cost=1/2) := by
  rcases h with rfl | rfl <;> norm_num

theorem monitoring_discounted_accounting :
    ((14/27 : ℝ)-1/2)/(9/10)=5/243 ∧
    (2/5 : ℝ)+(9/10)*(1/5)+(9/10)^2*(1/2)=197/200 ∧
    (9/10 : ℝ)^3*(5/243)=3/200 ∧
    (197/200 : ℝ)+3/200=1 := by norm_num

theorem pathwise_resource_must_cover_realizations (z : ℝ) (cost : Fin 2 → ℝ) :
    (∀ i, 0 ≤ z-cost i) ↔ (cost 0 ≤ z ∧ cost 1 ≤ z) := by
  constructor
  · intro h
    exact ⟨by linarith [h 0],by linarith [h 1]⟩
  · rintro ⟨h0,h1⟩ i
    fin_cases i <;> dsimp at * <;> linarith

theorem ellipse_candidate_feasible :
    (1/5 : ℝ)^2+4*(Real.sqrt 6/5)^2=1 ∧
    2*(1/5 : ℝ)+Real.sqrt 6/5=(2+Real.sqrt 6)/5 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)
  constructor <;> nlinarith

theorem ellipse_global_optimum (x y : ℝ) (he : x^2+4*y^2 ≤ 1) (hx : x ≤ 1/5) :
    2*x+y ≤ (2+Real.sqrt 6)/5 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)
  have hp := Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 6)
  have hrem : 0 ≤ (x-1/5)^2+4*(y-Real.sqrt 6/5)^2 := by positivity
  have hsupport : x/5+4*(Real.sqrt 6/5)*y ≤ 1 := by nlinarith
  have hnu : 0 < 2-1/(4*Real.sqrt 6) := by
    have hg : 1 < Real.sqrt 6 := by nlinarith
    have hdiv : 1/(4*Real.sqrt 6) < 1 := (div_lt_one (by positivity)).mpr (by nlinarith)
    linarith
  have hdual := mul_le_mul_of_nonneg_left hx (le_of_lt hnu)
  have hweight := mul_le_mul_of_nonneg_left hsupport (by positivity : 0 ≤ 5/(4*Real.sqrt 6))
  have hid : (5/(4*Real.sqrt 6))*(x/5+4*(Real.sqrt 6/5)*y)+
      (2-1/(4*Real.sqrt 6))*x=2*x+y := by field_simp;ring
  have hbound : 5/(4*Real.sqrt 6)+(2-1/(4*Real.sqrt 6))*(1/5)=
      (2+Real.sqrt 6)/5 := by field_simp; nlinarith
  linarith

theorem ellipse_kkt :
    (0 : ℝ) < 5/(4*Real.sqrt 6) ∧ 0 < 2-1/(4*Real.sqrt 6) ∧
    (5/(4*Real.sqrt 6))*(4*Real.sqrt 6/5)=1 ∧
    (5/(4*Real.sqrt 6))*(1/5)+(2-1/(4*Real.sqrt 6))=2 ∧
    (5/(4*Real.sqrt 6))*(((1/5)^2+4*(Real.sqrt 6/5)^2)/2-1/2)=0 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)
  have hp := Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 6)
  have hg : 1 < Real.sqrt 6 := by nlinarith
  refine ⟨by positivity,?_,?_,?_,?_⟩
  · have hh : 1/(4*Real.sqrt 6) < 1 := (div_lt_one (by positivity)).mpr (by nlinarith)
    linarith
  · field_simp
  · field_simp; ring
  · have he := ellipse_candidate_feasible.1
    rw [he]
    norm_num

theorem metric_comparison :
    (1/2 : ℝ)^2+0^2=0^2+(1/2 : ℝ)^2 ∧
    ((1/2 : ℝ)^2+4*0^2)/2=1/8 ∧
    (0^2+4*(1/2 : ℝ)^2)/2=1/2 ∧
    2*(1/2 : ℝ)+0=1 ∧ 2*0+(1/2 : ℝ)=1/2 ∧
    ¬ (1/2 : ℝ) ≤ 1/5 ∧ (0 : ℝ) ≤ 1/5 := by norm_num

theorem sufficient_constraint_values :
    (-1/5 : ℝ)+1/5+(1/5)*((1/5)^2+(Real.sqrt 6/5)^2)=7/125 ∧
    (-1/5 : ℝ)+0+(1/5)*(0^2+(1/2)^2) = -3/20 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)
  constructor <;> nlinarith

theorem positive_upper_bound_underdetermines_violation :
    ∃ safe violating : ℝ, safe ≤ 7/125 ∧ violating ≤ 7/125 ∧ safe ≤ 0 ∧ 0 < violating := by
  exact ⟨-1,7/125,by norm_num,by norm_num,by norm_num,by norm_num⟩

theorem tightened_constraint_sufficient (actual upper : ℝ) (ha : actual ≤ upper)
    (hu : upper ≤ 0) : actual ≤ 0 := ha.trans hu

theorem scalar_tube_iff (q radius allowance : ℝ) (hq : 0 ≤ q)
    (hr : 0 ≤ radius) (ha : 0 ≤ allowance) :
    (∀ x e : ℝ, |x| ≤ radius → |e| ≤ allowance → |q*x+e| ≤ radius) ↔
      q*radius+allowance ≤ radius := by
  constructor
  · intro h
    have hh := h radius allowance (by simpa [abs_of_nonneg hr]) (by simpa [abs_of_nonneg ha])
    rw [abs_of_nonneg (by positivity)] at hh
    exact hh
  · intro hb x e hx he
    exact BookApplications.tube_invariant_step x q e radius allowance hq hx he hb

theorem noisier_tube_radius (radius : ℝ) :
    (1/2)*radius+9/100 ≤ radius ↔ 9/50 ≤ radius := by constructor <;> intro h <;> linarith

theorem noisier_tube_and_band :
    (1/2 : ℝ)*(9/50)+9/100=9/50 ∧
    1-(9/50 : ℝ)=41/50 ∧ (1/2 : ℝ)+9/100=59/100 ∧
    (59/100 : ℝ) ≤ 1 := by norm_num

theorem accuracy_error_iff (error : ℝ) :
    (1/2)*(4/25)+1/20+error ≤ (4/25 : ℝ) ↔ error ≤ 3/100 := by
  constructor <;> intro h <;> linarith

theorem tightened_nominal_interval (z e radius : ℝ)
    (hz : |z| ≤ 1-radius) (he : |e| ≤ radius) : |z+e| ≤ 1 := by
  calc |z+e| ≤ |z|+|e| := abs_add_le _ _
       _ ≤ 1 := by linarith

theorem tube_envelope_converges (initial allowance : ℝ) :
    Tendsto (fun n : ℕ => allowance/(1-(1/2 : ℝ))+
      (1/2 : ℝ)^n*(|initial|-allowance/(1-(1/2 : ℝ)))) atTop
      (𝓝 (2*allowance)) := by
  have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ)<1)).mul_const (|initial|-allowance/(1-(1/2 : ℝ)))
  have hc : Tendsto (fun _ : ℕ => allowance/(1-(1/2 : ℝ))) atTop
      (𝓝 (allowance/(1-(1/2 : ℝ)))) := tendsto_const_nhds
  convert hc.add hh using 1 <;> simp <;> ring

end SafeLearning.CompleteCoreBook
