import SafeLearning.CompleteFoundationsPenaltyModels

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Set Filter
open scoped Topology
namespace SafeLearning.CompleteFoundationsAugmentedModels
open CompleteFoundationsPenaltyModels

def augmentedObjective (multiplier x : ℝ) : ℝ :=
  objective x+((max (multiplier+2*constraint x) 0)^2-multiplier^2)/4

def augmentedCandidate (multiplier : ℝ) : ℝ := (6-multiplier)/4

def multiplierUpdate (multiplier x : ℝ) : ℝ := max (multiplier+2*constraint x) 0

theorem actual_augmented_branches (multiplier x : ℝ) :
    (x ≤ 1-multiplier/2 → augmentedObjective multiplier x=objective x-multiplier^2/4) ∧
    (1-multiplier/2 ≤ x → augmentedObjective multiplier x=
      objective x+multiplier*(x-1)+(x-1)^2) := by
  constructor
  · intro hx
    have hn : multiplier+2*constraint x ≤ 0 := by dsimp [constraint];linarith
    rw [augmentedObjective,max_eq_right hn]
    ring
  · intro hx
    have hn : 0 ≤ multiplier+2*constraint x := by dsimp [constraint];linarith
    rw [augmentedObjective,max_eq_left hn]
    dsimp [constraint]
    ring

theorem actual_augmented_upper_completed_square (multiplier x : ℝ) :
    objective x+multiplier*(x-1)+(x-1)^2=
      2*(x-augmentedCandidate multiplier)^2+1-(2-multiplier)^2/8 := by
  dsimp [objective,augmentedCandidate]
  ring

theorem actual_augmented_global_unique (multiplier : ℝ)
    (hm : 0 ≤ multiplier) (x : ℝ) :
    1-(2-multiplier)^2/8 ≤ augmentedObjective multiplier x ∧
      (augmentedObjective multiplier x=1-(2-multiplier)^2/8 ↔ x=augmentedCandidate multiplier) := by
  by_cases hx : x ≤ 1-multiplier/2
  · rw [(actual_augmented_branches multiplier x).1 hx]
    have he : objective x-multiplier^2/4=1+multiplier+
        (1-multiplier/2-x)^2+(2+multiplier)*(1-multiplier/2-x) := by
      dsimp [objective]
      ring
    have hp := mul_nonneg (show 0 ≤ 2+multiplier by linarith)
      (show 0 ≤ 1-multiplier/2-x by linarith)
    have hstrict : 1-(2-multiplier)^2/8 < 1+multiplier := by
      nlinarith [sq_nonneg multiplier]
    rw [he]
    refine ⟨by nlinarith [sq_nonneg (1-multiplier/2-x)],?_⟩
    constructor
    · intro hh
      nlinarith [sq_nonneg (1-multiplier/2-x)]
    · intro hh
      dsimp [augmentedCandidate] at hh
      linarith
  · rw [(actual_augmented_branches multiplier x).2 (by linarith),
      actual_augmented_upper_completed_square]
    refine ⟨by nlinarith [sq_nonneg (x-augmentedCandidate multiplier)],?_⟩
    constructor
    · intro hh
      have hz : (x-augmentedCandidate multiplier)^2=0 := by nlinarith
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
    · intro hh
      rw [hh]
      ring

theorem actual_augmented_candidate_and_update (multiplier : ℝ) (hm : 0 ≤ multiplier) :
    augmentedObjective multiplier (augmentedCandidate multiplier)=1-(2-multiplier)^2/8 ∧
    multiplierUpdate multiplier (augmentedCandidate multiplier)=(multiplier+2)/2 := by
  refine ⟨(actual_augmented_global_unique multiplier hm _).2.mpr rfl,?_⟩
  have he : multiplier+2*constraint (augmentedCandidate multiplier)=(multiplier+2)/2 := by
    dsimp [constraint,augmentedCandidate]
    ring
  rw [multiplierUpdate,he,max_eq_left (by linarith)]

theorem actual_augmented_polynomial_derivative (multiplier x : ℝ) :
    HasDerivAt (fun y : ℝ => objective y+multiplier*(y-1)+(y-1)^2)
      (4*x+multiplier-6) x := by
  convert ((actual_objective_derivative x).add
    (((hasDerivAt_id x).sub_const 1).const_mul multiplier)).add
    (((hasDerivAt_id x).sub_const 1).pow 2) using 1
  · rfl
  · norm_num [id_eq]
    ring

theorem actual_augmented_candidate_true_stationarity (multiplier : ℝ) (hm : 0 ≤ multiplier) :
    HasDerivAt (augmentedObjective multiplier) 0 (augmentedCandidate multiplier) := by
  have hx : 1-multiplier/2 < augmentedCandidate multiplier := by
    dsimp [augmentedCandidate]
    linarith
  have hd : HasDerivAt (fun y : ℝ => objective y+multiplier*(y-1)+(y-1)^2)
      0 (augmentedCandidate multiplier) := by
    convert actual_augmented_polynomial_derivative multiplier (augmentedCandidate multiplier) using 1
    dsimp [augmentedCandidate]
    ring
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hx] with y hy
  exact (actual_augmented_branches multiplier y).2 hy.le

def actualMultiplier (n : ℕ) : ℝ := 2-2*(1/2:ℝ)^n
def actualPrimalStep (n : ℕ) : ℝ := augmentedCandidate (actualMultiplier n)

theorem actual_multiplier_range (n : ℕ) : 0 ≤ actualMultiplier n ∧ actualMultiplier n ≤ 2 := by
  have hp : 0 ≤ (1/2:ℝ)^n := pow_nonneg (by norm_num) n
  have hu : (1/2:ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  dsimp [actualMultiplier]
  constructor <;> linarith

theorem actual_primal_step_formula (n : ℕ) : actualPrimalStep n=1+(1/2:ℝ)*(1/2:ℝ)^n := by
  dsimp [actualPrimalStep,augmentedCandidate,actualMultiplier]
  ring

theorem actual_running_iteration (n : ℕ) :
    actualMultiplier 0=0 ∧
    (∀ x,augmentedObjective (actualMultiplier n) (actualPrimalStep n) ≤
      augmentedObjective (actualMultiplier n) x) ∧
    (∀ x,augmentedObjective (actualMultiplier n) x=
      augmentedObjective (actualMultiplier n) (actualPrimalStep n) ↔ x=actualPrimalStep n) ∧
    actualMultiplier (n+1)=multiplierUpdate (actualMultiplier n) (actualPrimalStep n) := by
  have hv := actual_augmented_candidate_and_update (actualMultiplier n) (actual_multiplier_range n).1
  refine ⟨by norm_num [actualMultiplier],?_,?_,?_⟩
  · intro x
    change augmentedObjective (actualMultiplier n) (augmentedCandidate (actualMultiplier n)) ≤ _
    rw [hv.1]
    exact (actual_augmented_global_unique _ (actual_multiplier_range n).1 x).1
  · intro x
    change _=augmentedObjective (actualMultiplier n) (augmentedCandidate (actualMultiplier n)) ↔ _
    rw [hv.1]
    exact (actual_augmented_global_unique _ (actual_multiplier_range n).1 x).2
  · change _=multiplierUpdate (actualMultiplier n) (augmentedCandidate (actualMultiplier n))
    rw [hv.2]
    dsimp [actualMultiplier]
    rw [pow_succ]
    ring

theorem actual_source_three_pairs :
    (actualPrimalStep 0,actualMultiplier 1)=((3/2:ℝ),1) ∧
    (actualPrimalStep 1,actualMultiplier 2)=((5/4:ℝ),3/2) ∧
    (actualPrimalStep 2,actualMultiplier 3)=((9/8:ℝ),7/4) := by
  norm_num [actualPrimalStep,augmentedCandidate,actualMultiplier]

theorem actual_running_primal_and_multiplier_limits :
    Tendsto actualPrimalStep atTop (𝓝 1) ∧ Tendsto actualMultiplier atTop (𝓝 2) := by
  have hp : Tendsto (fun n : ℕ => (1/2:ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  constructor
  · rw [show actualPrimalStep=(fun n : ℕ => 1+(1/2:ℝ)*(1/2:ℝ)^n) by
      funext n
      exact actual_primal_step_formula n]
    have h : Tendsto (fun n : ℕ => 1+(1/2:ℝ)*(1/2:ℝ)^n) atTop (𝓝 (1+(1/2:ℝ)*0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul hp)
    simpa only [mul_zero,add_zero] using h
  · change Tendsto (fun n : ℕ => 2-2*(1/2:ℝ)^n) atTop (𝓝 2)
    have h : Tendsto (fun n : ℕ => 2-2*(1/2:ℝ)^n) atTop (𝓝 (2-2*(0:ℝ))) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.mul hp)
    simpa only [mul_zero,sub_zero] using h

theorem actual_source_paired_iteration_limit :
    Tendsto (fun n : ℕ => (actualPrimalStep n,actualMultiplier (n+1))) atTop (𝓝 (1,2)) := by
  have hp := actual_running_primal_and_multiplier_limits
  have hm : Tendsto (fun n : ℕ => actualMultiplier (n+1)) atTop (𝓝 2) :=
    hp.2.comp (tendsto_add_atTop_nat 1)
  exact hp.1.prodMk_nhds hm

theorem actual_quad_source_candidates :
    candidate 2=(3/2:ℝ) ∧ candidate 18=(11/10:ℝ) ∧ candidate 198=(101/100:ℝ) := by
  norm_num [candidate]

theorem actual_quadratic_penalty_both_open_branch_curvatures (rho x : ℝ) :
    (x < 1 → HasDerivAt (deriv (quadraticPenalty rho)) 2 x) ∧
    (1 < x → HasDerivAt (deriv (quadraticPenalty rho)) (2+rho) x) := by
  constructor
  · intro hx
    have hd : HasDerivAt (fun y : ℝ => 2*(y-2)) 2 x := by
      convert ((hasDerivAt_id x).sub_const 2).const_mul 2 using 1 <;> simp
    apply hd.congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hx] with y hy
    exact (actual_penalty_derivative_below_one rho y hy).deriv
  · exact actual_penalty_second_derivative_above_one rho x

end SafeLearning.CompleteFoundationsAugmentedModels
