import SafeLearning.CompleteFoundationsPenaltyModels

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Set
namespace SafeLearning.CompleteFoundationsExactPenaltyModels
open CompleteFoundationsPenaltyModels

def exactPenalty (rho x : ℝ) : ℝ := objective x+rho*max (x-1) 0

theorem actual_exact_penalty_branches (rho x : ℝ) :
    (x ≤ 1 → exactPenalty rho x=objective x) ∧
    (1 ≤ x → exactPenalty rho x=objective x+rho*(x-1)) := by
  constructor
  · intro h
    simp [exactPenalty,max_eq_right (show x-1 ≤ 0 by linarith)]
  · intro h
    rw [exactPenalty,max_eq_left (show 0 ≤ x-1 by linarith)]

theorem actual_exact_penalty_upper_weight_global_unique (rho : ℝ) (hrho : 2 ≤ rho) (x : ℝ) :
    1 ≤ exactPenalty rho x ∧ (exactPenalty rho x=1 ↔ x=1) := by
  by_cases hx : x ≤ 1
  · rw [(actual_exact_penalty_branches rho x).1 hx]
    dsimp [objective]
    constructor
    · nlinarith [sq_nonneg (x-1)]
    · constructor <;> intro h <;> nlinarith [sq_nonneg (x-1)]
  · rw [(actual_exact_penalty_branches rho x).2 (by linarith)]
    have he : objective x+rho*(x-1)=1+(x-1)^2+(rho-2)*(x-1) := by
      dsimp [objective]
      ring
    rw [he]
    have hp := mul_nonneg (show 0 ≤ rho-2 by linarith) (show 0 ≤ x-1 by linarith)
    constructor
    · nlinarith [sq_nonneg (x-1)]
    · constructor <;> intro h <;> nlinarith [sq_nonneg (x-1)]

theorem actual_exact_penalty_below_weight_global_unique (rho : ℝ)
    (hrho : 0 ≤ rho) (hupper : rho < 2) (x : ℝ) :
    rho-rho^2/4 ≤ exactPenalty rho x ∧
      (exactPenalty rho x=rho-rho^2/4 ↔ x=2-rho/2) := by
  have hless : rho-rho^2/4 < 1 := by
    have hp := sq_pos_of_ne_zero (show rho-2 ≠ 0 by linarith)
    nlinarith
  by_cases hx : x ≤ 1
  · rw [(actual_exact_penalty_branches rho x).1 hx]
    have hobj : 1 ≤ objective x := by dsimp [objective];nlinarith [sq_nonneg (x-1)]
    refine ⟨by linarith,?_⟩
    constructor <;> intro h <;> nlinarith
  · rw [(actual_exact_penalty_branches rho x).2 (by linarith)]
    have he : objective x+rho*(x-1)=(x-(2-rho/2))^2+rho-rho^2/4 := by
      dsimp [objective]
      ring
    rw [he]
    constructor
    · nlinarith [sq_nonneg (x-(2-rho/2))]
    · constructor
      · intro h
        have hz : (x-(2-rho/2))^2=0 := by nlinarith
        exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
      · intro h
        rw [h]
        ring

theorem actual_exactness_threshold (rho : ℝ) (hrho : 0 ≤ rho) :
    (∀ x,exactPenalty rho 1 ≤ exactPenalty rho x) ↔ 2 ≤ rho := by
  have hvalue : exactPenalty rho 1=1 := by norm_num [exactPenalty,objective]
  rw [hvalue]
  constructor
  · intro h
    by_contra hn
    have hupper : rho < 2 := by linarith
    have hv := (actual_exact_penalty_below_weight_global_unique rho hrho hupper (2-rho/2)).2.mpr rfl
    have hp := sq_pos_of_ne_zero (show rho-2 ≠ 0 by linarith)
    have hh := h (2-rho/2)
    rw [hv] at hh
    nlinarith
  · intro h x
    exact (actual_exact_penalty_upper_weight_global_unique rho h x).1

theorem actual_exact_penalty_right_derivative (rho x : ℝ) :
    HasDerivAt (fun y : ℝ => objective y+rho*(y-1)) (2*(x-2)+rho) x := by
  convert (actual_objective_derivative x).add (((hasDerivAt_id x).sub_const 1).const_mul rho) using 1
  · rfl
  · simp

theorem actual_exact_penalty_one_sided_derivatives (rho : ℝ) :
    HasDerivWithinAt (exactPenalty rho) (-2) (Iic 1) 1 ∧
    HasDerivWithinAt (exactPenalty rho) (rho-2) (Ici 1) 1 := by
  constructor
  · have h : HasDerivAt objective (-2) 1 := by convert actual_objective_derivative 1 using 1 <;> norm_num
    apply h.hasDerivWithinAt.congr_of_mem
    · intro x hx
      exact (actual_exact_penalty_branches rho x).1 hx
    · simp
  · have h : HasDerivAt (fun y : ℝ => objective y+rho*(y-1)) (rho-2) 1 := by
      convert actual_exact_penalty_right_derivative rho 1 using 1 <;> ring
    apply h.hasDerivWithinAt.congr_of_mem
    · intro x hx
      exact (actual_exact_penalty_branches rho x).2 hx
    · simp

theorem actual_exact_penalty_is_nondifferentiable_at_threshold (rho : ℝ) (hrho : 2 ≤ rho) :
    ¬ DifferentiableAt ℝ (exactPenalty rho) 1 := by
  intro h
  have hd := h.hasDerivAt
  have hl := (actual_exact_penalty_one_sided_derivatives rho).1
  have hu := (actual_exact_penalty_one_sided_derivatives rho).2
  have he1 := (uniqueDiffWithinAt_Iic (1 : ℝ)).eq_deriv (Iic 1) hl hd.hasDerivWithinAt
  have he2 := (uniqueDiffWithinAt_Ici (1 : ℝ)).eq_deriv (Ici 1) hu hd.hasDerivWithinAt
  linarith

def slackObjective (price x slack : ℝ) : ℝ := objective x+price*slack
def slackFeasible (x slack : ℝ) : Prop := x ≤ 1+slack ∧ 0 ≤ slack

theorem actual_slack_objective_dominates_exact_penalty (price x slack : ℝ)
    (hp : 0 ≤ price) (hf : slackFeasible x slack) : exactPenalty price x ≤ slackObjective price x slack := by
  have hm : max (x-1) 0 ≤ slack := max_le (by linarith [hf.1]) hf.2
  change objective x+price*max (x-1) 0 ≤ objective x+price*slack
  exact add_le_add_right (mul_le_mul_of_nonneg_left hm hp) _

theorem actual_slack_lower_price_optimum (price : ℝ) (hp : 0 ≤ price) (hupper : price < 2) :
    slackFeasible (2-price/2) (1-price/2) ∧
    slackObjective price (2-price/2) (1-price/2)=price-price^2/4 ∧
    (∀ x slack,slackFeasible x slack →
      slackObjective price (2-price/2) (1-price/2) ≤ slackObjective price x slack) := by
  have hv : slackObjective price (2-price/2) (1-price/2)=price-price^2/4 := by
    dsimp [slackObjective,objective]
    ring
  refine ⟨⟨by linarith,by linarith⟩,hv,?_⟩
  intro x slack hf
  rw [hv]
  exact (actual_exact_penalty_below_weight_global_unique price hp hupper x).1.trans
    (actual_slack_objective_dominates_exact_penalty price x slack hp hf)

theorem actual_slack_upper_price_optimum (price : ℝ) (hp : 2 ≤ price) :
    slackFeasible 1 0 ∧ slackObjective price 1 0=1 ∧
    (∀ x slack,slackFeasible x slack → slackObjective price 1 0 ≤ slackObjective price x slack) := by
  refine ⟨by norm_num [slackFeasible],by norm_num [slackObjective,objective],?_⟩
  intro x slack hf
  norm_num [slackObjective,objective]
  exact (actual_exact_penalty_upper_weight_global_unique price hp x).1.trans
    (actual_slack_objective_dominates_exact_penalty price x slack (by linarith) hf)

theorem actual_source_slack_violation : slackFeasible (3/2) (1/2) ∧
    (∀ x slack,slackFeasible x slack → slackObjective 1 (3/2) (1/2) ≤ slackObjective 1 x slack) ∧
    ¬ constraint (3/2) ≤ 0 := by
  have h := actual_slack_lower_price_optimum 1 (by norm_num) (by norm_num)
  norm_num at h
  exact ⟨h.1,h.2.2,by norm_num [constraint]⟩

theorem actual_finite_softening_feasible {X : Type*} {n : ℕ} (g : Fin n → X → ℝ) (x : X) :
    ∃ slack : Fin n → ℝ,∀ i,0 ≤ slack i ∧ g i x ≤ slack i := by
  exact ⟨fun i => max (g i x) 0,fun i => ⟨le_max_right _ _,le_max_left _ _⟩⟩

def nonconvexObjective (x : ℝ) : ℝ := -x^4
def nonconvexConstraint (x : ℝ) : ℝ := x^2-1
def nonconvexPenalty (rho x : ℝ) : ℝ := nonconvexObjective x+rho*max (nonconvexConstraint x) 0

theorem actual_nonconvex_constrained_global_minima (x : ℝ) (hx : nonconvexConstraint x ≤ 0) :
    -1 ≤ nonconvexObjective x ∧ (nonconvexObjective x= -1 ↔ x=1 ∨ x= -1) := by
  have hs : x^2 ≤ 1 := by dsimp [nonconvexConstraint] at hx;linarith
  have he : x^4=(x^2)^2 := by ring
  have hn := sq_nonneg x
  dsimp [nonconvexObjective]
  rw [he]
  constructor
  · nlinarith
  · constructor
    · intro h
      have hz : x^2=1 := by nlinarith
      have hz' : x^2=(1 : ℝ)^2 := by simpa using hz
      rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hz' with h|h
      · exact Or.inl h
      · exact Or.inr h
    · rintro (rfl|rfl) <;> norm_num

theorem actual_nonconvex_lagrangian_derivative (multiplier x : ℝ) :
    HasDerivAt (fun y : ℝ => nonconvexObjective y+multiplier*nonconvexConstraint y)
      (-4*x^3+2*multiplier*x) x := by
  convert (((hasDerivAt_id x).pow 4).neg).add
    ((((hasDerivAt_id x).pow 2).sub_const 1).const_mul multiplier) using 1
  · rfl
  · norm_num [id_eq]
    ring

theorem actual_nonconvex_source_kkt :
    (∀ x : ℝ,x=1 ∨ x= -1 → nonconvexConstraint x=0 ∧
      (0 : ℝ) ≤ 2 ∧ (2 : ℝ)*nonconvexConstraint x=0 ∧
      deriv (fun y : ℝ => nonconvexObjective y+2*nonconvexConstraint y) x=0) := by
  intro x hx
  rw [(actual_nonconvex_lagrangian_derivative 2 x).deriv]
  rcases hx with rfl|rfl <;> norm_num [nonconvexConstraint]

theorem actual_nonconvex_penalty_unbounded_below (rho bound : ℝ) :
    ∃ x,nonconvexPenalty rho x < bound := by
  let r : ℝ := max rho 0
  let v : ℝ := r+|bound|+2
  have hr : 0 ≤ r := le_max_right _ _
  have hrr : rho ≤ r := le_max_left _ _
  have hb : 0 ≤ |bound| := abs_nonneg _
  have hv : 1 < v := by dsimp [v];linarith
  have hs : (Real.sqrt v)^2=v := Real.sq_sqrt (by linarith)
  have hp : rho*(v-1) ≤ r*(v-1) := mul_le_mul_of_nonneg_right hrr (by linarith)
  refine ⟨Real.sqrt v,?_⟩
  dsimp [nonconvexPenalty,nonconvexObjective,nonconvexConstraint]
  rw [show (Real.sqrt v)^4=((Real.sqrt v)^2)^2 by ring,hs,
    max_eq_left (show 0 ≤ v-1 by linarith)]
  have hneg := neg_abs_le bound
  have hp0 := mul_nonneg hr hb
  dsimp [v] at hp ⊢
  nlinarith [sq_nonneg |bound|]

end SafeLearning.CompleteFoundationsExactPenaltyModels
