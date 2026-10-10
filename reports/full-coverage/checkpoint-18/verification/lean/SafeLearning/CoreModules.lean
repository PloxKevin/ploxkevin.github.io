import Mathlib

/-! Source-linked checks for Modules 8–11. See the JSON coverage ledger for limits.
All decimal constants below are exact real rational numbers, as in the exercises. -/
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CoreModules

-- cmdp.html: exercise-8-p1, p2, p5; the infinite series is proved, not truncated.
theorem discounted_constant (c γ : ℝ) (hγ : |γ| < 1) :
    (∑' t : ℕ, γ ^ t * c) = c / (1 - γ) := by
  rw [tsum_mul_right, tsum_geometric_of_abs_lt_one hγ]
  ring

theorem cmdp_p1 : (2 : ℝ) / (1 - 1/2) = 4 ∧
    (1/4 : ℝ) / (1 - 1/2) = 1/2 ∧ (1/2 : ℝ) ≤ 3/5 := by norm_num

theorem cmdp_p2 : (3/10 : ℝ) + 7/10 = 1 ∧
    ((3/10 : ℝ)*3 + 7/10)/(1-1/2) = 16/5 ∧
    ((3/10 : ℝ)*2)/(1-1/2) = 6/5 := by norm_num

theorem cmdp_p3 : (8 : ℝ) - 3/2*(5-4) = 13/2 ∧
    (8 : ℝ) - 3/2*(3-4) = 19/2 := by norm_num

theorem cmdp_p4 : max (0 : ℝ) (1/10+1/5*(3-2)) = 3/10 ∧
    max (0 : ℝ) (3/10+1/5*(0-2)) = 0 := by norm_num

theorem cmdp_p5_flow (r₀ r₁ : ℝ)
    (h₀ : r₀ = 1/2) (h₁ : r₁ = (r₀+r₁)/2) :
    r₀ = 1/2 ∧ r₁ = 1/2 ∧ (0*r₀+2*r₁)/(1-1/2) = 2 := by
  constructor
  · exact h₀
  constructor
  · linarith
  · have hr : r₁ = 1/2 := by linarith
    rw [h₀, hr]
    norm_num

theorem cmdp_p6_feasible (p : ℝ) :
    (0 ≤ p ∧ p ≤ 1 ∧ 4*p ≤ 1) ↔ (0 ≤ p ∧ p ≤ 1/4) := by constructor <;> rintro ⟨a,b⟩ <;> constructor <;> first | assumption | (constructor <;> linarith) | linarith

theorem cmdp_p6_optimal (p : ℝ) (hp : p ≤ 1/4) :
    2+6*p ≤ 7/2 := by linarith

theorem cmdp_p6_attained : (2 : ℝ)+6*(1/4) = 7/2 ∧ 4*(1/4 : ℝ) = 1 := by norm_num

-- The finite-distribution Rockafellar–Uryasev objective is explicit here.
def tailObjective (p high α ν : ℝ) : ℝ :=
  ν + ((1-p)*max (-ν) 0 + p*max (high-ν) 0)/(1-α)

theorem cmdp_p7_cvar : tailObjective (1/5) 10 (9/10) 10 = 10 ∧
    ∀ ν : ℝ, 10 ≤ tailObjective (1/5) 10 (9/10) ν := by
  constructor
  · norm_num [tailObjective]
  intro ν
  unfold tailObjective
  have h₀ := le_max_right (-ν) 0
  have h₁ := le_max_left (10-ν) 0
  have h₂ := le_max_right (10-ν) 0
  norm_num [div_eq_mul_inv]
  by_cases h : ν ≤ 10
  · linarith
  · linarith

def binaryCDF (p high z : ℝ) : ℝ :=
  if z < 0 then 0 else if z < high then 1-p else 1

theorem cmdp_p7_var : (1/5 : ℝ)*10 = 2 ∧
    9/10 ≤ binaryCDF (1/5) 10 10 ∧
    ∀ z : ℝ, z < 10 → binaryCDF (1/5) 10 z < 9/10 := by
  constructor
  · norm_num
  constructor
  · norm_num [binaryCDF]
  intro z hz
  unfold binaryCDF
  split_ifs <;> norm_num

theorem cmdp_p11_var : 19/20 ≤ binaryCDF (1/100) 100 0 ∧
    ∀ z : ℝ, z < 0 → binaryCDF (1/100) 100 z < 19/20 := by
  constructor
  · norm_num [binaryCDF]
  intro z hz
  simp [binaryCDF, hz]

theorem cmdp_p8 : ((2-1 : ℝ)/(1/2)) = 2 ∧
    ((2-3/2 : ℝ)/(1/2)) = 1 ∧
    (2 : ℝ)-(1+(1/2)*(3/2)) = (1/2)^2*1 := by norm_num

def dual8 (l : ℝ) : ℝ := max (2+l) (8-3*l)

theorem cmdp_p9_upper (p l : ℝ) (h₀ : 0 ≤ p) (h₁ : p ≤ 1) :
    2+6*p-l*(4*p-1) ≤ dual8 l := by
  have a := le_max_left (2+l) (8-3*l)
  have b := le_max_right (2+l) (8-3*l)
  change 2+6*p-l*(4*p-1) ≤ max (2+l) (8-3*l)
  by_cases h : 0 ≤ 6-4*l
  · have := mul_le_mul_of_nonneg_left h₁ h
    nlinarith
  · have := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge h) h₀
    nlinarith

theorem cmdp_p9_dual_min (l : ℝ) : 7/2 ≤ dual8 l := by
  have a := le_max_left (2+l) (8-3*l)
  have b := le_max_right (2+l) (8-3*l)
  unfold dual8
  linarith

theorem cmdp_p9_dual_attained : dual8 (3/2) = 7/2 := by norm_num [dual8]

theorem cmdp_p9_all_maximize (p : ℝ) :
    2+6*p-(3/2)*(4*p-1) = 7/2 := by ring

theorem cmdp_p10 : max ((1+(-1) : ℝ)/2) 0 = 0 ∧
    (max (1 : ℝ) 0+max (-1 : ℝ) 0)/2 = 1/2 := by norm_num

theorem cmdp_p11_cvar : (1/100 : ℝ)*100 = 1 ∧
    tailObjective (1/100) 100 (19/20) 0 = 20 ∧
    ∀ ν : ℝ, 20 ≤ tailObjective (1/100) 100 (19/20) ν := by
  constructor
  · norm_num
  constructor
  · norm_num [tailObjective]
  intro ν
  unfold tailObjective
  have a := le_max_left (-ν) 0
  have b := le_max_right (-ν) 0
  have c := le_max_left (100-ν) 0
  norm_num [div_eq_mul_inv]
  by_cases h : 0 ≤ ν <;> linarith

theorem weak_duality_max (reward cost budget l bound : ℝ)
    (hl : 0 ≤ l) (hcost : cost ≤ budget)
    (hbound : reward-l*(cost-budget) ≤ bound) : reward ≤ bound := by
  have := mul_nonpos_of_nonneg_of_nonpos hl (sub_nonpos.mpr hcost)
  linarith

theorem dual_subgradient (reward cost budget l l' D D' : ℝ)
    (hmax : D = reward-l*(cost-budget))
    (hbound : reward-l'*(cost-budget) ≤ D') :
    D + (l'-l)*(budget-cost) ≤ D' := by nlinarith

-- Legacy cmdp.html Exercise8.3: exact universal LP bound and unique optimum.
theorem cmdp_legacy_two_state (p₁ p₂ : ℝ) (h₂ : 0 ≤ p₂)
    (hbudget : p₁+p₂ ≤ 9/10) : (4/3)*p₁+(2/3)*p₂ ≤ 6/5 := by linarith

theorem cmdp_legacy_two_state_unique (p₁ p₂ : ℝ) (h₂ : 0 ≤ p₂)
    (hbudget : p₁+p₂ ≤ 9/10) (hopt : (4/3)*p₁+(2/3)*p₂ = 6/5) :
    p₁ = 9/10 ∧ p₂ = 0 := by constructor <;> linarith

def legacyTail (ν : ℝ) : ℝ :=
  ν+20*((9/10)*max (-ν) 0+(2/25)*max (10-ν) 0+(1/50)*max (100-ν) 0)

theorem cmdp_legacy_cvar : legacyTail 10 = 46 ∧ ∀ ν : ℝ, 46 ≤ legacyTail ν := by
  constructor
  · norm_num [legacyTail]
  intro ν
  unfold legacyTail
  have a := le_max_left (-ν) 0
  have b := le_max_right (-ν) 0
  have c := le_max_left (10-ν) 0
  have d := le_max_right (10-ν) 0
  have e := le_max_left (100-ν) 0
  by_cases h : ν ≤ 10 <;> linarith

-- Policy optimization9.P1–P12.
theorem policy_p1 : (1/4 : ℝ)*5+(3/4)*1 = 2 ∧
    (1/4 : ℝ)*3+(3/4)*(-1) = 0 ∧ (1/2 : ℝ)*3+(1/2)*(-1) = 1 := by norm_num

theorem policy_p2_tv : (|((3/4 : ℝ)-1/2)|+|((1/4 : ℝ)-1/2)|)/2 = 1/4 := by norm_num

theorem policy_p3_axes (x y : ℝ) :
    ((1/2)*(4*x^2+y^2) ≤ (1/2 : ℝ)) ↔ 4*x^2+y^2 ≤ 1 := by constructor <;> intro h <;> linarith

theorem policy_p4 : (-1/5 : ℝ)+3/10 > 0 ∧ (-1/5 : ℝ)+1/10 < 0 := by norm_num

theorem policy_p5_bound (x y : ℝ) (h : x^2+4*y^2 ≤ 1) :
    x+2*y ≤ Real.sqrt 2 := by
  have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  nlinarith [sq_nonneg (x-2*y)]

theorem policy_p5_attained :
    (1/Real.sqrt 2)^2+4*(1/(2*Real.sqrt 2))^2 = 1 ∧
    1/Real.sqrt 2+2*(1/(2*Real.sqrt 2)) = Real.sqrt 2 := by
  have hp : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  constructor <;> field_simp <;> nlinarith

theorem policy_p6_projection (x y : ℝ) (hx : x ≤ 1/10) :
    1/8 ≤ (1/2)*((x-3/5)^2+(y-1/5)^2) := by
  have h : x-3/5 ≤ -1/2 := by linarith
  nlinarith [sq_nonneg (y-1/5)]

theorem policy_p7 : (2 : ℝ)*(9/10)*(1/2)*(1/100)/(1-9/10)^2 = 9/10 ∧
    (2 : ℝ)*(1/2)*(1/2)*(1/100)/(1-1/2)^2 = 1/50 := by norm_num

theorem policy_p8 (cost : ℝ) (hc : cost ≤ 5+2) : cost ≤ 8 := by linarith

theorem policy_p9_bound (x y : ℝ) (hd : x^2+y^2 ≤ 1) (hx : x ≤ 1/5) :
    x+y ≤ 1/5+Real.sqrt (24/25) := by
  have hs : (Real.sqrt (24/25))^2 = (24/25 : ℝ) := Real.sq_sqrt (by norm_num)
  have hr : (1/5 : ℝ) ≤ Real.sqrt (24/25) := by
    have := Real.sqrt_nonneg (24/25 : ℝ)
    nlinarith
  have hpos : 0 < Real.sqrt (24/25 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsupport : (1/5)*x+Real.sqrt (24/25)*y ≤ 1 := by
    nlinarith [sq_nonneg (x-1/5), sq_nonneg (y-Real.sqrt (24/25))]
  have hc := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hr) (sub_nonpos.mpr hx)
  nlinarith

theorem policy_p9_attained : (1/5 : ℝ)^2+(Real.sqrt (24/25))^2 = 1 := by
  rw [Real.sq_sqrt (by norm_num)]
  norm_num

theorem policy_p10_root :
    -(1/10 : ℝ)+( (-1+Real.sqrt (9/5))/4)+2*((-1+Real.sqrt (9/5))/4)^2 = 0 := by
  have := Real.sq_sqrt (show (0 : ℝ) ≤ 9/5 by norm_num)
  nlinarith

theorem policy_p10_linear_fails : -(1/10 : ℝ)+1/10+2*(1/10)^2 = 1/50 := by norm_num

theorem policy_p11_weights : (99/100 : ℝ)*((1/2)/(99/100))+
    (1/100)*((1/2)/(1/100)) = 1 ∧ (1/2 : ℝ)/(1/100) = 50 := by norm_num

theorem policy_p12_margins : (1 : ℝ)-1/50-3/100 = 19/20 ∧
    (2/5 : ℝ)-3/10 > 0 ∧ (7 : ℝ)+1/2 ≤ 8 := by norm_num

-- Barrier functions10.P1–P12.
theorem barrier_p1_safe_set (x : ℝ) : 0 ≤ 1-x^2 ↔ -1 ≤ x ∧ x ≤ 1 := by
  constructor
  · intro h; constructor <;> nlinarith
  · rintro ⟨a,b⟩; nlinarith [mul_nonneg (by linarith : 0 ≤ x+1) (by linarith : 0 ≤ 1-x)]

theorem barrier_p2 (x u : ℝ) : 0 ≤ u+2*x ↔ -2*x ≤ u := by constructor <;> intro h <;> linarith

theorem barrier_p3_optimal (u : ℝ) (hu : -1 ≤ u) : 2 ≤ (1/2)*(u+3)^2 := by nlinarith

theorem barrier_p3_attained : (-1 : ℝ) ≥ -1 ∧ (-1 : ℝ)-(-3) = 2 ∧
    (1/2 : ℝ)*(-1+3)^2 = 2 := by norm_num

theorem barrier_p3_unique (u : ℝ) (hu : -1 ≤ u)
    (he : (1/2)*(u+3)^2 = 2) : u = -1 := by nlinarith

theorem barrier_p4_interval (x t : ℝ) (hx : 0 ≤ x ∧ x ≤ 2) (ht : 0 ≤ t) :
    0 ≤ 1+(x-1)*Real.exp (-t) ∧ 1+(x-1)*Real.exp (-t) ≤ 2 := by
  have he₀ := Real.exp_pos (-t)
  have he₁ : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have a := mul_nonneg hx.1 (le_of_lt he₀)
  have b := mul_le_mul_of_nonneg_right hx.2 (le_of_lt he₀)
  constructor <;> nlinarith

theorem barrier_p5_optimal (u v : ℝ) (h : 1 ≤ u+v) : 1/4 ≤ (1/2)*(u^2+v^2) := by
  nlinarith [sq_nonneg (u-v)]

theorem barrier_p5_unique (u v : ℝ) (h : 1 ≤ u+v)
    (he : (1/2)*(u^2+v^2) = 1/4) : u = 1/2 ∧ v = 1/2 := by
  constructor <;> nlinarith [sq_nonneg (u-v), sq_nonneg (u-1/2), sq_nonneg (v-1/2)]

theorem barrier_p5_attained_kkt : (1 : ℝ) ≤ 1/2+1/2 ∧
    (1/2 : ℝ)*((1/2)^2+(1/2)^2) = 1/4 ∧ (0 : ℝ) ≤ 1/2 ∧
    (1/2 : ℝ)-1/2 = 0 ∧ (1/2 : ℝ)*(1-1/2-1/2) = 0 := by norm_num

theorem barrier_p6_infeasible : ¬ ∃ u : ℝ, u ≤ 1/5 ∧ 0 ≤ -1+u+1/10 := by rintro ⟨u,a,b⟩; linarith

theorem barrier_p6_feasible (u : ℝ) (hu : -1/5 ≤ u) : 0 ≤ -1+u+2 := by linarith

theorem barrier_p7_robust (u x : ℝ) :
    (∀ w : ℝ, |w| ≤ 3/10 → 0 ≤ u+w+x) ↔ 3/10-x ≤ u := by
  constructor
  · intro h; have := h (-3/10) (by norm_num); linarith
  · intro h w hw; have := (abs_le.mp hw).1; linarith

theorem barrier_p8 : (-2/5 : ℝ)+1 = 3/5 ∧
    (2 : ℝ)*(-2/5)+1 = 1/5 ∧ (1/10 : ℝ)-1 = -9/10 := by norm_num

theorem barrier_p9_counterexample (t : ℝ) (ht : 0 < t) :
    (3 : ℝ)*0^2*(-1) = 0 ∧ ¬ 0 ≤ (-t)^3 := by constructor <;> nlinarith [pow_pos ht 3]

theorem barrier_p10_held_interval (Δ : ℝ) (hΔ : 0 ≤ Δ) :
    (∀ t : ℝ, 0 ≤ t → t ≤ Δ → 0 ≤ 1-t) ↔ Δ ≤ 1 := by
  constructor
  · intro h; have := h Δ hΔ le_rfl; linarith
  · intro h t ht htd; linarith

theorem barrier_p10_continuous (t : ℝ) : 0 < Real.exp (-t) := Real.exp_pos _

theorem barrier_p11_plan : (1 : ℝ)-1/2 = 1/2 ∧
    (1/2 : ℝ)-1/4 = 1/4 ∧ (1/4 : ℝ)-1/4 = 0 := by norm_num

theorem barrier_p11_terminal (x : ℝ) (h : |x| ≤ 1/4) :
    |(-x)| ≤ 1/2 ∧ |x+(-x)| ≤ 1/4 := by rw [abs_neg]; constructor <;> first | linarith | norm_num

inductive ShieldState | a | b | failure deriving DecidableEq
inductive ShieldAction | left | right deriving DecidableEq
def safe (s : ShieldState) : Prop := s ≠ .failure
def successor : ShieldState → ShieldAction → ShieldState
  | .a, .left => .b
  | .a, .right => .failure
  | .b, .left => .a
  | .b, .right => .b
  | .failure, _ => .failure
theorem barrier_p12_shield :
    safe (successor .a .left) ∧ ¬ safe (successor .a .right) ∧
    safe (successor .b .left) ∧ safe (successor .b .right) ∧
    ¬ (∀ s ∈ ({ShieldState.b, ShieldState.failure} : Finset ShieldState), safe s) := by
  simp [safe, successor]

-- Lyapunov/MPC11.P1–P12.
theorem lyapunov_p1_decrease (x : ℝ) : ((3/5)*x)^2-x^2 = -(16/25)*x^2 := by ring

theorem lyapunov_p1_strict (x : ℝ) (hx : x ≠ 0) : ((3/5)*x)^2-x^2 < 0 := by
  have := sq_pos_of_ne_zero hx
  nlinarith

theorem lyapunov_p1_sublevel (x : ℝ) : x^2 ≤ 4 ↔ -2 ≤ x ∧ x ≤ 2 := by
  constructor
  · intro h; constructor <;> nlinarith
  · rintro ⟨a,b⟩; nlinarith [mul_nonneg (by linarith : 0 ≤ x+2) (by linarith : 0 ≤ 2-x)]

theorem lyapunov_p2 : (4 : ℝ)*(2/5)^2+(1/2)^2 = 89/100 ∧
    (4 : ℝ)*(3/5)^2 = 36/25 := by norm_num

theorem lyapunov_p3 (w : ℝ) (hw : |w| ≤ 1/10) :
    ((1/2)*(2/5)+w)^2-(2/5)^2 ≤ -(7/100) := by
  rcases abs_le.mp hw with ⟨a,b⟩
  nlinarith [mul_nonneg (by linarith : 0 ≤ w+1/10) (by linarith : 0 ≤ 1/10-w)]

theorem lyapunov_p4 : (7/10 : ℝ)-((1/5)+(1/2)*(4/5)) = 1/10 := by norm_num

theorem lyapunov_p5_transfer (d dg error distance : ℝ)
    (hs : dg ≤ -3/25) (he : error ≤ 1/50) (hr : distance ≤ 1/100)
    (h : d ≤ dg+error+5*distance) : d ≤ -1/20 := by linarith

theorem lyapunov_p5_coarser : (-3/25 : ℝ)+1/50+5*(3/100) = 1/20 := by norm_num

theorem lyapunov_p6_tube (e w : ℝ) (he : |e| ≤ 1/5) (hw : |w| ≤ 1/10) :
    |(1/2)*e+w| ≤ 1/5 := by
  rcases abs_le.mp he with ⟨a,b⟩
  rcases abs_le.mp hw with ⟨c,d⟩
  apply abs_le.mpr; constructor <;> linarith

theorem lyapunov_p6_state (z e : ℝ) (hz : |z| ≤ 4/5) (he : |e| ≤ 1/5) : |z+e| ≤ 1 := by
  calc |z+e| ≤ |z|+|e| := abs_add_le _ _
    _ ≤ 1 := by linarith

theorem lyapunov_p6_input (v e : ℝ) (hv : |v| ≤ 9/10) (he : |e| ≤ 1/5) :
    |v-(1/2)*e| ≤ 1 := by
  rcases abs_le.mp hv with ⟨a,b⟩
  rcases abs_le.mp he with ⟨c,d⟩
  apply abs_le.mpr; constructor <;> linarith

theorem lyapunov_p7_optimal (u : ℝ) (hu : -1/2 ≤ u) :
    7/4 ≤ 1+u^2+2*(1+u)^2 := by
  have h : 0 ≤ u+1/2 := by linarith
  nlinarith [sq_nonneg (u+1/2)]

theorem lyapunov_p7_attained : (1 : ℝ)+(-1/2)^2+2*(1-1/2)^2 = 7/4 := by norm_num

theorem lyapunov_p9_identity (x : ℝ) : (x-x^3)^2-x^2 = x^4*(x^2-2) := by ring

theorem lyapunov_p9_strict (x : ℝ) (hx : x ≠ 0) (hb : x^2 < 2) :
    (x-x^3)^2-x^2 < 0 := by
  rw [lyapunov_p9_identity]
  exact mul_neg_of_pos_of_neg (pow_pos (sq_pos_of_ne_zero hx) 2 |>.trans_eq (by ring)) (by linarith)

theorem lyapunov_p9_invariant (x : ℝ) (hx : x^2 ≤ 1) : (x-x^3)^2 ≤ 1 := by
  have h : (x-x^3)^2 ≤ x^2 := by
    rw [← sub_nonpos, lyapunov_p9_identity]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  linarith

theorem lyapunov_p9_two_cycle :
    Real.sqrt 2-(Real.sqrt 2)^3 = -Real.sqrt 2 ∧
    (-Real.sqrt 2)-(-Real.sqrt 2)^3 = Real.sqrt 2 := by
  have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  constructor <;> nlinarith [congrArg (fun z : ℝ => Real.sqrt 2*z) hs]

theorem lyapunov_p10_relative (x e : ℝ) (he : |e| ≤ (1/10)*|x|) :
    |(1/2)*x+e| ≤ (3/5)*|x| := by
  calc |(1/2)*x+e| ≤ |(1/2)*x|+|e| := abs_add_le _ _
    _ ≤ (3/5)*|x| := by rw [abs_mul]; norm_num; linarith

theorem lyapunov_p10_absolute_counterexample :
    |(1/10 : ℝ)| ≤ 1/10 ∧ (1/2 : ℝ)*(1/5)+1/10 = 1/5 ∧ (1/5 : ℝ) ≠ 0 := by norm_num

-- Exact powers verify both integer thresholds without floating point logarithms.
set_option exponentiation.threshold 1000 in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem lyapunov_p11_single :
    (99/100 : ℚ)^299 ≤ 1/20 ∧ 1/20 < (99/100 : ℚ)^298 := by norm_num [div_pow]

set_option exponentiation.threshold 1000 in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem lyapunov_p11_twenty :
    (99/100 : ℚ)^597 ≤ 1/400 ∧ 1/400 < (99/100 : ℚ)^596 := by norm_num [div_pow]

theorem lyapunov_p12_budget : (1 : ℝ)-1/100-1/50 = 97/100 := by norm_num

end SafeLearning.CoreModules
