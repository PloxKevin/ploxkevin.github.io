import Mathlib
import SafeLearning.CoreModules

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SafeLearning.CompleteAlternatingCMDP

def state (n : ℕ) : Fin 2 := ⟨n % 2, Nat.mod_lt _ (by norm_num)⟩
def stateLaw (n : ℕ) : PMF (Fin 2) := PMF.pure (state n)
def indicator (s : Fin 2) (n : ℕ) : ℝ := if state n = s then 1 else 0
def discountedMass (s : Fin 2) : ℝ := ∑' n : ℕ, (1 / 2 : ℝ) ^ n * indicator s n
def occupancy (s : Fin 2) : ℝ := (1 / 2) * discountedMass s

theorem genuine_state_probability (s : Fin 2) (n : ℕ) :
    (stateLaw n s).toReal = indicator s n := by
  by_cases h : s = state n
  · simp [stateLaw, indicator, PMF.pure_apply, h]
  · simp [stateLaw, indicator, PMF.pure_apply, h, Ne.symm h]

theorem actual_alternation (n : ℕ) :
    indicator 0 (n + 1) = indicator 1 n ∧
      indicator 1 (n + 1) = indicator 0 n := by
  have h : n % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have h0 : (n + 1) % 2 = 0 ↔ n % 2 = 1 := by omega
  have h1 : (n + 1) % 2 = 1 ↔ n % 2 = 0 := by omega
  simp [indicator, state, Fin.ext_iff, h0, h1]

theorem discounted_mass_summable (s : Fin 2) :
    Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n * indicator s n) := by
  refine Summable.of_nonneg_of_le ?_ ?_
    (summable_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1))
  · intro n
    unfold indicator
    split_ifs <;> positivity
  · intro n
    unfold indicator
    split_ifs <;> simp

theorem genuine_discounted_flow_constraints :
    occupancy 0 = 1 / 2 + (1 / 2) * occupancy 1 ∧
      occupancy 1 = (1 / 2) * occupancy 0 := by
  have h0 : discountedMass 0 = 1 + (1 / 2) * discountedMass 1 := by
    unfold discountedMass
    rw [(discounted_mass_summable 0).tsum_eq_zero_add]
    simp only [pow_zero]
    rw [show indicator 0 0 = 1 by norm_num [indicator, state]]
    simp only [mul_one]
    congr 1
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [(actual_alternation n).1, pow_succ]
    ring
  have h1 : discountedMass 1 = (1 / 2) * discountedMass 0 := by
    unfold discountedMass
    rw [(discounted_mass_summable 1).tsum_eq_zero_add]
    simp only [pow_zero]
    rw [show indicator 1 0 = 0 by norm_num [indicator, state]]
    simp only [mul_zero, zero_add]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [(actual_alternation n).2, pow_succ]
    ring
  unfold occupancy
  constructor <;> linarith

theorem genuine_state_marginals_and_normalization :
    occupancy 0 = 2 / 3 ∧ occupancy 1 = 1 / 3 ∧ occupancy 0 + occupancy 1 = 1 := by
  obtain ⟨h0, h1⟩ := genuine_discounted_flow_constraints
  constructor
  · linarith
  constructor <;> linarith

def reward (p1 p2 : ℝ) : ℝ := (4 / 3) * p1 + (2 / 3) * p2
def cost (p1 p2 : ℝ) : ℝ := (4 / 3) * (p1 + p2)
def feasible (p1 p2 : ℝ) : Prop := p1 ∈ Icc 0 1 ∧ p2 ∈ Icc 0 1 ∧ cost p1 p2 ≤ 6 / 5
def lagrangian (p1 p2 price : ℝ) : ℝ := reward p1 p2 - price * (cost p1 p2 - 6 / 5)
def dual (price : ℝ) : ℝ :=
  (4 / 3) * max 0 (1 - price) + (2 / 3) * max 0 (1 - 2 * price) + (6 / 5) * price

theorem literal_source_LP_feasible_iff (p1 p2 : ℝ) : feasible p1 p2 ↔
    0 ≤ p1 ∧ 0 ≤ p2 ∧ p1 + p2 ≤ 9 / 10 := by
  unfold feasible cost
  constructor
  · rintro ⟨h1, h2, hcost⟩
    exact ⟨h1.1, h2.1, by linarith⟩
  · rintro ⟨h1, h2, hcost⟩
    exact ⟨⟨h1, by linarith⟩, ⟨h2, by linarith⟩, by linarith⟩

theorem genuine_unique_LP_optimum (p1 p2 : ℝ) (hp : feasible p1 p2) :
    reward p1 p2 ≤ 6 / 5 ∧
      (reward p1 p2 = 6 / 5 ↔ p1 = 9 / 10 ∧ p2 = 0) := by
  obtain ⟨h1, h2, hb⟩ := (literal_source_LP_feasible_iff p1 p2).mp hp
  unfold reward
  constructor
  · linarith
  · constructor
    · intro he
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨rfl, rfl⟩
      norm_num

theorem actual_optimum_and_binding_budget :
    feasible (9 / 10) 0 ∧ reward (9 / 10) 0 = 6 / 5 ∧ cost (9 / 10) 0 = 6 / 5 := by
  norm_num [feasible, reward, cost]

theorem actual_lagrangian_decomposition (p1 p2 price : ℝ) :
    lagrangian p1 p2 price = (4 / 3) * (1 - price) * p1 +
      (2 / 3) * (1 - 2 * price) * p2 + (6 / 5) * price := by
  unfold lagrangian reward cost
  ring

theorem actual_dual_piecewise (price : ℝ) :
    (price ≤ 1 / 2 → dual price = 2 - (22 / 15) * price) ∧
      (price ∈ Icc (1 / 2) 1 → dual price = 4 / 3 - (2 / 15) * price) ∧
      (1 ≤ price → dual price = (6 / 5) * price) := by
  unfold dual
  constructor
  · intro h
    rw [max_eq_right (by linarith), max_eq_right (by linarith)]
    ring
  constructor
  · intro h
    rw [max_eq_right (by linarith [h.2]), max_eq_left (by linarith [h.1])]
    ring
  · intro h
    rw [max_eq_left (by linarith), max_eq_left (by linarith)]
    ring

theorem source_dual_unique_minimum (price : ℝ) :
    6 / 5 ≤ dual price ∧ (dual price = 6 / 5 ↔ price = 1) := by
  by_cases h : price ≤ 1 / 2
  · rw [(actual_dual_piecewise price).1 h]
    constructor
    · linarith
    · constructor <;> intro he <;> linarith
  · by_cases hh : price ≤ 1
    · rw [(actual_dual_piecewise price).2.1 ⟨le_of_not_ge h, hh⟩]
      constructor
      · linarith
      · constructor <;> intro he <;> linarith
    · rw [(actual_dual_piecewise price).2.2 (le_of_not_ge hh)]
      constructor
      · linarith
      · constructor <;> intro he <;> linarith

end SafeLearning.CompleteAlternatingCMDP
