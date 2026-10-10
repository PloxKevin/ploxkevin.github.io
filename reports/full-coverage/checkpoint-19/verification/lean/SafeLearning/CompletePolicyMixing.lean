import SafeLearning.CompleteCoreReturns

set_option autoImplicit false
noncomputable section
open Set
open scoped NNReal

namespace SafeLearning.CompletePolicyMixing

def reward (p : ℝ) : ℝ := 2 + 6 * p
def cost (p : ℝ) : ℝ := 4 * p
def lagrangian (p lambda : ℝ) : ℝ := reward p - lambda * (cost p - 1)
def dual (lambda : ℝ) : ℝ := max (2 + lambda) (8 - 3 * lambda)

theorem actual_discounted_returns (p : ℝ≥0) (hp : p ≤ 1) :
    CompleteCoreBook.modeReturn p hp (1 / 2) 1 4 = reward p ∧
      CompleteCoreBook.modeReturn p hp (1 / 2) 0 2 = cost p := by
  have h := CompleteCoreReturns.mixed_half_discount_returns p hp
  exact ⟨h.2.2, h.2.1⟩

theorem one_step_expectations (p : ℝ≥0) (hp : p ≤ 1) :
    CompleteCoreBook.expectedMode p hp 1 4 = 1 + 3 * (p : ℝ) ∧
      CompleteCoreBook.expectedMode p hp 0 2 = 2 * (p : ℝ) := by
  rw [CompleteCoreBook.mode_expectation, CompleteCoreBook.mode_expectation]
  constructor <;> ring

theorem feasible_range (p : ℝ) :
    (p ∈ Icc 0 1 ∧ cost p ≤ 1) ↔ p ∈ Icc 0 (1 / 4) := by
  unfold cost
  constructor
  · rintro ⟨hp, hc⟩
    exact ⟨hp.1, by linarith⟩
  · intro hp
    exact ⟨⟨hp.1, by linarith [hp.2]⟩, by linarith [hp.2]⟩

theorem reward_strictly_increasing : StrictMono reward := by
  intro x y h
  unfold reward
  linarith

theorem unique_feasible_optimum (p : ℝ) (hp : p ∈ Icc 0 1) (hc : cost p ≤ 1) :
    reward p ≤ 7 / 2 ∧ (reward p = 7 / 2 ↔ p = 1 / 4) := by
  have hf := (feasible_range p).mp ⟨hp, hc⟩
  unfold reward
  constructor
  · linarith [hf.2]
  · constructor <;> intro h <;> linarith

theorem optimum_and_endpoint_policies :
    cost (1 / 4) = 1 ∧ reward (1 / 4) = 7 / 2 ∧
      cost 0 ≤ 1 ∧ reward 0 = 2 ∧ 1 < cost 1 := by
  norm_num [cost, reward]

theorem primal_actual_supremum :
    sSup (reward '' {p : ℝ | p ∈ Icc 0 1 ∧ cost p ≤ 1}) = 7 / 2 := by
  have hmem : (7 / 2 : ℝ) ∈ reward '' {p : ℝ | p ∈ Icc 0 1 ∧ cost p ≤ 1} :=
    ⟨1 / 4, by norm_num [cost], by norm_num [reward]⟩
  have hbound : ∀ y ∈ reward '' {p : ℝ | p ∈ Icc 0 1 ∧ cost p ≤ 1}, y ≤ 7 / 2 := by
    rintro y ⟨p, hp, rfl⟩
    exact (unique_feasible_optimum p hp.1 hp.2).1
  exact le_antisymm (csSup_le ⟨_, hmem⟩ hbound) (le_csSup ⟨_, hbound⟩ hmem)

theorem lagrangian_affine (p lambda : ℝ) :
    lagrangian p lambda = 2 + lambda + (6 - 4 * lambda) * p := by
  unfold lagrangian reward cost
  ring

theorem actual_return_lagrangian (p : ℝ≥0) (hp : p ≤ 1) (lambda : ℝ) :
    CompleteCoreBook.modeReturn p hp (1 / 2) 1 4 -
      lambda * (CompleteCoreBook.modeReturn p hp (1 / 2) 0 2 - 1) =
        lagrangian p lambda := by
  rw [(actual_discounted_returns p hp).1, (actual_discounted_returns p hp).2]
  rfl

theorem lagrangian_le_dual (p lambda : ℝ) (hp : p ∈ Icc 0 1) :
    lagrangian p lambda ≤ dual lambda := by
  have h0 := le_max_left (2 + lambda) (8 - 3 * lambda)
  have h1 := le_max_right (2 + lambda) (8 - 3 * lambda)
  change 2 + lambda ≤ dual lambda at h0
  change 8 - 3 * lambda ≤ dual lambda at h1
  rw [lagrangian_affine]
  by_cases hs : 0 ≤ 6 - 4 * lambda
  · have hh := mul_le_mul_of_nonneg_left hp.2 hs
    nlinarith
  · have hh := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hs) hp.1
    nlinarith

theorem endpoint_attains_dual (lambda : ℝ) :
    ∃ p ∈ Icc (0 : ℝ) 1, lagrangian p lambda = dual lambda := by
  by_cases h : 2 + lambda ≤ 8 - 3 * lambda
  · refine ⟨1, by norm_num, ?_⟩
    rw [dual, max_eq_right h, lagrangian_affine]
    ring
  · refine ⟨0, by norm_num, ?_⟩
    rw [dual, max_eq_left (le_of_not_ge h), lagrangian_affine]
    ring

theorem dual_actual_supremum (lambda : ℝ) :
    sSup ((fun p => lagrangian p lambda) '' Icc 0 1) = dual lambda := by
  obtain ⟨p, hp, he⟩ := endpoint_attains_dual lambda
  have hmem : dual lambda ∈ (fun p => lagrangian p lambda) '' Icc 0 1 := ⟨p, hp, he⟩
  have hbound : ∀ y ∈ (fun p => lagrangian p lambda) '' Icc 0 1, y ≤ dual lambda := by
    rintro y ⟨q, hq, rfl⟩
    exact lagrangian_le_dual q lambda hq
  exact le_antisymm (csSup_le ⟨_, hmem⟩ hbound) (le_csSup ⟨_, hbound⟩ hmem)

theorem dual_piecewise (lambda : ℝ) :
    (lambda ≤ 3 / 2 → dual lambda = 8 - 3 * lambda) ∧
      (3 / 2 ≤ lambda → dual lambda = 2 + lambda) := by
  unfold dual
  constructor
  · intro h
    exact max_eq_right (by linarith)
  · intro h
    exact max_eq_left (by linarith)

theorem unique_dual_minimum (lambda : ℝ) :
    7 / 2 ≤ dual lambda ∧ (dual lambda = 7 / 2 ↔ lambda = 3 / 2) := by
  have h0 := le_max_left (2 + lambda) (8 - 3 * lambda)
  have h1 := le_max_right (2 + lambda) (8 - 3 * lambda)
  change 2 + lambda ≤ dual lambda at h0
  change 8 - 3 * lambda ≤ dual lambda at h1
  constructor
  · linarith
  · constructor
    · intro h
      linarith
    · rintro rfl
      norm_num [dual]

theorem flat_at_optimal_price (p : ℝ) : lagrangian p (3 / 2) = 7 / 2 := by
  rw [lagrangian_affine]
  ring

theorem every_policy_is_lagrangian_maximizer (p : ℝ) (hp : p ∈ Icc 0 1) :
    lagrangian p (3 / 2) = dual (3 / 2) ∧
      ∀ q ∈ Icc (0 : ℝ) 1, lagrangian q (3 / 2) ≤ lagrangian p (3 / 2) := by
  rw [flat_at_optimal_price]
  refine ⟨by norm_num [dual], ?_⟩
  intro q _
  rw [flat_at_optimal_price]

theorem arbitrary_maximizer_can_fail :
    lagrangian 1 (3 / 2) = dual (3 / 2) ∧ 1 < cost 1 ∧
      lagrangian 0 (3 / 2) = dual (3 / 2) ∧ cost 0 ≤ 1 ∧ reward 0 < 7 / 2 := by
  norm_num [lagrangian, reward, cost, dual]

theorem complementarity_recovers_primal (p : ℝ) :
    (3 / 2 : ℝ) * (cost p - 1) = 0 ↔ p = 1 / 4 := by
  unfold cost
  constructor <;> intro h <;> linarith

end SafeLearning.CompletePolicyMixing
