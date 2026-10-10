import SafeLearning.CompleteFiniteCMDPFlow

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SafeLearning.CompleteFiniteCMDPRecovery

open SafeLearning.CompleteFiniteCMDPOccupancy SafeLearning.CompleteFiniteCMDPFlow

variable {S A : Type*} [Fintype S] [Fintype A]

theorem actual_stochastic_discounted_fixed_point_unique
    (K : S → S → ℝ) (hK0 : ∀ s t, 0 ≤ K s t) (hK1 : ∀ s, ∑ t, K s t = 1)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (μ x y : S → ℝ)
    (hx : ∀ t, x t = (1 - γ) * μ t + γ * ∑ s, x s * K s t)
    (hy : ∀ t, y t = (1 - γ) * μ t + γ * ∑ s, y s * K s t) : x = y := by
  have hdiff (t : S) : x t - y t = γ * ∑ s, (x s - y s) * K s t := by
    rw [hx t, hy t]
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  have hlocal (t : S) : |x t - y t| ≤ γ * ∑ s, |x s - y s| * K s t := by
    calc
      _ = |γ * ∑ s, (x s - y s) * K s t| := congrArg abs (hdiff t)
      _ = γ * |∑ s, (x s - y s) * K s t| := by rw [abs_mul, abs_of_nonneg hγ0]
      _ ≤ γ * ∑ s, |(x s - y s) * K s t| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hγ0
      _ = _ := by simp only [abs_mul, abs_of_nonneg (hK0 _ _)]
  have rearrange : (∑ t, ∑ s, |x s - y s| * K s t) = ∑ s, |x s - y s| := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hK1, mul_one]
  have htotal := Finset.sum_le_sum (fun t (_ : t ∈ Finset.univ) => hlocal t)
  rw [← Finset.mul_sum, rearrange] at htotal
  have hnonneg : 0 ≤ ∑ s, |x s - y s| := Finset.sum_nonneg (fun s _ => abs_nonneg _)
  have hzero : (∑ s, |x s - y s|) = 0 := by nlinarith
  funext t
  have hcoord := Finset.single_le_sum (s := Finset.univ)
    (fun s _ => abs_nonneg (x s - y s)) (Finset.mem_univ t)
  rw [hzero] at hcoord
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hcoord (abs_nonneg _)))

def recoveredAction (a₀ : A) (ρ : S → A → ℝ) (s : S) (a : A) : ℝ := by
  classical
  exact if 0 < stateMarginal ρ s then ρ s a / stateMarginal ρ s else if a = a₀ then 1 else 0

theorem actual_nonnegative_row_marginal (ρ : S → A → ℝ)
    (hρ : ∀ s a, 0 ≤ ρ s a) (s : S) : 0 ≤ stateMarginal ρ s :=
  Finset.sum_nonneg (fun a _ => hρ s a)

theorem actual_zero_nonnegative_row_has_zero_coordinates (ρ : S → A → ℝ)
    (hρ : ∀ s a, 0 ≤ ρ s a) (s : S) (hs : stateMarginal ρ s = 0) (a : A) : ρ s a = 0 := by
  have h := Finset.single_le_sum (s := Finset.univ) (fun b _ => hρ s b) (Finset.mem_univ a)
  change ρ s a ≤ stateMarginal ρ s at h
  rw [hs] at h
  exact le_antisymm h (hρ s a)

theorem actual_recovered_action_nonneg (a₀ : A) (ρ : S → A → ℝ)
    (hρ : ∀ s a, 0 ≤ ρ s a) (s : S) (a : A) : 0 ≤ recoveredAction a₀ ρ s a := by
  unfold recoveredAction
  split_ifs with hs ha
  · exact div_nonneg (hρ s a) hs.le
  · exact zero_le_one
  · exact le_refl 0

theorem actual_recovered_action_normalized (a₀ : A) (ρ : S → A → ℝ)
    (hρ : ∀ s a, 0 ≤ ρ s a) (s : S) : ∑ a, recoveredAction a₀ ρ s a = 1 := by
  classical
  by_cases hs : 0 < stateMarginal ρ s
  · simp only [recoveredAction, if_pos hs, ← Finset.sum_div]
    exact div_self (ne_of_gt hs)
  · simp [recoveredAction, hs]

theorem actual_recovered_row_action_product (a₀ : A) (ρ : S → A → ℝ)
    (hρ : ∀ s a, 0 ≤ ρ s a) (s : S) (a : A) :
    stateMarginal ρ s * recoveredAction a₀ ρ s a = ρ s a := by
  by_cases hs : 0 < stateMarginal ρ s
  · simp only [recoveredAction, if_pos hs]
    exact mul_div_cancel₀ _ (ne_of_gt hs)
  · have hz : stateMarginal ρ s = 0 :=
      le_antisymm (le_of_not_gt hs) (actual_nonnegative_row_marginal ρ hρ s)
    rw [hz, zero_mul, actual_zero_nonnegative_row_has_zero_coordinates ρ hρ s hz a]

def recoveredPolicy (a₀ : A) (ρ : S → A → ℝ) (hρ : ∀ s a, 0 ≤ ρ s a) : Policy S A where
  action _ := recoveredAction a₀ ρ
  action_nonneg _ := actual_recovered_action_nonneg a₀ ρ hρ
  action_sum _ := actual_recovered_action_normalized a₀ ρ hρ

def stationaryKernel (M : Model S A) (w : S → A → ℝ) (s t : S) : ℝ :=
  ∑ a, w s a * M.transition s a t

theorem actual_stationary_occupancy_factorization (M : Model S A) (π : Policy S A)
    (hw : ∀ n s a, π.action n s a = π.action 0 s a)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) (a : A) :
    occupancy M π γ s a = stateMarginal (occupancy M π γ) s * π.action 0 s a := by
  rw [stateMarginal, actual_occupancy_state_marginal M π γ hγ0 hγ1 s]
  simp only [occupancy, jointMass, hw, ← mul_assoc, tsum_mul_right]

theorem actual_stationary_kernel_probability_law (M : Model S A) (w : S → A → ℝ)
    (hw0 : ∀ s a, 0 ≤ w s a) (hw1 : ∀ s, ∑ a, w s a = 1) :
    (∀ s t, 0 ≤ stationaryKernel M w s t) ∧
      ∀ s, ∑ t, stationaryKernel M w s t = 1 := by
  constructor
  · intro s t
    exact Finset.sum_nonneg (fun a _ => mul_nonneg (hw0 s a) (M.transition_nonneg s a t))
  · intro s
    simp only [stationaryKernel]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, M.transition_sum, mul_one]
    exact hw1 s

theorem actual_flow_factorization_gives_kernel_fixed_point
    (M : Model S A) (γ : ℝ) (ρ w : S → A → ℝ) (hρ : FlowFeasible M γ ρ)
    (hprod : ∀ s a, stateMarginal ρ s * w s a = ρ s a) :
    ∀ t, stateMarginal ρ t = (1 - γ) * M.initial t +
      γ * ∑ s, stateMarginal ρ s * stationaryKernel M w s t := by
  intro t
  have he : (∑ s, ∑ a, ρ s a * M.transition s a t) =
      ∑ s, stateMarginal ρ s * stationaryKernel M w s t := by
    apply Finset.sum_congr rfl
    intro s hs
    simp only [stationaryKernel, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [← mul_assoc, hprod s a]
  exact (hρ.2 t).trans (congrArg (fun x => (1 - γ) * M.initial t + γ * x) he)

/-- Every nonnegative finite-model Bellman flow is the actual occupancy of its recovered policy. -/
theorem actual_every_feasible_flow_is_realized_by_recovered_stationary_policy
    (M : Model S A) (a₀ : A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (ρ : S → A → ℝ) (hρ : FlowFeasible M γ ρ) :
    occupancy M (recoveredPolicy a₀ ρ hρ.1) γ = ρ := by
  let π := recoveredPolicy a₀ ρ hρ.1
  let w := recoveredAction a₀ ρ
  have hstationary : ∀ n s a, π.action n s a = π.action 0 s a := fun _ _ _ => rfl
  have hprod₁ : ∀ s a, stateMarginal ρ s * w s a = ρ s a :=
    actual_recovered_row_action_product a₀ ρ hρ.1
  have hprod₂ : ∀ s a,
      stateMarginal (occupancy M π γ) s * w s a = occupancy M π γ s a := by
    intro s a
    exact (actual_stationary_occupancy_factorization M π hstationary γ hγ0 hγ1 s a).symm
  have hK := actual_stationary_kernel_probability_law M w
    (actual_recovered_action_nonneg a₀ ρ hρ.1) (actual_recovered_action_normalized a₀ ρ hρ.1)
  have hmarg : stateMarginal (occupancy M π γ) = stateMarginal ρ :=
    actual_stochastic_discounted_fixed_point_unique (stationaryKernel M w) hK.1 hK.2
      γ hγ0 hγ1 M.initial (stateMarginal (occupancy M π γ)) (stateMarginal ρ)
      (actual_flow_factorization_gives_kernel_fixed_point M γ (occupancy M π γ) w
        (actual_occupancy_satisfies_flow M π γ hγ0 hγ1) hprod₂)
      (actual_flow_factorization_gives_kernel_fixed_point M γ ρ w hρ hprod₁)
  funext s a
  calc
    _ = stateMarginal (occupancy M π γ) s * w s a := (hprod₂ s a).symm
    _ = stateMarginal ρ s * w s a := congrArg (fun x : S → ℝ => x s * w s a) hmarg
    _ = ρ s a := hprod₁ s a

end SafeLearning.CompleteFiniteCMDPRecovery
