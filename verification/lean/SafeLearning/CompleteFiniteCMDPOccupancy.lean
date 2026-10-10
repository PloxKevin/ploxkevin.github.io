import Mathlib

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SafeLearning.CompleteFiniteCMDPOccupancy

variable {S A : Type*} [Fintype S] [Fintype A]

/-- A finite initial probability law and a finite controlled stochastic kernel. -/
structure Model (S A : Type*) [Fintype S] [Fintype A] where
  initial : S → ℝ
  transition : S → A → S → ℝ
  initial_nonneg : ∀ s, 0 ≤ initial s
  initial_sum : ∑ s, initial s = 1
  transition_nonneg : ∀ s a t, 0 ≤ transition s a t
  transition_sum : ∀ s a, ∑ t, transition s a t = 1

/-- An arbitrary time-dependent randomized Markov policy. -/
structure Policy (S A : Type*) [Fintype S] [Fintype A] where
  action : ℕ → S → A → ℝ
  action_nonneg : ∀ n s a, 0 ≤ action n s a
  action_sum : ∀ n s, ∑ a, action n s a = 1

variable (M : Model S A) (π : Policy S A)

def stateMass : ℕ → S → ℝ
  | 0 => M.initial
  | n + 1 => fun t => ∑ s, ∑ a,
      stateMass n s * π.action n s a * M.transition s a t

def jointMass (n : ℕ) (s : S) (a : A) : ℝ :=
  stateMass M π n s * π.action n s a

theorem actual_state_nonneg (n : ℕ) (s : S) : 0 ≤ stateMass M π n s := by
  induction n generalizing s with
  | zero => exact M.initial_nonneg s
  | succ n ih =>
    exact Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun a _ =>
      mul_nonneg (mul_nonneg (ih t) (π.action_nonneg n t a))
        (M.transition_nonneg t a s)

theorem actual_joint_nonneg (n : ℕ) (s : S) (a : A) :
    0 ≤ jointMass M π n s a :=
  mul_nonneg (actual_state_nonneg M π n s) (π.action_nonneg n s a)

theorem actual_joint_state_marginal (n : ℕ) (s : S) :
    ∑ a, jointMass M π n s a = stateMass M π n s := by
  simp [jointMass, ← Finset.mul_sum, π.action_sum]

theorem actual_state_total_mass (n : ℕ) : ∑ s, stateMass M π n s = 1 := by
  induction n with
  | zero => exact M.initial_sum
  | succ n ih =>
    simp only [stateMass]
    have rearrange : (∑ t, ∑ s, ∑ a,
        stateMass M π n s * π.action n s a * M.transition s a t) =
        ∑ s, ∑ a, ∑ t,
        stateMass M π n s * π.action n s a * M.transition s a t := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s hs
      exact Finset.sum_comm
    rw [rearrange]
    simp_rw [← Finset.mul_sum, M.transition_sum, mul_one,
      ← Finset.mul_sum, π.action_sum, mul_one]
    exact ih

theorem actual_joint_total_mass (n : ℕ) :
    ∑ s, ∑ a, jointMass M π n s a = 1 := by
  simp_rw [actual_joint_state_marginal]
  exact actual_state_total_mass M π n

theorem actual_state_mass_le_one (n : ℕ) (s : S) : stateMass M π n s ≤ 1 := by
  rw [← actual_state_total_mass M π n]
  exact Finset.single_le_sum (fun t _ => actual_state_nonneg M π n t)
    (Finset.mem_univ s)

theorem actual_joint_mass_le_one (n : ℕ) (s : S) (a : A) :
    jointMass M π n s a ≤ 1 := by
  have h := Finset.single_le_sum (s := Finset.univ)
    (fun b _ => actual_joint_nonneg M π n s b) (Finset.mem_univ a)
  rw [actual_joint_state_marginal] at h
  exact h.trans (actual_state_mass_le_one M π n s)

def occupancy (γ : ℝ) (s : S) (a : A) : ℝ :=
  (1 - γ) * ∑' n : ℕ, γ ^ n * jointMass M π n s a

theorem actual_joint_discounted_series_summable (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) (a : A) :
    Summable (fun n : ℕ => γ ^ n * jointMass M π n s a) := by
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (pow_nonneg hγ0 n) (actual_joint_nonneg M π n s a))
    (fun n => ?_) (summable_geometric_of_lt_one hγ0 hγ1)
  exact mul_le_of_le_one_right (pow_nonneg hγ0 n) (actual_joint_mass_le_one M π n s a)

theorem actual_occupancy_nonneg (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (s : S) (a : A) : 0 ≤ occupancy M π γ s a := by
  exact mul_nonneg (sub_nonneg.mpr hγ1.le)
    (tsum_nonneg fun n => mul_nonneg (pow_nonneg hγ0 n) (actual_joint_nonneg M π n s a))

theorem finite_double_sum_tsum (f : S → A → ℕ → ℝ)
    (hf : ∀ s a, Summable (f s a)) :
    (∑ s, ∑ a, ∑' n, f s a n) = ∑' n, ∑ s, ∑ a, f s a n := by
  symm
  rw [Summable.tsum_finsetSum (fun s _ => summable_sum (fun a _ => hf s a))]
  apply Finset.sum_congr rfl
  intro s hs
  exact Summable.tsum_finsetSum (fun a _ => hf s a)

theorem actual_discounted_reward_series_summable (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (r : S → A → ℝ) :
    Summable (fun n : ℕ => γ ^ n * ∑ s, ∑ a, jointMass M π n s a * r s a) := by
  have h := summable_sum (fun s (_ : s ∈ Finset.univ) =>
    summable_sum (fun a (_ : a ∈ Finset.univ) =>
      (actual_joint_discounted_series_summable M π γ hγ0 hγ1 s a).mul_right (r s a)))
  simpa only [Finset.mul_sum, mul_assoc] using h

theorem actual_occupancy_linear_functional (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (r : S → A → ℝ) :
    (∑ s, ∑ a, occupancy M π γ s a * r s a) =
      (1 - γ) * ∑' n : ℕ, γ ^ n * ∑ s, ∑ a, jointMass M π n s a * r s a := by
  simp only [occupancy, mul_assoc, ← tsum_mul_right, ← Finset.mul_sum]
  congr 1
  rw [finite_double_sum_tsum (fun s a n => γ ^ n * (jointMass M π n s a * r s a))
    (fun s a => by simpa only [mul_assoc] using
      (actual_joint_discounted_series_summable M π γ hγ0 hγ1 s a).mul_right (r s a))]
  apply tsum_congr
  intro n
  simp only [Finset.mul_sum, mul_assoc]

theorem actual_occupancy_total_mass (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    ∑ s, ∑ a, occupancy M π γ s a = 1 := by
  have h := actual_occupancy_linear_functional M π γ hγ0 hγ1 (fun _ _ => 1)
  simp only [mul_one, actual_joint_total_mass] at h
  rw [h, tsum_geometric_of_lt_one hγ0 hγ1]
  exact mul_inv_cancel₀ (ne_of_gt (sub_pos.mpr hγ1))

/-- The actual discounted sum of expected stage rewards under the finite law. -/
def expectedReturn (γ : ℝ) (r : S → A → ℝ) : ℝ :=
  ∑' n : ℕ, γ ^ n * ∑ s, ∑ a, jointMass M π n s a * r s a

theorem actual_reward_return_identity (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (r : S → A → ℝ) :
    expectedReturn M π γ r = (∑ s, ∑ a, occupancy M π γ s a * r s a) / (1 - γ) := by
  rw [actual_occupancy_linear_functional M π γ hγ0 hγ1 r]
  exact (mul_div_cancel_left₀ _ (ne_of_gt (sub_pos.mpr hγ1))).symm

theorem actual_state_discounted_series_summable (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) :
    Summable (fun n : ℕ => γ ^ n * stateMass M π n s) := by
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (pow_nonneg hγ0 n) (actual_state_nonneg M π n s))
    (fun n => ?_) (summable_geometric_of_lt_one hγ0 hγ1)
  exact mul_le_of_le_one_right (pow_nonneg hγ0 n) (actual_state_mass_le_one M π n s)

theorem actual_occupancy_state_marginal (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) :
    (∑ a, occupancy M π γ s a) = (1 - γ) * ∑' n : ℕ, γ ^ n * stateMass M π n s := by
  simp only [occupancy, ← Finset.mul_sum]
  congr 1
  rw [← Summable.tsum_finsetSum
    (fun a (_ : a ∈ Finset.univ) => actual_joint_discounted_series_summable M π γ hγ0 hγ1 s a)]
  apply tsum_congr
  intro n
  rw [← Finset.mul_sum, actual_joint_state_marginal]

theorem actual_joint_transition_law (n : ℕ) (t : S) :
    (∑ s, ∑ a, jointMass M π n s a * M.transition s a t) =
      stateMass M π (n + 1) t := rfl

theorem actual_discounted_bellman_flow (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (t : S) :
    (∑ a, occupancy M π γ t a) = (1 - γ) * M.initial t +
      γ * ∑ s, ∑ a, occupancy M π γ s a * M.transition s a t := by
  have htail : Summable (fun n : ℕ => γ ^ (n + 1) * stateMass M π (n + 1) t) :=
    (summable_nat_add_iff (f := fun n : ℕ => γ ^ n * stateMass M π n t) 1).mpr
      (actual_state_discounted_series_summable M π γ hγ0 hγ1 t)
  have hsplit := tsum_eq_zero_add'
    (f := fun n : ℕ => γ ^ n * stateMass M π n t) htail
  have htrans := actual_occupancy_linear_functional M π γ hγ0 hγ1
    (fun s a => M.transition s a t)
  change (∑ s, ∑ a, occupancy M π γ s a * M.transition s a t) =
    (1 - γ) * ∑' n : ℕ, γ ^ n * stateMass M π (n + 1) t at htrans
  have htail_eq : (∑' n : ℕ, γ ^ (n + 1) * stateMass M π (n + 1) t) =
      γ * ∑' n : ℕ, γ ^ n * stateMass M π (n + 1) t := by
    calc
      _ = ∑' n : ℕ, γ * (γ ^ n * stateMass M π (n + 1) t) := by
        apply tsum_congr
        intro n
        rw [pow_succ]
        ring
      _ = _ := tsum_mul_left
  have hsplit' : (∑' n : ℕ, γ ^ n * stateMass M π n t) =
      M.initial t + γ * ∑' n : ℕ, γ ^ n * stateMass M π (n + 1) t := by
    calc
      _ = (γ ^ 0 * stateMass M π 0 t) +
          ∑' n : ℕ, γ ^ (n + 1) * stateMass M π (n + 1) t := hsplit
      _ = _ := by
        have hz : γ ^ 0 * stateMass M π 0 t = M.initial t := by
          simp only [pow_zero, one_mul, stateMass]
        rw [htail_eq, hz]
  calc
    _ = (1 - γ) * ∑' n : ℕ, γ ^ n * stateMass M π n t :=
      actual_occupancy_state_marginal M π γ hγ0 hγ1 t
    _ = (1 - γ) * (M.initial t +
        γ * ∑' n : ℕ, γ ^ n * stateMass M π (n + 1) t) := congrArg ((1 - γ) * ·) hsplit'
    _ = (1 - γ) * M.initial t +
        γ * ((1 - γ) * ∑' n : ℕ, γ ^ n * stateMass M π (n + 1) t) := by ring
    _ = _ := congrArg (fun x => (1 - γ) * M.initial t + γ * x) htrans.symm

end SafeLearning.CompleteFiniteCMDPOccupancy
