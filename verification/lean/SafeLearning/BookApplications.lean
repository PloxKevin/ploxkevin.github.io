import Mathlib

/-! Selected universal statements underlying the new book applications.

These are mathematical implications for the explicitly assumed models, not
claims about hardware, identified dynamics, or complete research theorems.
Source mapping and remaining scope are supplied to the integrating reviewer.
-/
set_option autoImplicit false
noncomputable section
open Set
open scoped NNReal

namespace SafeLearning.BookApplications

/- The tank project: volumes and commanded changes are in litres per sample. -/
theorem robust_tank_step (x y u w cap sensor inflow : ℝ)
    (hmeasurement : |x-y| ≤ sensor) (hdisturbance : |w| ≤ inflow)
    (hlower : sensor+inflow-y ≤ u)
    (hupper : u ≤ cap-sensor-inflow-y) :
    x+u+w ∈ Icc 0 cap := by
  rcases abs_le.mp hmeasurement with ⟨hm₀, hm₁⟩
  rcases abs_le.mp hdisturbance with ⟨hw₀, hw₁⟩
  constructor <;> linarith

theorem tank_original_step (x y u w : ℝ)
    (hmeasurement : |x-y| ≤ 1/10) (hdisturbance : |w| ≤ 1/5)
    (hinput : u ∈ Icc (3/10-y) (97/10-y)) :
    x+u+w ∈ Icc 0 10 := by
  exact robust_tank_step x y u w 10 (1/10) (1/5)
    hmeasurement hdisturbance (by linarith [hinput.1]) (by linarith [hinput.2])

theorem tank_filter_feasible (y : ℝ) (hy : y ∈ Icc (-1/10) (101/10)) :
    ∃ u : ℝ, u ∈ Icc (-1) 1 ∧ u ∈ Icc (3/10-y) (97/10-y) := by
  refine ⟨max (-1) (3/10-y), ?_, ?_⟩
  · constructor
    · exact le_max_left _ _
    · apply max_le <;> linarith [hy.1]
  · constructor
    · exact le_max_right _ _
    · apply max_le <;> linarith [hy.2]

theorem tank_measurement_feedback (y : ℝ) (hy : y ∈ Icc (-1/10) (101/10)) :
    ∃ u : ℝ, u ∈ Icc (-1) 1 ∧
      ∀ x w : ℝ, |x-y| ≤ 1/10 → |w| ≤ 1/5 → x+u+w ∈ Icc 0 10 := by
  rcases tank_filter_feasible y hy with ⟨u, hu, hs⟩
  exact ⟨u, hu, fun x w hm hw => tank_original_step x y u w hm hw hs⟩

theorem tank_sampled_invariance (x y u w : ℕ → ℝ)
    (hzero : x 0 ∈ Icc 0 10)
    (hmeasurement : ∀ n, |x n-y n| ≤ 1/10)
    (hdisturbance : ∀ n, |w n| ≤ 1/5)
    (hinput : ∀ n, u n ∈ Icc (3/10-y n) (97/10-y n))
    (hupdate : ∀ n, x (n+1) = x n+u n+w n) :
    ∀ n, x n ∈ Icc 0 10 := by
  intro n
  cases n with
  | zero => exact hzero
  | succ n =>
    rw [hupdate]
    exact tank_original_step (x n) (y n) (u n) (w n)
      (hmeasurement n) (hdisturbance n) (hinput n)

theorem tank_feedback_recursive_invariance (x y w : ℕ → ℝ) (policy : ℝ → ℝ)
    (hzero : x 0 ∈ Icc 0 10)
    (hmeasurement : ∀ n, |x n-y n| ≤ 1/10)
    (hdisturbance : ∀ n, |w n| ≤ 1/5)
    (hpolicy : ∀ measured ∈ Icc (-1/10 : ℝ) (101/10),
      policy measured ∈ Icc (-1 : ℝ) 1 ∧
      policy measured ∈ Icc (3/10-measured) (97/10-measured))
    (hupdate : ∀ n, x (n+1) = x n+policy (y n)+w n) :
    ∀ n, x n ∈ Icc 0 10 := by
  intro n
  induction n with
  | zero => exact hzero
  | succ n ih =>
    have hm := abs_le.mp (hmeasurement n)
    have hy : y n ∈ Icc (-1/10 : ℝ) (101/10) := by
      constructor <;> linarith [ih.1, ih.2, hm.1, hm.2]
    rw [hupdate]
    exact tank_original_step (x n) (y n) (policy (y n)) (w n)
      (hmeasurement n) (hdisturbance n) (hpolicy (y n) hy).2

theorem tank_no_shared_input :
    ¬ ∃ u : ℝ, ∀ x ∈ Icc (0 : ℝ) 10,
      ∀ w ∈ Icc (-1/5 : ℝ) (1/5), x+u+w ∈ Icc 0 10 := by
  rintro ⟨u, hu⟩
  have hlo := (hu 0 (by norm_num) (-1/5) (by norm_num)).1
  have hhi := (hu 10 (by norm_num) (1/5) (by norm_num)).2
  linarith

theorem tank_large_disturbance_impossible (u : ℝ) (hu : u ≤ 1) :
    ¬ (0+u-6/5 ∈ Icc (0 : ℝ) 10) := by
  intro h
  linarith [h.1]

/- Module 8: expected discounted one-state policy mixing, gamma = 9/10.
The reward/cost formulas are assumed summaries; no probability law is encoded.
-/
def mixReward (p : ℝ) : ℝ := 20+30*p
def mixCost (p : ℝ) : ℝ := 1/5+(9/5)*p

theorem policy_mix_feasible (p : ℝ) :
    (p ∈ Icc 0 1 ∧ mixCost p ≤ 1) ↔ p ∈ Icc 0 (4/9) := by
  unfold mixCost
  constructor
  · rintro ⟨⟨h₀,h₁⟩,hc⟩
    constructor <;> linarith
  · rintro ⟨h₀,h₁⟩
    constructor
    · constructor <;> linarith
    · linarith

theorem policy_mix_constrained_optimum (p : ℝ) (_hp : p ∈ Icc 0 1)
    (hc : mixCost p ≤ 1) : mixReward p ≤ 100/3 := by
  unfold mixCost at hc
  unfold mixReward
  linarith

theorem policy_mix_unique_optimum (p : ℝ) :
    mixReward p = 100/3 ↔ p = 4/9 := by
  unfold mixReward
  constructor <;> intro h <;> linarith

theorem policy_mix_optimum_attained :
    (4/9 : ℝ) ∈ Icc 0 1 ∧ mixCost (4/9) = 1 ∧ mixReward (4/9) = 100/3 := by
  norm_num [mixCost, mixReward]

theorem policy_mix_budget_optimum (budget : ℝ)
    (hb : budget ∈ Icc (1/5 : ℝ) 2) :
    (5*budget-1)/9 ∈ Icc (0 : ℝ) 1 ∧
      mixCost ((5*budget-1)/9) = budget ∧
      ∀ p : ℝ, mixCost p ≤ budget →
        mixReward p ≤ mixReward ((5*budget-1)/9) := by
  constructor
  · constructor <;> linarith [hb.1, hb.2]
  constructor
  · unfold mixCost
    ring
  · intro p hp
    unfold mixCost at hp
    unfold mixReward
    linarith

theorem policy_mix_flat_lagrangian (p : ℝ) :
    mixReward p-(50/3)*(mixCost p-1) = 100/3 := by
  unfold mixReward mixCost
  ring

/- Module 10: the all-times affine lower bound during one holding interval.
The integral/dynamics-to-lower-bound implication is an explicit assumption.
-/
theorem held_barrier_affine (initial slope horizon t : ℝ)
    (hinitial : 0 ≤ initial) (ht : t ∈ Icc 0 horizon)
    (hterminal : 0 ≤ initial+slope*horizon) :
    0 ≤ initial+slope*t := by
  by_cases hs : 0 ≤ slope
  · nlinarith [mul_nonneg hs ht.1]
  · have hp := mul_nonneg (by linarith [ht.2] : 0 ≤ horizon-t)
      (by linarith : 0 ≤ -slope)
    nlinarith

theorem held_barrier_clearance (clearance : ℝ → ℝ)
    (initial input disturbance horizon : ℝ) (hinitial : 0 ≤ initial)
    (hterminal : 0 ≤ initial+(input-disturbance)*horizon)
    (hlower : ∀ t ∈ Icc (0 : ℝ) horizon,
      initial+(input-disturbance)*t ≤ clearance t) :
    ∀ t ∈ Icc (0 : ℝ) horizon, 0 ≤ clearance t := by
  intro t ht
  exact (held_barrier_affine initial (input-disturbance) horizon t hinitial ht hterminal).trans
    (hlower t ht)

theorem held_barrier_half_second (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (1/2)) :
    0 ≤ 3/10+(-1/2-1/10)*t := by
  apply held_barrier_affine (3/10) (-1/2-1/10) (1/2) t (by norm_num) ht
  norm_num

theorem held_barrier_late_counterexample :
    (3/10 : ℝ)+(-1/2-1/10)*1 = -3/10 ∧ (-3/10 : ℝ) < 0 := by
  norm_num

/- Module 11: the real-valued scalar tube and its complete finite-time envelope. -/
theorem tube_invariant_step (x q error radius allowance : ℝ)
    (hq : 0 ≤ q) (hx : |x| ≤ radius) (he : |error| ≤ allowance)
    (hbudget : q*radius+allowance ≤ radius) :
    |q*x+error| ≤ radius := by
  calc |q*x+error| ≤ |q*x|+|error| := abs_add_le _ _
    _ = q*|x|+|error| := by rw [abs_mul, abs_of_nonneg hq]
    _ ≤ q*radius+allowance := by nlinarith [mul_le_mul_of_nonneg_left hx hq]
    _ ≤ radius := hbudget

theorem tube_sampled_invariance (x error : ℕ → ℝ) (q radius allowance : ℝ)
    (hq : 0 ≤ q) (hzero : |x 0| ≤ radius)
    (he : ∀ n, |error n| ≤ allowance)
    (hbudget : q*radius+allowance ≤ radius)
    (hupdate : ∀ n, x (n+1) = q*x n+error n) :
    ∀ n, |x n| ≤ radius := by
  intro n
  induction n with
  | zero => exact hzero
  | succ n ih =>
    rw [hupdate]
    exact tube_invariant_step (x n) q (error n) radius allowance hq ih (he n) hbudget

theorem tube_thermal_errors (w approximation : ℝ)
    (hw : |w| ≤ 1/20) (ha : |approximation| ≤ 1/50) :
    |w+approximation| ≤ 7/100 := by
  calc |w+approximation| ≤ |w|+|approximation| := abs_add_le _ _
    _ ≤ 7/100 := by linarith

theorem tube_thermal_radius (x error : ℝ)
    (hx : |x| ≤ 7/50) (he : |error| ≤ 7/100) :
    |(1/2)*x+error| ≤ 7/50 := by
  exact tube_invariant_step x (1/2) error (7/50) (7/100) (by norm_num) hx he (by norm_num)

theorem tube_error_envelope (x : ℕ → ℝ) (q allowance : ℝ)
    (hq₀ : 0 ≤ q) (hq₁ : q < 1)
    (hstep : ∀ n, |x (n+1)| ≤ q*|x n|+allowance) :
    ∀ n, |x n| ≤ allowance/(1-q)+q^n*(|x 0|-allowance/(1-q)) := by
  have hne : 1-q ≠ 0 := by linarith
  have hfixed : (1-q)*(allowance/(1-q)) = allowance := by
    field_simp
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hmul := mul_le_mul_of_nonneg_left ih hq₀
    have hs := hstep n
    rw [pow_succ]
    nlinarith

/- Modules 3--6 and the tuning project: metric-space confidence transfer.
The observation is bounded deterministically; Lipschitz regularity is assumed.
-/
theorem lipschitz_observation_transfer {X : Type*} [PseudoMetricSpace X]
    (f : X → ℝ) (L : ℝ≥0) (hf : LipschitzWith L f)
    (x z : X) (observation error radius : ℝ)
    (ho : |observation-f z| ≤ error) (hr : dist x z ≤ radius) :
    observation-error-L*radius ≤ f x := by
  have hd := hf.dist_le_mul x z
  rw [Real.dist_eq] at hd
  have hlo := (abs_le.mp hd).1
  have hobs := (abs_le.mp ho).2
  have hdist := mul_le_mul_of_nonneg_left hr L.coe_nonneg
  linarith

theorem lipschitz_ball_safety {X : Type*} [PseudoMetricSpace X]
    (f : X → ℝ) (L : ℝ≥0) (hf : LipschitzWith L f)
    (z : X) (observation error radius threshold : ℝ)
    (ho : |observation-f z| ≤ error)
    (hmargin : threshold ≤ observation-error-L*radius) :
    ∀ x ∈ Metric.closedBall z radius, threshold ≤ f x := by
  intro x hx
  exact hmargin.trans (lipschitz_observation_transfer f L hf x z observation error radius
    ho (Metric.mem_closedBall.mp hx))

theorem lipschitz_implemented_parameter {X : Type*} [PseudoMetricSpace X]
    (f : X → ℝ) (L : ℝ≥0) (hf : LipschitzWith L f)
    (actual command observed : X) (value error displacement realization threshold : ℝ)
    (ho : |value-f observed| ≤ error)
    (hcommand : dist command observed ≤ displacement)
    (hrealization : dist actual command ≤ realization)
    (hmargin : threshold ≤ value-error-L*(displacement+realization)) :
    threshold ≤ f actual := by
  have hd : dist actual observed ≤ displacement+realization := by
    calc dist actual observed ≤ dist actual command+dist command observed := dist_triangle _ _ _
      _ ≤ displacement+realization := by linarith
  exact hmargin.trans (lipschitz_observation_transfer f L hf actual observed value error
    (displacement+realization) ho hd)

end SafeLearning.BookApplications
