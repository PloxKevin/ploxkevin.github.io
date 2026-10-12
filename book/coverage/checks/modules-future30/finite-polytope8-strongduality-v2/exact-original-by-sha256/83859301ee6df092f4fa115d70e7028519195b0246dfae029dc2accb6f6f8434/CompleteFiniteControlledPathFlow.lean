import SafeLearning.CompleteFiniteTrajectoryReturns
import SafeLearning.CompleteFiniteCMDPRecovery

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MeasureTheory

namespace SafeLearning.CompleteFiniteControlledPathFlow

open SafeLearning.CompleteFiniteTrajectoryReturns
open SafeLearning.CompleteFiniteCMDPOccupancy
open SafeLearning.CompleteFiniteCMDPFlow

variable {S A Ω : Type*} [Fintype S] [Fintype A] [MeasurableSpace Ω]

/-- Actual one-step controlled transition laws on a probability space. The action
process is arbitrary; it may depend on the entire past. -/
structure ControlledLaw (M : Model S A) (μ : Measure Ω)
    (X : ℕ → Ω → S) (U : ℕ → Ω → A) : Prop where
  state_measurable : ∀ n s, MeasurableSet {ω | X n ω = s}
  joint_measurable : ∀ n s a, MeasurableSet {ω | X n ω = s ∧ U n ω = a}
  initial : ∀ s, μ.real {ω | X 0 ω = s} = M.initial s
  transition_joint : ∀ n s a t,
    μ.real {ω | X n ω = s ∧ U n ω = a ∧ X (n + 1) ω = t} =
      μ.real {ω | X n ω = s ∧ U n ω = a} * M.transition s a t

variable (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem actual_finite_event_partition {F : Type*} [Fintype F]
    (Z : Ω → F) (E : Set Ω)
    (hm : ∀ z, MeasurableSet {ω | Z ω = z ∧ ω ∈ E}) :
    μ.real E = ∑ z, μ.real {ω | Z ω = z ∧ ω ∈ E} := by
  have hd : Pairwise (fun z w => Disjoint {ω | Z ω = z ∧ ω ∈ E}
      {ω | Z ω = w ∧ ω ∈ E}) := by
    intro z w hzw
    apply Set.disjoint_left.mpr
    intro ω hz hw
    exact hzw (hz.1.symm.trans hw.1)
  have he : (⋃ z, {ω | Z ω = z ∧ ω ∈ E}) = E := by
    ext ω
    simp
  calc
    μ.real E = μ.real (⋃ z, {ω | Z ω = z ∧ ω ∈ E}) := congrArg μ.real he.symm
    _ = _ := measureReal_iUnion_fintype (μ := μ) hd hm

variable (M : Model S A) (X : ℕ → Ω → S) (U : ℕ → Ω → A)
variable (h : ControlledLaw M μ X U)

def stateProbability (n : ℕ) (s : S) : ℝ := μ.real {ω | X n ω = s}
def jointProbability (n : ℕ) (s : S) (a : A) : ℝ :=
  μ.real {ω | X n ω = s ∧ U n ω = a}

include h in
theorem actual_joint_state_marginal (n : ℕ) (s : S) :
    ∑ a, jointProbability μ X U n s a = stateProbability μ X n s := by
  have hp := actual_finite_event_partition μ (U n) {ω | X n ω = s}
    (fun a => by simpa only [Set.mem_ofPred_eq, and_comm] using h.joint_measurable n s a)
  simpa only [stateProbability, jointProbability, Set.mem_ofPred_eq, and_comm] using hp.symm

include h in
theorem actual_history_independent_transition_identity (n : ℕ) (t : S) :
    stateProbability μ X (n + 1) t =
      ∑ s, ∑ a, jointProbability μ X U n s a * M.transition s a t := by
  have hm : ∀ z : S × A,
      MeasurableSet {ω | (X n ω, U n ω) = z ∧ X (n + 1) ω = t} := by
    intro z
    rcases z with ⟨s, a⟩
    simpa only [Set.inter_def, Set.mem_ofPred_eq, Prod.mk.injEq, and_assoc] using
      (h.joint_measurable n s a).inter (h.state_measurable (n + 1) t)
  have hp := actual_finite_event_partition μ
    (fun ω => (X n ω, U n ω)) {ω | X (n + 1) ω = t} hm
  rw [Fintype.sum_prod_type] at hp
  simpa only [stateProbability, Prod.mk.injEq, and_assoc, Set.mem_ofPred_eq,
    h.transition_joint, jointProbability] using hp

def controlledOccupancy (γ : ℝ) (s : S) (a : A) : ℝ :=
  (1 - γ) * ∑' n : ℕ, γ ^ n * jointProbability μ X U n s a

theorem actual_joint_discounted_series_summable
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) (a : A) :
    Summable (fun n : ℕ => γ ^ n * jointProbability μ X U n s a) := by
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (pow_nonneg hγ0 n) measureReal_nonneg)
    (fun n => ?_) (summable_geometric_of_lt_one hγ0 hγ1)
  exact mul_le_of_le_one_right (pow_nonneg hγ0 n) measureReal_le_one

theorem actual_state_discounted_series_summable
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) :
    Summable (fun n : ℕ => γ ^ n * stateProbability μ X n s) := by
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (pow_nonneg hγ0 n) measureReal_nonneg)
    (fun n => ?_) (summable_geometric_of_lt_one hγ0 hγ1)
  exact mul_le_of_le_one_right (pow_nonneg hγ0 n) measureReal_le_one

theorem actual_controlled_occupancy_linear_functional
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (r : S → A → ℝ) :
    (∑ s, ∑ a, controlledOccupancy μ X U γ s a * r s a) =
      (1 - γ) * ∑' n : ℕ, γ ^ n * ∑ s, ∑ a, jointProbability μ X U n s a * r s a := by
  simp only [controlledOccupancy, mul_assoc, ← Finset.mul_sum]
  congr 1
  simp_rw [← tsum_mul_right]
  simp only [mul_assoc]
  rw [finite_double_sum_tsum (fun s a n => γ ^ n * (jointProbability μ X U n s a * r s a))
    (fun s a => by simpa only [mul_assoc] using
      (actual_joint_discounted_series_summable μ X U γ hγ0 hγ1 s a).mul_right (r s a))]
  apply tsum_congr
  intro n
  simp only [Finset.mul_sum, mul_assoc]

include h in
theorem actual_controlled_occupancy_state_marginal
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) :
    (∑ a, controlledOccupancy μ X U γ s a) =
      (1 - γ) * ∑' n : ℕ, γ ^ n * stateProbability μ X n s := by
  simp only [controlledOccupancy, ← Finset.mul_sum]
  congr 1
  rw [← Summable.tsum_finsetSum (fun a (_ : a ∈ Finset.univ) =>
    actual_joint_discounted_series_summable μ X U γ hγ0 hγ1 s a)]
  apply tsum_congr
  intro n
  rw [← Finset.mul_sum, actual_joint_state_marginal μ M X U h]

include h in
theorem actual_every_controlled_history_law_satisfies_bellman_flow
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    FlowFeasible M γ (controlledOccupancy μ X U γ) := by
  constructor
  · intro s a
    exact mul_nonneg (sub_nonneg.mpr hγ1.le)
      (tsum_nonneg fun n => mul_nonneg (pow_nonneg hγ0 n) measureReal_nonneg)
  · intro t
    have htail : Summable (fun n : ℕ => γ ^ (n + 1) * stateProbability μ X (n + 1) t) :=
      (summable_nat_add_iff (f := fun n : ℕ => γ ^ n * stateProbability μ X n t) 1).mpr
        (actual_state_discounted_series_summable μ X γ hγ0 hγ1 t)
    have hsplit := tsum_eq_zero_add'
      (f := fun n : ℕ => γ ^ n * stateProbability μ X n t) htail
    have htrans := actual_controlled_occupancy_linear_functional μ X U γ hγ0 hγ1
      (fun s a => M.transition s a t)
    simp_rw [← actual_history_independent_transition_identity μ M X U h] at htrans
    have htail_eq : (∑' n : ℕ, γ ^ (n + 1) * stateProbability μ X (n + 1) t) =
        γ * ∑' n : ℕ, γ ^ n * stateProbability μ X (n + 1) t := by
      calc
        _ = ∑' n : ℕ, γ * (γ ^ n * stateProbability μ X (n + 1) t) := by
          apply tsum_congr
          intro n
          rw [pow_succ]
          ring
        _ = _ := tsum_mul_left
    have hz : γ ^ 0 * stateProbability μ X 0 t = M.initial t := by
      simpa only [pow_zero, one_mul, stateProbability] using h.initial t
    rw [htail_eq, hz] at hsplit
    change (∑ a, controlledOccupancy μ X U γ t a) = _
    rw [actual_controlled_occupancy_state_marginal μ M X U h γ hγ0 hγ1 t,
      hsplit, htrans]
    ring

theorem actual_controlled_occupancy_is_the_path_event_occupancy
    (γ : ℝ) (s : S) (a : A) :
    controlledOccupancy μ X U γ s a =
      pathOccupancy μ (fun n ω => (X n ω, U n ω)) γ (s, a) := by
  simp only [controlledOccupancy, pathOccupancy, atomMass, jointProbability, Prod.mk.injEq]

include h in
theorem actual_every_controlled_history_law_return_formula
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (r : S → A → ℝ) :
    (∫ ω, ∑' n : ℕ, γ ^ n * r (X n ω) (U n ω) ∂μ) =
      (∑ s, ∑ a, controlledOccupancy μ X U γ s a * r s a) / (1 - γ) := by
  have hm : ∀ (n : ℕ) (z : S × A), MeasurableSet {ω | (X n ω, U n ω) = z} := by
    intro n z
    rcases z with ⟨s, a⟩
    simpa only [Prod.mk.injEq] using h.joint_measurable n s a
  have hr := actual_path_return_linear_functional μ
    (fun n ω => (X n ω, U n ω)) hm γ hγ0 hγ1 (fun z => r z.1 z.2)
  simpa only [pathReturn, Fintype.sum_prod_type,
    ← actual_controlled_occupancy_is_the_path_event_occupancy] using hr

include h in
theorem actual_history_path_occupancy_is_realized_by_a_stationary_policy
    (a₀ : A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    ∃ π : Policy S A, (∀ n s a, π.action n s a = π.action 0 s a) ∧
      occupancy M π γ = controlledOccupancy μ X U γ := by
  have hf := actual_every_controlled_history_law_satisfies_bellman_flow μ M X U h γ hγ0 hγ1
  refine ⟨SafeLearning.CompleteFiniteCMDPRecovery.recoveredPolicy a₀
    (controlledOccupancy μ X U γ) hf.1, fun _ _ _ => rfl, ?_⟩
  exact SafeLearning.CompleteFiniteCMDPRecovery.actual_every_feasible_flow_is_realized_by_recovered_stationary_policy
    M a₀ γ hγ0 hγ1 (controlledOccupancy μ X U γ) hf

end SafeLearning.CompleteFiniteControlledPathFlow
