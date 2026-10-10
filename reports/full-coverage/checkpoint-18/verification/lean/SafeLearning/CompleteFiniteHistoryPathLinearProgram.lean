import SafeLearning.CompleteFiniteMarkovPathCorrespondence
import SafeLearning.CompleteFiniteCMDPLinearProgram

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace SafeLearning.CompleteFiniteHistoryPathLinearProgram

open SafeLearning.CompleteFiniteCMDPOccupancy
open SafeLearning.CompleteFiniteCMDPFlow
open SafeLearning.CompleteFiniteCMDPLinearProgram
open SafeLearning.CompleteFiniteControlledPathMeasure
open SafeLearning.CompleteFiniteControlledPathMeasureLaws
open SafeLearning.CompleteFiniteMarkovPathCorrespondence

variable {S A I : Type*} [Fintype S] [Fintype A] [Fintype I]
variable [MeasurableSpace S] [MeasurableSpace A]
variable [MeasurableSingletonClass S] [MeasurableSingletonClass A]

def pathOccupancy (M : Model S A) (γ : ℝ) (π : HistoryPolicy S A) : S → A → ℝ :=
  SafeLearning.CompleteFiniteControlledPathFlow.controlledOccupancy
    (controlledPathMeasure M π) (fun n path => (path n).1) (fun n path => (path n).2) γ

/-- The actual Bochner expectation of the discounted reward on the constructed path. -/
def pathReturn (M : Model S A) (γ : ℝ) (π : HistoryPolicy S A) (r : S → A → ℝ) : ℝ :=
  ∫ path, ∑' n : ℕ, γ ^ n * r (path n).1 (path n).2 ∂controlledPathMeasure M π

theorem actual_history_path_occupancy_total_mass (M : Model S A) (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (π : HistoryPolicy S A) :
    ∑ s, ∑ a, pathOccupancy M γ π s a = 1 :=
  actual_all_feasible_flows_have_total_mass_one M γ hγ1 _
    (actual_all_history_policies_have_flow_feasible_path_occupancy M π γ hγ0 hγ1)

theorem actual_history_path_return_linear_formula (M : Model S A) (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (π : HistoryPolicy S A) (r : S → A → ℝ) :
    pathReturn M γ π r = rewardFunctional r (pathOccupancy M γ π) / (1 - γ) :=
  actual_all_history_policies_have_the_true_path_return_formula M π γ hγ0 hγ1 r

theorem actual_all_history_path_occupancies_equal_the_flow_polytope
    (M : Model S A) (a₀ : A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    Set.range (pathOccupancy M γ) = {ρ | FlowFeasible M γ ρ} := by
  ext ρ
  constructor
  · rintro ⟨π, rfl⟩
    exact actual_all_history_policies_have_flow_feasible_path_occupancy M π γ hγ0 hγ1
  · intro hρ
    obtain ⟨π, _, hπ⟩ :=
      actual_every_feasible_flow_has_a_constructed_stationary_path M a₀ γ hγ0 hγ1 ρ hρ
    exact ⟨π, hπ⟩

theorem actual_history_path_cost_feasible_iff (M : Model S A) (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (π : HistoryPolicy S A)
    (cost : I → S → A → ℝ) (budget : I → ℝ) :
    (∀ i, pathReturn M γ π (cost i) ≤ budget i) ↔
      CostFeasible M γ cost budget (pathOccupancy M γ π) := by
  have hp : 0 < 1 - γ := sub_pos.mpr hγ1
  constructor
  · intro h
    refine ⟨actual_all_history_policies_have_flow_feasible_path_occupancy M π γ hγ0 hγ1, ?_⟩
    intro i
    have hi := h i
    rw [actual_history_path_return_linear_formula M γ hγ0 hγ1] at hi
    simpa only [mul_comm] using (div_le_iff₀ hp).mp hi
  · intro h i
    rw [actual_history_path_return_linear_formula M γ hγ0 hγ1]
    apply (div_le_iff₀ hp).mpr
    simpa only [mul_comm] using h.2 i

theorem actual_history_path_constrained_rewards_equal_the_linear_program
    (M : Model S A) (a₀ : A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (reward : S → A → ℝ) (cost : I → S → A → ℝ) (budget : I → ℝ) :
    {v : ℝ | ∃ π : HistoryPolicy S A,
      (∀ i, pathReturn M γ π (cost i) ≤ budget i) ∧ v = pathReturn M γ π reward} =
      {v : ℝ | ∃ ρ : S → A → ℝ, CostFeasible M γ cost budget ρ ∧
        v = rewardFunctional reward ρ / (1 - γ)} := by
  ext v
  constructor
  · rintro ⟨π, hπ, rfl⟩
    exact ⟨pathOccupancy M γ π,
      (actual_history_path_cost_feasible_iff M γ hγ0 hγ1 π cost budget).mp hπ,
      actual_history_path_return_linear_formula M γ hγ0 hγ1 π reward⟩
  · rintro ⟨ρ, hρ, rfl⟩
    obtain ⟨π, _, hπ⟩ :=
      actual_every_feasible_flow_has_a_constructed_stationary_path M a₀ γ hγ0 hγ1 ρ hρ.1
    change pathOccupancy M γ π = ρ at hπ
    refine ⟨π, ?_, ?_⟩
    · apply (actual_history_path_cost_feasible_iff M γ hγ0 hγ1 π cost budget).mpr
      rwa [hπ]
    · rw [actual_history_path_return_linear_formula M γ hγ0 hγ1, hπ]

def historyPathAchievablePairs (M : Model S A) (γ : ℝ)
    (reward cost : S → A → ℝ) : Set (ℝ × ℝ) :=
  {z | ∃ π : HistoryPolicy S A, z = (pathReturn M γ π reward, pathReturn M γ π cost)}

theorem actual_all_history_path_return_pairs_equal_the_flow_linear_image
    (M : Model S A) (a₀ : A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (reward cost : S → A → ℝ) :
    historyPathAchievablePairs M γ reward cost =
      returnPairMap γ reward cost '' {ρ | FlowFeasible M γ ρ} := by
  have hpair (π : HistoryPolicy S A) :
      returnPairMap γ reward cost (pathOccupancy M γ π) =
        (pathReturn M γ π reward, pathReturn M γ π cost) := by
    apply Prod.ext <;>
      simp [returnPairMap, actual_history_path_return_linear_formula M γ hγ0 hγ1,
        div_eq_mul_inv, mul_comm]
  ext z
  constructor
  · rintro ⟨π, rfl⟩
    exact ⟨pathOccupancy M γ π,
      actual_all_history_policies_have_flow_feasible_path_occupancy M π γ hγ0 hγ1, hpair π⟩
  · rintro ⟨ρ, hρ, rfl⟩
    obtain ⟨π, hπ⟩ :=
      (actual_all_history_path_occupancies_equal_the_flow_polytope M a₀ γ hγ0 hγ1).symm ▸ hρ
    exact ⟨π, hπ ▸ hpair π⟩

theorem actual_all_history_path_return_pairs_are_convex
    (M : Model S A) (a₀ : A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (reward cost : S → A → ℝ) :
    Convex ℝ (historyPathAchievablePairs M γ reward cost) := by
  rw [actual_all_history_path_return_pairs_equal_the_flow_linear_image M a₀ γ hγ0 hγ1]
  exact (actual_nonnegative_flow_polyhedron_is_convex M γ).linear_image
    (returnPairMap γ reward cost)

end SafeLearning.CompleteFiniteHistoryPathLinearProgram
