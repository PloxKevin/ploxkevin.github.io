import SafeLearning.CompletePolicyAdvantages
import SafeLearning.CompletePolicyGeometry
import SafeLearning.CompletePolicyChecks
import SafeLearning.CompleteAppliedReturns
import SafeLearning.CoreModules

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix BigOperators

namespace SafeLearning.CompletePolicyPracticeConsequences
open CompletePolicyAdvantages

def reward (gamma : ℝ) (i : Fin 2) : ℝ := actionValue i - gamma * stateValue
def discountedValue (q : unitInterval) (gamma : ℝ) : ℝ :=
  ∑' n : ℕ, gamma ^ n * ∫ i, reward gamma i ∂(policy q).toMeasure

theorem actual_one_step_reward (q : unitInterval) (gamma : ℝ) :
    (∫ i, reward gamma i ∂(policy q).toMeasure) = 1 + 4 * (q : ℝ) - 2 * gamma := by
  rw [genuine_binary_policy_integral]
  simp only [reward, actionValue, source_state_value_and_advantages.1,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem actual_discounted_value (q : unitInterval) (gamma : ℝ) (hg : |gamma| < 1) :
    discountedValue q gamma = (1 + 4 * (q : ℝ) - 2 * gamma) / (1 - gamma) := by
  simp only [discountedValue, actual_one_step_reward]
  exact CoreModules.discounted_constant _ gamma hg

theorem genuine_source_Q_and_old_Bellman_value (gamma : ℝ) (hg : |gamma| < 1) :
    discountedValue oldParameter gamma = stateValue ∧
      ∀ i, reward gamma i + gamma * discountedValue oldParameter gamma = actionValue i := by
  have hn : 1 - gamma ≠ 0 := by have h := (abs_lt.mp hg).2; linarith
  have hv : discountedValue oldParameter gamma = 2 := by
    rw [actual_discounted_value _ _ hg]
    norm_num [oldParameter]
    field_simp
  refine ⟨by rw [hv, source_state_value_and_advantages.1], ?_⟩
  intro i
  rw [reward, hv, source_state_value_and_advantages.1]
  ring

theorem actual_discounted_state_visitation (gamma : ℝ) (hg : |gamma| < 1) :
    (1 - gamma) * (∑' n : ℕ, gamma ^ n * (1 : ℝ)) = 1 := by
  have hn : 1 - gamma ≠ 0 := by have h := (abs_lt.mp hg).2; linarith
  rw [CoreModules.discounted_constant _ _ hg]
  field_simp

theorem actual_return_change_needs_discounted_visitation_factor
    (gamma : ℝ) (hg : |gamma| < 1) :
    discountedValue newParameter gamma - discountedValue oldParameter gamma =
      (∫ i, advantage i ∂(policy newParameter).toMeasure) / (1 - gamma) := by
  rw [actual_discounted_value _ _ hg, actual_discounted_value _ _ hg,
    actual_old_and_new_advantage_expectations.2]
  norm_num [oldParameter, newParameter]
  ring

theorem genuine_pathwise_return {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (action : ℕ → Ω → Fin 2)
    (q : unitInterval) (gamma : ℝ) (hg : |gamma| < 1)
    (hlaw : ∀ n, HasLaw (action n) (policy q).toMeasure μ) :
    (∫ ω, ∑' n : ℕ, gamma ^ n * reward gamma (action n ω) ∂μ) =
      discountedValue q gamma := by
  have hm : Measurable (reward gamma) := measurable_from_top
  have hmeas : ∀ n, AEStronglyMeasurable (fun ω => reward gamma (action n ω)) μ :=
    fun n => (hm.comp_aemeasurable (hlaw n).aemeasurable).aestronglyMeasurable
  have hb : ∀ n, ∀ᵐ ω ∂μ, |reward gamma (action n ω)| ≤ 5 + 2 * |gamma| := by
    intro n
    exact ae_of_all μ (fun ω => by
      have hh := abs_sub (actionValue (action n ω)) (gamma * stateValue)
      generalize action n ω = i at *
      fin_cases i <;> norm_num [reward, actionValue, source_state_value_and_advantages.1,
        abs_mul] at hh ⊢ <;> linarith)
  rw [CompleteAppliedReturns.discounted_expectation_interchange μ _ gamma _ hg hmeas hb]
  unfold discountedValue
  apply tsum_congr
  intro n
  rw [show (fun ω => reward gamma (action n ω)) = reward gamma ∘ action n from rfl,
    (hlaw n).integral_comp hm.aestronglyMeasurable]

def crossMetric : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1 / 2; 1 / 2, 1]
def weightedObjective (x : Fin 2 → ℝ) : ℝ :=
  (1 / 2) * dotProduct (x - ![3 / 5, 1 / 5])
    (crossMetric *ᵥ (x - ![3 / 5, 1 / 5]))
def weightedProjection : Fin 2 → ℝ := ![1 / 10, 9 / 20]

theorem actual_cross_quadratic (x : Fin 2 → ℝ) :
    dotProduct x (crossMetric *ᵥ x) =
      (x 1 + x 0 / 2) ^ 2 + (3 / 4) * x 0 ^ 2 := by
  simp [crossMetric, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem genuine_cross_metric_is_positive_definite : crossMetric.PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [crossMetric, Matrix.IsHermitian]
  · intro x hx
    simp only [star_trivial]
    rw [actual_cross_quadratic]
    have h0 := sq_nonneg (x 0)
    have h1 := sq_nonneg (x 1 + x 0 / 2)
    by_contra h
    have hz : x 0 = 0 := by nlinarith
    have hy : x 1 = 0 := by rw [hz] at h h1; nlinarith
    apply hx
    ext i
    fin_cases i <;> simp [hz, hy]

theorem actual_weighted_distance (x : Fin 2 → ℝ) :
    weightedObjective x = (1 / 2) *
      ((x 1 - 1 / 5 + (x 0 - 3 / 5) / 2) ^ 2 +
        (3 / 4) * (x 0 - 3 / 5) ^ 2) := by
  rw [weightedObjective, actual_cross_quadratic]
  rfl

theorem another_genuine_metric_changes_the_projection (x : Fin 2 → ℝ)
    (hx : x 0 ≤ 1 / 10) :
    weightedProjection 0 ≤ 1 / 10 ∧
      weightedObjective weightedProjection = 3 / 32 ∧
      weightedObjective weightedProjection ≤ weightedObjective x ∧
      (weightedObjective x = weightedObjective weightedProjection ↔ x = weightedProjection) ∧
      weightedProjection ≠ ![1 / 10, 1 / 5] := by
  have hp : weightedObjective weightedProjection = 3 / 32 := by
    norm_num [actual_weighted_distance, weightedProjection]
  have hs := sq_nonneg (x 1 - 1 / 5 + (x 0 - 3 / 5) / 2)
  have hf : 1 / 4 ≤ (x 0 - 3 / 5) ^ 2 := by nlinarith [sq_nonneg (x 0 - 1 / 10)]
  have he := actual_weighted_distance x
  refine ⟨by norm_num [weightedProjection], hp, by nlinarith, ?_, ?_⟩
  · constructor
    · intro h
      have h0 : x 0 = 1 / 10 := by nlinarith [sq_nonneg (x 0 - 1 / 10)]
      have h1 : x 1 = 9 / 20 := by rw [h0] at hs he; nlinarith
      ext i
      fin_cases i
      · simpa [weightedProjection] using h0
      · simpa [weightedProjection] using h1
    · rintro rfl
      rfl
  · intro h
    have hh := congrFun h 1
    norm_num [weightedProjection] at hh

theorem genuine_nonlinear_and_linearized_origin_derivatives :
    HasDerivAt (fun t : ℝ => CompletePolicyChecks.linearResidual ![t, 1 / 10]) 1 0 ∧
      HasDerivAt (fun t : ℝ => CompletePolicyChecks.nonlinearResidual ![t, 1 / 10]) 1 0 := by
  constructor
  · simpa [CompletePolicyChecks.actual_affine_residual] using
      (hasDerivAt_id (0 : ℝ)).const_add (-1 / 5)
  · convert ((hasDerivAt_id (0 : ℝ)).const_add (-1 / 5)).add
      (((hasDerivAt_id (0 : ℝ)).pow 2).const_mul 20) using 1
    · ext t
      simp [CompletePolicyChecks.nonlinearResidual, CompletePolicyChecks.actual_affine_residual]
    · norm_num

end SafeLearning.CompletePolicyPracticeConsequences
