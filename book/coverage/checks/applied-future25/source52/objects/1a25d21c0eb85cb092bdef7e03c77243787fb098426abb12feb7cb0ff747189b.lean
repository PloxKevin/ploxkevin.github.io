import Mathlib
import SafeLearning.CompleteAlternatingCMDP
import SafeLearning.CompletePolicyAdvantages
import SafeLearning.CompleteAppliedReturns

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SafeLearning.CompleteAlternatingCMDPReturns
open SafeLearning.CompleteAlternatingCMDP
open SafeLearning.CompletePolicyAdvantages (policy genuine_binary_policy_integral)

def stageLaw (p : Fin 2 → unitInterval) (n : ℕ) : PMF (Fin 2 × Fin 2) :=
  (policy (p (state n))).map (fun a => (state n, a))

theorem genuine_joint_probability (p : Fin 2 → unitInterval) (n : ℕ)
    (s a : Fin 2) : (stageLaw p n (s, a)).toReal =
      indicator s n * (policy (p s) a).toReal := by
  simp only [stageLaw, PMF.map_apply, tsum_fintype, Fin.sum_univ_two]
  unfold indicator
  generalize hs : state n = t
  fin_cases t <;> fin_cases s <;> fin_cases a <;> simp

theorem genuine_joint_integral (p : Fin 2 → unitInterval) (n : ℕ)
    (f : Fin 2 × Fin 2 → ℝ) :
    (∫ sa, f sa ∂(stageLaw p n).toMeasure) =
      (p (state n) : ℝ) * f (state n, 0) +
        (1 - (p (state n) : ℝ)) * f (state n, 1) := by
  rw [PMF.integral_eq_sum]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, smul_eq_mul]
  simp_rw [genuine_joint_probability]
  unfold indicator
  generalize hs : state n = t
  fin_cases t <;> simp [policy, PMF.ofFintype_apply,
    ENNReal.toReal_ofReal (p 0).2.1, ENNReal.toReal_ofReal (p 1).2.1,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (p 0).2.2),
    ENNReal.toReal_ofReal (sub_nonneg.mpr (p 1).2.2)]

def stageReward (sa : Fin 2 × Fin 2) : ℝ := if sa.2 = 0 then 1 else 0
def stageCost (sa : Fin 2 × Fin 2) : ℝ :=
  if sa.2 = 0 then (if sa.1 = 0 then 1 else 2) else 0

theorem actual_stage_expectations (p : Fin 2 → unitInterval) (n : ℕ) :
    (∫ sa, stageReward sa ∂(stageLaw p n).toMeasure) =
      indicator 0 n * (p 0 : ℝ) + indicator 1 n * (p 1 : ℝ) ∧
    (∫ sa, stageCost sa ∂(stageLaw p n).toMeasure) =
      indicator 0 n * (p 0 : ℝ) + indicator 1 n * (2 * (p 1 : ℝ)) := by
  rw [genuine_joint_integral, genuine_joint_integral]
  unfold indicator
  generalize hs : state n = t
  fin_cases t <;> simp [stageReward, stageCost, mul_comm]

def discountedReturn (p : Fin 2 → unitInterval) (f : Fin 2 × Fin 2 → ℝ) : ℝ :=
  ∑' n : ℕ, (1 / 2 : ℝ) ^ n * ∫ sa, f sa ∂(stageLaw p n).toMeasure

theorem actual_geometric_weighted_expectation (x y : ℝ) :
    (∑' n : ℕ, (1 / 2 : ℝ) ^ n *
      (indicator 0 n * x + indicator 1 n * y)) =
        discountedMass 0 * x + discountedMass 1 * y := by
  simp_rw [mul_add, ← mul_assoc]
  rw [((discounted_mass_summable 0).mul_right x).tsum_add
    ((discounted_mass_summable 1).mul_right y), tsum_mul_right, tsum_mul_right]
  rfl

theorem genuine_infinite_reward_and_cost (p : Fin 2 → unitInterval) :
    discountedReturn p stageReward = reward (p 0) (p 1) ∧
      discountedReturn p stageCost = cost (p 0) (p 1) := by
  have hm0 : discountedMass 0 = 4 / 3 := by
    have h := genuine_state_marginals_and_normalization.1
    unfold occupancy at h
    linarith
  have hm1 : discountedMass 1 = 2 / 3 := by
    have h := genuine_state_marginals_and_normalization.2.1
    unfold occupancy at h
    linarith
  unfold discountedReturn
  simp_rw [(actual_stage_expectations p _).1, (actual_stage_expectations p _).2]
  rw [actual_geometric_weighted_expectation, actual_geometric_weighted_expectation,
    hm0, hm1]
  unfold reward cost
  constructor <;> ring

def normalizedJoint (p : Fin 2 → unitInterval) (s a : Fin 2) : ℝ :=
  (1 / 2) * ∑' n : ℕ, (1 / 2 : ℝ) ^ n * (stageLaw p n (s, a)).toReal

theorem genuine_state_action_occupancy (p : Fin 2 → unitInterval) (s a : Fin 2) :
    normalizedJoint p s a = occupancy s * (policy (p s) a).toReal := by
  unfold normalizedJoint occupancy discountedMass
  simp_rw [genuine_joint_probability, ← mul_assoc]
  rw [tsum_mul_right]
  ring

theorem literal_source_fast_occupancies (p : Fin 2 → unitInterval) :
    normalizedJoint p 0 0 = (2 / 3) * (p 0 : ℝ) ∧
      normalizedJoint p 1 0 = (1 / 3) * (p 1 : ℝ) := by
  simp [genuine_state_action_occupancy, genuine_state_marginals_and_normalization.1,
    genuine_state_marginals_and_normalization.2.1, policy, PMF.ofFintype_apply,
    ENNReal.toReal_ofReal (p 0).2.1, ENNReal.toReal_ofReal (p 1).2.1]

theorem genuine_pathwise_return_interchange {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (joint : ℕ → Ω → Fin 2 × Fin 2)
    (p : Fin 2 → unitInterval) (hlaw : ∀ n, HasLaw (joint n) (stageLaw p n).toMeasure μ)
    (f : Fin 2 × Fin 2 → ℝ) (bound : ℝ) (hf : ∀ sa, |f sa| ≤ bound) :
    (∫ omega, ∑' n : ℕ, (1 / 2 : ℝ) ^ n * f (joint n omega) ∂μ) =
      discountedReturn p f := by
  have hm : Measurable f := measurable_of_finite f
  have hmeas : ∀ n, AEStronglyMeasurable (fun omega => f (joint n omega)) μ :=
    fun n => (hm.comp_aemeasurable (hlaw n).aemeasurable).aestronglyMeasurable
  have hb : ∀ n, ∀ᵐ omega ∂μ, |f (joint n omega)| ≤ bound :=
    fun n => ae_of_all μ (fun omega => hf (joint n omega))
  rw [CompleteAppliedReturns.discounted_expectation_interchange μ _ (1 / 2) bound
    (by norm_num) hmeas hb]
  unfold discountedReturn
  apply tsum_congr
  intro n
  rw [show (fun omega => f (joint n omega)) = f ∘ joint n from rfl,
    (hlaw n).integral_comp hm.aestronglyMeasurable]

theorem genuine_pathwise_reward_and_cost {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (joint : ℕ → Ω → Fin 2 × Fin 2)
    (p : Fin 2 → unitInterval) (hlaw : ∀ n, HasLaw (joint n) (stageLaw p n).toMeasure μ) :
    (∫ omega, ∑' n : ℕ, (1 / 2 : ℝ) ^ n * stageReward (joint n omega) ∂μ) =
      reward (p 0) (p 1) ∧
    (∫ omega, ∑' n : ℕ, (1 / 2 : ℝ) ^ n * stageCost (joint n omega) ∂μ) =
      cost (p 0) (p 1) := by
  have hr : ∀ sa, |stageReward sa| ≤ 1 := by
    rintro ⟨s, a⟩
    fin_cases s <;> fin_cases a <;> norm_num [stageReward]
  have hc : ∀ sa, |stageCost sa| ≤ 2 := by
    rintro ⟨s, a⟩
    fin_cases s <;> fin_cases a <;> norm_num [stageCost]
  exact ⟨(genuine_pathwise_return_interchange μ joint p hlaw stageReward 1 hr).trans
      (genuine_infinite_reward_and_cost p).1,
    (genuine_pathwise_return_interchange μ joint p hlaw stageCost 2 hc).trans
      (genuine_infinite_reward_and_cost p).2⟩

end SafeLearning.CompleteAlternatingCMDPReturns
