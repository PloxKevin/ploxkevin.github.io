import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology NNReal

namespace SafeLearning.CompleteModulesViabilityDualExpectation30

def actualDual {U : Type*} (reward risk : U → ℝ) (p : ℝ) : ℝ :=
  ⨆ u, reward u - p * risk u

def actualPrimal {U : Type*} (reward risk : U → ℝ) : ℝ :=
  ⨆ u : {u : U // risk u = 0}, reward u.val

theorem actual_bounded_rewards_and_unit_risks_bound_every_penalized_return
    {U : Type*} (reward risk : U → ℝ) (B p : ℝ)
    (hR : ∀ u, |reward u| ≤ B) (hC : ∀ u, risk u ∈ Icc 0 1) :
    BddAbove (range (fun u => reward u - p * risk u)) := by
  refine ⟨B + |p|, ?_⟩
  rintro _ ⟨u,rfl⟩
  have hc : |risk u| ≤ 1 := by rw [abs_of_nonneg (hC u).1]; exact (hC u).2
  have hp : |p * risk u| ≤ |p| := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hc (abs_nonneg p)).trans_eq (mul_one _)
  calc
    reward u - p * risk u ≤ |reward u - p * risk u| := le_abs_self _
    _ ≤ |reward u| + |p * risk u| := abs_sub _ _
    _ ≤ B + |p| := add_le_add (hR u) hp

theorem actual_dual_is_nonincreasing
    {U : Type*} [Nonempty U] (reward risk : U → ℝ) (B : ℝ)
    (hR : ∀ u, |reward u| ≤ B) (hC : ∀ u, risk u ∈ Icc 0 1) :
    Antitone (actualDual reward risk) := by
  intro p q hpq
  apply ciSup_le
  intro u
  have h := le_ciSup (actual_bounded_rewards_and_unit_risks_bound_every_penalized_return reward risk B p hR hC) u
  change reward u-p*risk u ≤ actualDual reward risk p at h
  have hm := mul_le_mul_of_nonneg_right hpq (hC u).1
  exact (sub_le_sub_left hm (reward u)).trans h

theorem actual_dual_is_convex
    {U : Type*} [Nonempty U] (reward risk : U → ℝ) (B : ℝ)
    (hR : ∀ u, |reward u| ≤ B) (hC : ∀ u, risk u ∈ Icc 0 1) :
    ConvexOn ℝ univ (actualDual reward risk) := by
  refine ⟨convex_univ,?_⟩
  intro p hp q hq a b ha hb hab
  apply ciSup_le
  intro u
  have hp' := le_ciSup (actual_bounded_rewards_and_unit_risks_bound_every_penalized_return reward risk B p hR hC) u
  have hq' := le_ciSup (actual_bounded_rewards_and_unit_risks_bound_every_penalized_return reward risk B q hR hC) u
  change reward u-p*risk u ≤ actualDual reward risk p at hp'
  change reward u-q*risk u ≤ actualDual reward risk q at hq'
  have he : reward u-(a*p+b*q)*risk u = a*(reward u-p*risk u)+b*(reward u-q*risk u) := by
    linear_combination -(reward u)*hab
  change reward u-(a*p+b*q)*risk u ≤ a*actualDual reward risk p+b*actualDual reward risk q
  rw [he]
  exact add_le_add (mul_le_mul_of_nonneg_left hp' ha) (mul_le_mul_of_nonneg_left hq' hb)

theorem actual_dual_change_is_bounded_by_the_multiplier_change
    {U : Type*} [Nonempty U] (reward risk : U → ℝ) (B p q : ℝ)
    (hR : ∀ u, |reward u| ≤ B) (hC : ∀ u, risk u ∈ Icc 0 1) :
    actualDual reward risk p ≤ actualDual reward risk q + |p-q| := by
  apply ciSup_le
  intro u
  have h := le_ciSup (actual_bounded_rewards_and_unit_risks_bound_every_penalized_return reward risk B q hR hC) u
  change reward u-q*risk u ≤ actualDual reward risk q at h
  have hm : (q-p)*risk u ≤ |p-q| := by
    have h1 := mul_le_mul_of_nonneg_right (le_abs_self (q-p)) (hC u).1
    have h2 := mul_le_mul_of_nonneg_left (hC u).2 (abs_nonneg (q-p))
    rw [mul_one, abs_sub_comm] at h2
    exact h1.trans h2
  linarith

theorem actual_dual_is_one_Lipschitz_and_continuous
    {U : Type*} [Nonempty U] (reward risk : U → ℝ) (B : ℝ)
    (hR : ∀ u, |reward u| ≤ B) (hC : ∀ u, risk u ∈ Icc 0 1) :
    LipschitzWith 1 (actualDual reward risk) ∧ Continuous (actualDual reward risk) := by
  have hl : LipschitzWith 1 (actualDual reward risk) := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    have h1 := actual_dual_change_is_bounded_by_the_multiplier_change reward risk B p q hR hC
    have h2 := actual_dual_change_is_bounded_by_the_multiplier_change reward risk B q p hR hC
    rw [abs_sub_comm q p] at h2
    simp only [Real.dist_eq, NNReal.coe_one, one_mul]
    exact abs_sub_le_iff.mpr ⟨by linarith,by linarith⟩
  exact ⟨hl,hl.continuous⟩

theorem actual_zero_risk_feasible_reward_is_below_every_dual
    {U : Type*} (reward risk : U → ℝ) (B p : ℝ)
    (hR : ∀ u, |reward u| ≤ B) (hC : ∀ u, risk u ∈ Icc 0 1)
    (u : U) (hu : risk u = 0) : reward u ≤ actualDual reward risk p := by
  simpa [actualDual,hu] using le_ciSup
    (actual_bounded_rewards_and_unit_risks_bound_every_penalized_return reward risk B p hR hC) u

theorem actual_zero_risk_primal_is_below_every_dual
    {U : Type*} [Nonempty {u : U // risk u = 0}] (reward risk : U → ℝ) (B p : ℝ)
    (hR : ∀ u, |reward u| ≤ B) (hC : ∀ u, risk u ∈ Icc 0 1) :
    actualPrimal reward risk ≤ actualDual reward risk p := by
  apply ciSup_le
  intro u
  exact actual_zero_risk_feasible_reward_is_below_every_dual reward risk B p hR hC u.val u.property

theorem actual_zero_risk_constraint_has_no_strict_Slater_point
    {U : Type*} (risk : U → ℝ) (hC : ∀ u, 0 ≤ risk u) :
    ¬ ∃ u, risk u < 0 := by
  rintro ⟨u,hu⟩
  exact (not_lt_of_ge (hC u)) hu

theorem actual_safe_common_optimum_and_safe_penalized_maximizers_give_exact_value
    {U : Type*} [Nonempty U] (reward risk : U → ℝ) (B P threshold : ℝ)
    (hR : ∀ u, |reward u| ≤ B) (hC : ∀ u, risk u ∈ Icc 0 1)
    (safe : U) (hsafe : risk safe = 0) (hsafevalue : reward safe = P)
    (hsafebound : ∀ u, risk u = 0 → reward u ≤ P)
    (hattained : ∀ p : ℝ, ∃ u, ∀ v, reward v-p*risk v ≤ reward u-p*risk u)
    (hallmaxsafe : ∀ p : ℝ, threshold < p → ∀ u,
      (∀ v, reward v-p*risk v ≤ reward u-p*risk u) → risk u = 0) :
    ∀ p : ℝ, threshold < p → actualDual reward risk p = P := by
  intro p hp
  obtain ⟨u,hu⟩ := hattained p
  have hsafeu := hallmaxsafe p hp u hu
  apply le_antisymm
  · apply ciSup_le
    intro v
    exact (hu v).trans (by simpa [hsafeu] using hsafebound u hsafeu)
  · simpa [hsafevalue] using actual_zero_risk_feasible_reward_is_below_every_dual reward risk B p hR hC safe hsafe

theorem actual_optimal_nonnegative_multiplier_set_is_a_closed_ray
    {U : Type*} [Nonempty U] (reward risk : U → ℝ) (B P threshold : ℝ)
    (hR : ∀ u, |reward u| ≤ B) (hC : ∀ u, risk u ∈ Icc 0 1)
    (safe : U) (hsafe : risk safe = 0) (hsafevalue : reward safe = P)
    (hsafebound : ∀ u, risk u = 0 → reward u ≤ P)
    (hattained : ∀ p : ℝ, ∃ u, ∀ v, reward v-p*risk v ≤ reward u-p*risk u)
    (hallmaxsafe : ∀ p : ℝ, threshold < p → ∀ u,
      (∀ v, reward v-p*risk v ≤ reward u-p*risk u) → risk u = 0) :
    ∃ lambda0 : ℝ, 0 ≤ lambda0 ∧
      {p : ℝ | 0 ≤ p ∧ actualDual reward risk p = P} = Ici lambda0 ∧
      ∀ p : ℝ, 0 ≤ p → threshold < p → lambda0 ≤ p := by
  let S : Set ℝ := {p | 0 ≤ p ∧ actualDual reward risk p = P}
  have hc : IsClosed S := isClosed_Ici.inter (isClosed_eq
    (actual_dual_is_one_Lipschitz_and_continuous reward risk B hR hC).2 continuous_const)
  have heq := actual_safe_common_optimum_and_safe_penalized_maximizers_give_exact_value
    reward risk B P threshold hR hC safe hsafe hsafevalue hsafebound hattained hallmaxsafe
  have hn : S.Nonempty := ⟨max 0 threshold+1,by
    change 0 ≤ max 0 threshold+1 ∧ actualDual reward risk (max 0 threshold+1) = P
    constructor
    · linarith [le_max_left (0:ℝ) threshold]
    · exact heq _ (by linarith [le_max_right (0:ℝ) threshold])⟩
  have hb : BddBelow S := ⟨0,fun p hp => hp.1⟩
  have hm : sInf S ∈ S := hc.csInf_mem hn hb
  refine ⟨sInf S,hm.1,?_,?_⟩
  · ext p
    constructor
    · intro hp;exact csInf_le hb hp
    · intro hp
      have hmono := actual_dual_is_nonincreasing reward risk B hR hC hp
      have hlower := actual_zero_risk_feasible_reward_is_below_every_dual reward risk B p hR hC safe hsafe
      exact ⟨hm.1.trans hp,le_antisymm (hmono.trans_eq hm.2) (by simpa [hsafevalue] using hlower)⟩
  · intro p hp htp
    exact csInf_le hb ⟨hp,heq p htp⟩

section Expected
variable {X U : Type*} [MeasurableSpace X] [Nonempty U]

def expectedReward (mu : Measure X) (G : X → U → ℝ) (u : U) : ℝ := ∫ x, G x u ∂mu

def expectedRisk (mu : Measure X) (rho : X → U → ℝ) (u : U) : ℝ := ∫ x, rho x u ∂mu

def pointwiseValue (G rho : X → U → ℝ) (p : ℝ) (x : X) : ℝ :=
  actualDual (G x) (rho x) p

theorem actual_bounded_measurable_reward_and_risk_are_integrable
    (mu : Measure X) [IsProbabilityMeasure mu] (G rho : X → U → ℝ) (B : ℝ)
    (hG : ∀ u, AEStronglyMeasurable (fun x => G x u) mu)
    (hrho : ∀ u, AEStronglyMeasurable (fun x => rho x u) mu)
    (hbound : ∀ x u, |G x u| ≤ B) (hrisk : ∀ x u, rho x u ∈ Icc 0 1) :
    ∀ u, Integrable (fun x => G x u) mu ∧ Integrable (fun x => rho x u) mu := by
  intro u
  constructor
  · exact (integrable_const B).mono' (hG u) (ae_of_all _ (fun x => by simpa [Real.norm_eq_abs] using hbound x u))
  · exact (integrable_const (1:ℝ)).mono' (hrho u) (ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hrisk x u).1];exact (hrisk x u).2))

theorem actual_expected_reward_and_risk_bounds
    (mu : Measure X) [IsProbabilityMeasure mu] (G rho : X → U → ℝ) (B : ℝ)
    (hG : ∀ u, AEStronglyMeasurable (fun x => G x u) mu)
    (hrho : ∀ u, AEStronglyMeasurable (fun x => rho x u) mu)
    (hbound : ∀ x u, |G x u| ≤ B) (hrisk : ∀ x u, rho x u ∈ Icc 0 1) :
    (∀ u, |expectedReward mu G u| ≤ B) ∧ (∀ u, expectedRisk mu rho u ∈ Icc 0 1) := by
  have hi := actual_bounded_measurable_reward_and_risk_are_integrable mu G rho B hG hrho hbound hrisk
  constructor
  · intro u
    have h := norm_integral_le_of_norm_le (integrable_const B) (ae_of_all _ (fun x => by simpa [Real.norm_eq_abs] using hbound x u))
    simpa [expectedReward,Real.norm_eq_abs] using h
  · intro u
    constructor
    · exact integral_nonneg (fun x => (hrisk x u).1)
    · have h := integral_mono (hi u).2 (integrable_const (1:ℝ)) (fun x => (hrisk x u).2)
      simpa [expectedRisk] using h

theorem actual_expected_lagrangian_is_the_integral_of_the_pointwise_lagrangian
    (mu : Measure X) (G rho : X → U → ℝ) (p : ℝ) (u : U)
    (hG : Integrable (fun x => G x u) mu) (hrho : Integrable (fun x => rho x u) mu) :
    expectedReward mu G u-p*expectedRisk mu rho u = ∫ x, G x u-p*rho x u ∂mu := by
  rw [integral_sub hG (hrho.const_mul p), integral_const_mul]
  rfl

theorem actual_expected_zero_risk_iff_almost_sure_zero_pointwise_risk
    (mu : Measure X) (rho : X → U → ℝ) (u : U)
    (hi : Integrable (fun x => rho x u) mu) (hn : ∀ x, 0 ≤ rho x u) :
    expectedRisk mu rho u = 0 ↔ ∀ᵐ x ∂mu, rho x u = 0 := by
  exact integral_eq_zero_iff_of_nonneg hn hi

theorem actual_common_pointwise_maximizer_derives_the_dual_expectation_identity
    (mu : Measure X) [IsProbabilityMeasure mu] (G rho : X → U → ℝ) (B p : ℝ)
    (hG : ∀ u, AEStronglyMeasurable (fun x => G x u) mu)
    (hrho : ∀ u, AEStronglyMeasurable (fun x => rho x u) mu)
    (hbound : ∀ x u, |G x u| ≤ B) (hrisk : ∀ x u, rho x u ∈ Icc 0 1)
    (common : U) (hmax : ∀ x u, G x u-p*rho x u ≤ G x common-p*rho x common) :
    Integrable (pointwiseValue G rho p) mu ∧
      actualDual (expectedReward mu G) (expectedRisk mu rho) p = ∫ x, pointwiseValue G rho p x ∂mu := by
  have hi := actual_bounded_measurable_reward_and_risk_are_integrable mu G rho B hG hrho hbound hrisk
  have he : ∀ x, pointwiseValue G rho p x = G x common-p*rho x common := by
    intro x
    apply le_antisymm
    · exact ciSup_le (hmax x)
    · exact le_ciSup (actual_bounded_rewards_and_unit_risks_bound_every_penalized_return (G x) (rho x) B p (hbound x) (hrisk x)) common
  have hiv : Integrable (pointwiseValue G rho p) mu := by
    have h := (hi common).1.sub ((hi common).2.const_mul p)
    exact h.congr (ae_of_all _ (fun x => (he x).symm))
  refine ⟨hiv,le_antisymm ?_ ?_⟩
  · apply ciSup_le
    intro u
    rw [actual_expected_lagrangian_is_the_integral_of_the_pointwise_lagrangian mu G rho p u (hi u).1 (hi u).2]
    exact integral_mono ((hi u).1.sub ((hi u).2.const_mul p)) hiv (fun x => by rw [he x];exact hmax x u)
  · have hb := actual_expected_reward_and_risk_bounds mu G rho B hG hrho hbound hrisk
    have h := le_ciSup (actual_bounded_rewards_and_unit_risks_bound_every_penalized_return (expectedReward mu G) (expectedRisk mu rho) B p hb.1 hb.2) common
    change expectedReward mu G common-p*expectedRisk mu rho common ≤ actualDual (expectedReward mu G) (expectedRisk mu rho) p at h
    rw [actual_expected_lagrangian_is_the_integral_of_the_pointwise_lagrangian mu G rho p common (hi common).1 (hi common).2] at h
    simpa only [show (fun x => G x common-p*rho x common) = pointwiseValue G rho p from funext (fun x => (he x).symm)] using h

end Expected
end SafeLearning.CompleteModulesViabilityDualExpectation30
