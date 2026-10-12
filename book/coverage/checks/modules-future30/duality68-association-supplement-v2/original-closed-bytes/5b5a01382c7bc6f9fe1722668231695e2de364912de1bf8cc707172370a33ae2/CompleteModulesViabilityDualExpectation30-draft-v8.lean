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
    rw [mul_one] at h2
    simpa only [abs_sub_comm q p] using h1.trans h2
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
    {U : Type*} (reward risk : U → ℝ) [Nonempty {u : U // risk u = 0}] (B p : ℝ)
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
    (hattained : ∀ p : ℝ, 0 ≤ p → ∃ u, ∀ v, reward v-p*risk v ≤ reward u-p*risk u)
    (hallmaxsafe : ∀ p : ℝ, 0 ≤ p → threshold < p → ∀ u,
      (∀ v, reward v-p*risk v ≤ reward u-p*risk u) → risk u = 0) :
    ∀ p : ℝ, 0 ≤ p → threshold < p → actualDual reward risk p = P := by
  intro p hp0 hp
  obtain ⟨u,hu⟩ := hattained p hp0
  have hsafeu := hallmaxsafe p hp0 hp u hu
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
    (hattained : ∀ p : ℝ, 0 ≤ p → ∃ u, ∀ v, reward v-p*risk v ≤ reward u-p*risk u)
    (hallmaxsafe : ∀ p : ℝ, 0 ≤ p → threshold < p → ∀ u,
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
    · exact heq _ (by linarith [le_max_left (0:ℝ) threshold]) (by linarith [le_max_right (0:ℝ) threshold])⟩
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
    exact csInf_le hb ⟨hp,heq p hp htp⟩

section Expected
variable {X U : Type*} [MeasurableSpace X]

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
    have h := norm_integral_le_of_norm_le (μ := mu) (f := fun x => G x u) (integrable_const B) (ae_of_all _ (fun x => by simpa [Real.norm_eq_abs] using hbound x u))
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
    [Nonempty U] (mu : Measure X) [IsProbabilityMeasure mu] (G rho : X → U → ℝ) (B p : ℝ)
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

def actualConstrainedPointwiseValue {X U : Type*} (G rho : X → U → ℝ) (x : X) : ℝ :=
  ⨆ u : {u : U // rho x u = 0}, G x u.val

section PrimalExpected
variable {X U : Type*} [MeasurableSpace X] [Nonempty U]

omit [Nonempty U] in
theorem actual_common_safe_pointwise_optimum_derives_the_expected_primal_identity
    (mu : Measure X) [IsProbabilityMeasure mu] (G rho : X → U → ℝ) (B : ℝ)
    (hG : ∀ u, AEStronglyMeasurable (fun x => G x u) mu)
    (hrho : ∀ u, AEStronglyMeasurable (fun x => rho x u) mu)
    (hbound : ∀ x u, |G x u| ≤ B) (hrisk : ∀ x u, rho x u ∈ Icc 0 1)
    (common : U) (hsafe : ∀ x, rho x common = 0)
    (hbest : ∀ x u, rho x u = 0 → G x u ≤ G x common) :
    Integrable (actualConstrainedPointwiseValue G rho) mu ∧
      actualPrimal (expectedReward mu G) (expectedRisk mu rho) =
        ∫ x, actualConstrainedPointwiseValue G rho x ∂mu := by
  have hi := actual_bounded_measurable_reward_and_risk_are_integrable mu G rho B hG hrho hbound hrisk
  have hb := actual_expected_reward_and_risk_bounds mu G rho B hG hrho hbound hrisk
  have he : ∀ x, actualConstrainedPointwiseValue G rho x = G x common := by
    intro x
    let _ : Nonempty {u : U // rho x u = 0} := ⟨⟨common,hsafe x⟩⟩
    apply le_antisymm
    · exact ciSup_le (fun u => hbest x u.val u.property)
    · exact le_ciSup (show BddAbove (range (fun u : {u : U // rho x u = 0} => G x u.val)) from
        ⟨B,by rintro _ ⟨u,rfl⟩;exact (le_abs_self _).trans (hbound x u.val)⟩) ⟨common,hsafe x⟩
  have hiv : Integrable (actualConstrainedPointwiseValue G rho) mu :=
    (hi common).1.congr (ae_of_all _ (fun x => (he x).symm))
  have hsafeE : expectedRisk mu rho common = 0 := by
    simp [expectedRisk,hsafe]
  let _ : Nonempty {u : U // expectedRisk mu rho u = 0} := ⟨⟨common,hsafeE⟩⟩
  have heint : (∫ x,actualConstrainedPointwiseValue G rho x ∂mu) = expectedReward mu G common := by
    exact integral_congr_ae (ae_of_all _ he)
  refine ⟨hiv,le_antisymm ?_ ?_⟩
  · apply ciSup_le
    intro u
    rw [heint]
    have hu := (actual_expected_zero_risk_iff_almost_sure_zero_pointwise_risk mu rho u.val
      (hi u.val).2 (fun x => (hrisk x u.val).1)).mp u.property
    apply integral_mono_ae (hi u.val).1 (hi common).1
    filter_upwards [hu] with x hx
    exact hbest x u.val hx
  · rw [heint]
    exact le_ciSup (show BddAbove (range (fun u : {u : U // expectedRisk mu rho u = 0} => expectedReward mu G u.val)) from
      ⟨B,by rintro _ ⟨u,rfl⟩;exact (le_abs_self _).trans (hb.1 u.val)⟩) ⟨common,hsafeE⟩

theorem actual_common_pointwise_SVF_and_safe_optimum_give_zero_duality_gap
    (mu : Measure X) [IsProbabilityMeasure mu] (G rho : X → U → ℝ) (B p : ℝ)
    (hG : ∀ u, AEStronglyMeasurable (fun x => G x u) mu)
    (hrho : ∀ u, AEStronglyMeasurable (fun x => rho x u) mu)
    (hbound : ∀ x u, |G x u| ≤ B) (hrisk : ∀ x u, rho x u ∈ Icc 0 1)
    (safe common : U) (hsafe : ∀ x, rho x safe = 0)
    (hbest : ∀ x u, rho x u = 0 → G x u ≤ G x safe)
    (hmax : ∀ x u, G x u-p*rho x u ≤ G x common-p*rho x common)
    (hSVF : ∀ x u, (∀ v, G x v-p*rho x v ≤ G x u-p*rho x u) → rho x u = 0) :
    actualDual (expectedReward mu G) (expectedRisk mu rho) p =
      actualPrimal (expectedReward mu G) (expectedRisk mu rho) := by
  have hc : ∀ x, rho x common = 0 := fun x => hSVF x common (hmax x)
  have he : ∀ x, G x common = G x safe := by
    intro x
    apply le_antisymm (hbest x common (hc x))
    simpa [hc x,hsafe x] using hmax x safe
  have hs : ∀ x u, G x u-p*rho x u ≤ G x safe-p*rho x safe := by
    intro x u
    simpa [he x,hc x,hsafe x] using hmax x u
  have hd := (actual_common_pointwise_maximizer_derives_the_dual_expectation_identity
    mu G rho B p hG hrho hbound hrisk safe hs).2
  have hp := (actual_common_safe_pointwise_optimum_derives_the_expected_primal_identity
    mu G rho B hG hrho hbound hrisk safe hsafe hbest).2
  rw [hd,hp]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  have hv : pointwiseValue G rho p x = G x safe := by
    apply le_antisymm
    · apply ciSup_le
      intro u
      simpa [hsafe x] using hs x u
    · simpa [pointwiseValue,actualDual,hsafe x] using le_ciSup
        (actual_bounded_rewards_and_unit_risks_bound_every_penalized_return (G x) (rho x) B p (hbound x) (hrisk x)) safe
  have hcV : actualConstrainedPointwiseValue G rho x = G x safe := by
    let _ : Nonempty {u : U // rho x u = 0} := ⟨⟨safe,hsafe x⟩⟩
    apply le_antisymm
    · exact ciSup_le (fun u => hbest x u.val u.property)
    · exact le_ciSup (show BddAbove (range (fun u : {u : U // rho x u = 0} => G x u.val)) from
        ⟨B,by rintro _ ⟨u,rfl⟩;exact (le_abs_self _).trans (hbound x u.val)⟩) ⟨safe,hsafe x⟩
  exact hv.trans hcV.symm

theorem actual_expected_global_maximizer_is_almost_surely_safe_under_pointwise_SVF
    (mu : Measure X) [IsProbabilityMeasure mu] (G rho : X → U → ℝ) (B p : ℝ)
    (hG : ∀ u, AEStronglyMeasurable (fun x => G x u) mu)
    (hrho : ∀ u, AEStronglyMeasurable (fun x => rho x u) mu)
    (hbound : ∀ x u, |G x u| ≤ B) (hrisk : ∀ x u, rho x u ∈ Icc 0 1)
    (common : U) (hmax : ∀ x u, G x u-p*rho x u ≤ G x common-p*rho x common)
    (hSVF : ∀ x u, (∀ v, G x v-p*rho x v ≤ G x u-p*rho x u) → rho x u = 0)
    (u : U) (hmaxE : expectedReward mu G u-p*expectedRisk mu rho u =
      actualDual (expectedReward mu G) (expectedRisk mu rho) p) :
    ∀ᵐ x ∂mu, rho x u = 0 := by
  have hi := actual_bounded_measurable_reward_and_risk_are_integrable mu G rho B hG hrho hbound hrisk
  obtain ⟨hiv,hd⟩ := actual_common_pointwise_maximizer_derives_the_dual_expectation_identity
    mu G rho B p hG hrho hbound hrisk common hmax
  have hil : Integrable (fun x => G x u-p*rho x u) mu := (hi u).1.sub ((hi u).2.const_mul p)
  have hnn : ∀ x, 0 ≤ pointwiseValue G rho p x-(G x u-p*rho x u) := by
    intro x
    apply sub_nonneg.mpr
    exact le_ciSup (actual_bounded_rewards_and_unit_risks_bound_every_penalized_return (G x) (rho x) B p (hbound x) (hrisk x)) u
  have hzero : (∫ x,pointwiseValue G rho p x-(G x u-p*rho x u) ∂mu) = 0 := by
    rw [integral_sub hiv hil,← actual_expected_lagrangian_is_the_integral_of_the_pointwise_lagrangian mu G rho p u (hi u).1 (hi u).2,← hd,hmaxE,sub_self]
  have hz := (integral_eq_zero_iff_of_nonneg hnn (hiv.sub hil)).mp hzero
  filter_upwards [hz] with x hx
  have he : pointwiseValue G rho p x = G x u-p*rho x u := sub_eq_zero.mp hx
  apply hSVF x u
  intro v
  have h := le_ciSup (actual_bounded_rewards_and_unit_risks_bound_every_penalized_return (G x) (rho x) B p (hbound x) (hrisk x)) v
  exact h.trans_eq he

end PrimalExpected


def projectedZeroRiskStep (lambda eta cost : ℝ) : ℝ := max 0 (lambda+eta*cost)

theorem actual_zero_budget_projected_step_is_the_true_nonnegative_increment
    (lambda eta cost : ℝ) (hlambda : 0 ≤ lambda) (heta : 0 < eta) (hcost : 0 ≤ cost) :
    projectedZeroRiskStep lambda eta cost = lambda+eta*cost ∧
      lambda ≤ projectedZeroRiskStep lambda eta cost ∧
      (lambda < projectedZeroRiskStep lambda eta cost ↔ 0 < cost) ∧
      (projectedZeroRiskStep lambda eta cost = lambda ↔ cost = 0) := by
  have he : projectedZeroRiskStep lambda eta cost = lambda+eta*cost :=
    max_eq_right (add_nonneg hlambda (mul_nonneg heta.le hcost))
  rw [he]
  exact ⟨rfl,le_add_of_nonneg_right (mul_nonneg heta.le hcost),by
    constructor <;> intro h <;> nlinarith,by constructor <;> intro h <;> nlinarith⟩

theorem actual_zero_budget_expected_risk_search_stops_exactly_when_the_controller_is_AS_safe
    {X U : Type*} [MeasurableSpace X]
    (mu : Measure X) (rho : X → U → ℝ) (u : U) (lambda eta : ℝ)
    (hlambda : 0 ≤ lambda) (heta : 0 < eta)
    (hi : Integrable (fun x => rho x u) mu) (hn : ∀ x, 0 ≤ rho x u) :
    lambda ≤ projectedZeroRiskStep lambda eta (expectedRisk mu rho u) ∧
      (projectedZeroRiskStep lambda eta (expectedRisk mu rho u) = lambda ↔
        ∀ᵐ x ∂mu, rho x u = 0) := by
  have hc : 0 ≤ expectedRisk mu rho u := integral_nonneg hn
  have h := actual_zero_budget_projected_step_is_the_true_nonnegative_increment lambda eta (expectedRisk mu rho u) hlambda heta hc
  exact ⟨h.2.1,h.2.2.2.trans (actual_expected_zero_risk_iff_almost_sure_zero_pointwise_risk mu rho u hi hn)⟩

def actualBudgetDual {U : Type*} (reward risk : U → ℝ) (budget p : ℝ) : ℝ :=
  ⨆ u, reward u-p*(risk u-budget)

theorem actual_bounded_risk_dual_is_the_penalty_dual_plus_its_budget_constant
    {U : Type*} [Nonempty U] (reward risk : U → ℝ) (B budget p : ℝ)
    (hR : ∀ u, |reward u| ≤ B) (hC : ∀ u, risk u ∈ Icc 0 1) :
    actualBudgetDual reward risk budget p = actualDual reward risk p+p*budget := by
  have hb := actual_bounded_rewards_and_unit_risks_bound_every_penalized_return reward risk B p hR hC
  have hbb : BddAbove (range (fun u => reward u-p*(risk u-budget))) := by
    refine ⟨B+|p|+p*budget,?_⟩
    rintro _ ⟨u,rfl⟩
    have h := hb.choose_spec (mem_range_self u)
    have h' : reward u-p*risk u ≤ B+|p| := by
      have hr := le_ciSup hb u
      exact (show reward u-p*risk u ≤ B+|p| from by
        have ha := (abs_sub (reward u) (p*risk u)).trans (add_le_add (hR u) (show |p*risk u| ≤ |p| from by
          rw [abs_mul,abs_of_nonneg (hC u).1];exact (mul_le_mul_of_nonneg_left (hC u).2 (abs_nonneg p)).trans_eq (mul_one _)))
        exact (le_abs_self _).trans ha)
    linarith
  apply le_antisymm
  · apply ciSup_le
    intro u
    have h := le_ciSup hb u
    change reward u-p*risk u ≤ actualDual reward risk p at h
    linarith
  · have h : actualDual reward risk p ≤ actualBudgetDual reward risk budget p-p*budget := by
      apply ciSup_le
      intro u
      have h := le_ciSup hbb u
      change reward u-p*(risk u-budget) ≤ actualBudgetDual reward risk budget p at h
      linarith
    linarith

theorem actual_attained_primal_and_zero_gap_give_a_feasible_Lagrangian_maximizer_and_saddle
    {U : Type*} [Nonempty U] (reward risk : U → ℝ) (B budget p : ℝ)
    (hR : ∀ u, |reward u| ≤ B) (hC : ∀ u, risk u ∈ Icc 0 1)
    (hp : 0 ≤ p) (primal : U) (hfeasible : risk primal ≤ budget)
    (hzerogap : actualBudgetDual reward risk budget p = reward primal) :
    p*(budget-risk primal) = 0 ∧
      (∀ u, reward u-p*(risk u-budget) ≤ reward primal-p*(risk primal-budget)) ∧
      (∀ q : ℝ, 0 ≤ q → reward primal-p*(risk primal-budget) ≤ reward primal-q*(risk primal-budget)) := by
  have hd := actual_bounded_risk_dual_is_the_penalty_dual_plus_its_budget_constant reward risk B budget p hR hC
  have h0 := le_ciSup (actual_bounded_rewards_and_unit_risks_bound_every_penalized_return reward risk B p hR hC) primal
  change reward primal-p*risk primal ≤ actualDual reward risk p at h0
  have hnonneg : 0 ≤ p*(budget-risk primal) := mul_nonneg hp (sub_nonneg.mpr hfeasible)
  have he : p*(budget-risk primal) = 0 := by rw [hzerogap] at hd;linarith
  refine ⟨he,?_,?_⟩
  · intro u
    have h := le_ciSup (actual_bounded_rewards_and_unit_risks_bound_every_penalized_return reward risk B p hR hC) u
    change reward u-p*risk u ≤ actualDual reward risk p at h
    rw [hzerogap] at hd
    nlinarith
  · intro q hq
    have hqnonneg := mul_nonneg hq (sub_nonneg.mpr hfeasible)
    nlinarith

def actualPaperExampleReward (theta : ℝ) : ℝ := theta/10

def actualPaperExampleCost (theta : ℝ) : ℝ := theta/10

def actualPaperExamplePenalized (theta p : ℝ) : ℝ := theta/10*(1-p/10)

theorem actual_printed_paper_example_at_penalty_ten_ties_every_controller :
    (∀ theta ∈ Icc (0:ℝ) 1, actualPaperExamplePenalized theta 10 = 0) ∧
      (∀ theta ∈ Icc (0:ℝ) 1, ∀ other ∈ Icc (0:ℝ) 1,
        actualPaperExamplePenalized other 10 ≤ actualPaperExamplePenalized theta 10) := by
  constructor <;> intros <;> norm_num [actualPaperExamplePenalized]

theorem actual_paper_example_has_a_feasible_optimal_tie_an_infeasible_tie_and_a_suboptimal_tie :
    (1/10:ℝ) ∈ Icc (0:ℝ) 1 ∧
      actualPaperExampleCost (1/10) = 1/100 ∧
      (∀ theta ∈ Icc (0:ℝ) 1, actualPaperExampleCost theta ≤ 1/100 →
        actualPaperExampleReward theta ≤ actualPaperExampleReward (1/10)) ∧
      1 ∈ Icc (0:ℝ) 1 ∧ ¬ actualPaperExampleCost 1 ≤ 1/100 ∧
      0 ∈ Icc (0:ℝ) 1 ∧ actualPaperExampleCost 0 ≤ 1/100 ∧
      actualPaperExampleReward 0 < actualPaperExampleReward (1/10) := by
  norm_num [actualPaperExampleCost,actualPaperExampleReward]

theorem actual_printed_penalty_parameter_corresponds_to_a_rescaled_Lagrange_multiplier
    (theta p : ℝ) :
    actualPaperExamplePenalized theta p = actualPaperExampleReward theta-(p/10)*actualPaperExampleCost theta := by
  dsimp [actualPaperExamplePenalized,actualPaperExampleReward,actualPaperExampleCost]
  ring

def actualChainDualProfile (p : ℝ) : ℝ := max (-(7/4)) (-(3/2)-p/4)

theorem actual_chain_dual_profile_has_exact_optimal_ray_one :
    {p : ℝ | 0 ≤ p ∧ actualChainDualProfile p = -(7/4)} = Ici 1 := by
  ext p
  change (0 ≤ p ∧ actualChainDualProfile p = -(7/4)) ↔ 1 ≤ p
  dsimp [actualChainDualProfile]
  rw [max_eq_left_iff]
  constructor
  · rintro ⟨hp,he⟩;linarith
  · intro hp;constructor <;> linarith

theorem actual_chain_dual_profile_zero_gap_ray_is_strictly_below_the_conservative_threshold :
    actualChainDualProfile 1 = -(7/4) ∧ (1:ℝ)<15/2 ∧
      (∀ p : ℝ, 1 < p → -(3/2)-p/4 < -(7/4)) ∧
      -(3/2)-(1:ℝ)/4 = -(7/4) := by
  constructor
  · norm_num [actualChainDualProfile]
  · constructor
    · norm_num
    · constructor
      · intro p hp;linarith
      · norm_num



theorem actual_zero_gap_feasible_Lagrangian_maximizer_is_true_primal_optimal
    {U : Type*} [Nonempty U] (reward risk : U → ℝ) (B budget p : ℝ)
    (hR : ∀ u, |reward u| ≤ B) (hC : ∀ u, risk u ∈ Icc 0 1)
    (hp : 0 ≤ p) (primal : U) (hfeasible : risk primal ≤ budget)
    (hzerogap : actualBudgetDual reward risk budget p = reward primal) :
    ∀ u, risk u ≤ budget → reward u ≤ reward primal := by
  have hs := actual_attained_primal_and_zero_gap_give_a_feasible_Lagrangian_maximizer_and_saddle
    reward risk B budget p hR hC hp primal hfeasible hzerogap
  intro u hu
  have h := hs.2.1 u
  have hnonneg := mul_nonneg hp (sub_nonneg.mpr hu)
  nlinarith [hs.1]

end SafeLearning.CompleteModulesViabilityDualExpectation30
