import SafeLearning.CompleteFiniteCMDPLinearProgram
import SafeLearning.CompleteFiniteCMDPVertexClassification
import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Set
open scoped BigOperators
namespace SafeLearning.CompleteModulesFinitePolytopeDuality30

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {I : Type*} [Fintype I]

/-- A finite polytope with one feasible linear inequality has an attained primal point and
an actual nonnegative Lagrange multiplier, even when strict feasibility fails. -/
theorem actual_feasible_finite_polytope_has_a_single_constraint_saddle
    (vertex : I → E) (reward cost : E →ₗ[ℝ] ℝ) (budget : ℝ)
    (hr : Continuous reward) (hc : Continuous cost)
    (hne : ∃ x ∈ convexHull ℝ (range vertex), cost x ≤ budget) :
    ∃ (x : E) (lambda : ℝ),
      x ∈ convexHull ℝ (range vertex) ∧ cost x ≤ budget ∧ 0 ≤ lambda ∧
      lambda * (cost x - budget) = 0 ∧
      ∀ y ∈ convexHull ℝ (range vertex),
        reward y - lambda * (cost y - budget) ≤ reward x := by
  classical
  let K := convexHull ℝ (range vertex)
  have hK : IsCompact K := (Set.finite_range vertex).isCompact_convexHull ℝ
  have hconv : Convex ℝ K := convex_convexHull ℝ _
  have hf : IsCompact {x | x ∈ K ∧ cost x ≤ budget} :=
    hK.inter_right (isClosed_le hc continuous_const)
  obtain ⟨x, hx, hmax⟩ := hf.exists_isMaxOn hne hr.continuousOn
  let slope : Option I → ℝ := fun z => match z with
    | none => 0
    | some i => if budget < cost (vertex i) then
        (reward (vertex i) - reward x) / (cost (vertex i) - budget) else 0
  let lambda : ℝ := Finset.univ.sup' Finset.univ_nonempty slope
  have hlower (z : Option I) : slope z ≤ lambda :=
    Finset.le_sup' slope (Finset.mem_univ z)
  have hl0 : 0 ≤ lambda := by simpa only [slope] using hlower none
  have hvertex (i : I) : vertex i ∈ K := subset_convexHull ℝ _ (mem_range_self i)
  have hnegative (j : I) (hj : cost (vertex j) < budget) :
      lambda ≤ (reward x - reward (vertex j)) / (budget - cost (vertex j)) := by
    have hjd : 0 < budget - cost (vertex j) := sub_pos.mpr hj
    have hjr : reward (vertex j) ≤ reward x := hmax ⟨hvertex j, hj.le⟩
    have hz : 0 ≤ (reward x - reward (vertex j)) / (budget - cost (vertex j)) :=
      div_nonneg (sub_nonneg.mpr hjr) hjd.le
    apply Finset.sup'_le Finset.univ_nonempty
    intro z _
    cases z with
    | none => exact hz
    | some i =>
      dsimp only [slope]
      by_cases hi : budget < cost (vertex i)
      · rw [if_pos hi]
        have hid : 0 < cost (vertex i) - budget := sub_pos.mpr hi
        have hdiff : 0 < cost (vertex i) - cost (vertex j) := by linarith
        let u := (budget - cost (vertex j)) / (cost (vertex i) - cost (vertex j))
        let v := (cost (vertex i) - budget) / (cost (vertex i) - cost (vertex j))
        have hu : 0 ≤ u := div_nonneg hjd.le hdiff.le
        have hv : 0 ≤ v := div_nonneg hid.le hdiff.le
        have huv : u + v = 1 := by
          dsimp only [u,v]
          field_simp [ne_of_gt hdiff]
          <;> ring
        have hm : u • vertex i + v • vertex j ∈ K :=
          hconv (hvertex i) (hvertex j) hu hv huv
        have hcost : cost (u • vertex i + v • vertex j) = budget := by
          simp only [map_add, map_smul, smul_eq_mul]
          dsimp only [u,v]
          field_simp [ne_of_gt hdiff]
          <;> ring
        have hrmix : reward (u • vertex i + v • vertex j) ≤ reward x := hmax ⟨hm, hcost.le⟩
        have hre : reward (u • vertex i + v • vertex j) =
            ((budget - cost (vertex j)) * reward (vertex i) +
              (cost (vertex i) - budget) * reward (vertex j)) /
                (cost (vertex i) - cost (vertex j)) := by
          simp only [map_add, map_smul, smul_eq_mul]
          dsimp only [u,v]
          ring
        rw [hre] at hrmix
        have hnum := (div_le_iff₀ hdiff).mp hrmix
        apply (div_le_div_iff₀ hid hjd).mpr
        nlinarith
      · rw [if_neg hi]
        exact hz
  have hvertices (i : I) :
      reward (vertex i) - lambda * (cost (vertex i) - budget) ≤ reward x := by
    rcases lt_trichotomy (cost (vertex i)) budget with hi | hi | hi
    · have h := (le_div_iff₀ (sub_pos.mpr hi)).mp (hnegative i hi)
      nlinarith
    · rw [hi, sub_self, mul_zero, sub_zero]
      exact hmax ⟨hvertex i, hi.le⟩
    · have h := hlower (some i)
      dsimp only [slope] at h
      rw [if_pos hi] at h
      have h := (div_le_iff₀ (sub_pos.mpr hi)).mp h
      linarith
  have hhalf : Convex ℝ {y : E | reward y - lambda * cost y ≤ reward x - lambda * budget} := by
    intro y hy z hz u v hu hv huv
    simp only [mem_setOf_eq, map_add, map_smul, smul_eq_mul] at *
    calc
      u * reward y + v * reward z - lambda * (u * cost y + v * cost z) =
          u * (reward y - lambda * cost y) + v * (reward z - lambda * cost z) := by ring
      _ ≤ u * (reward x - lambda * budget) + v * (reward x - lambda * budget) :=
          add_le_add (mul_le_mul_of_nonneg_left hy hu) (mul_le_mul_of_nonneg_left hz hv)
      _ = reward x - lambda * budget := by rw [←add_mul,huv,one_mul]
  have hhull : K ⊆ {y : E | reward y - lambda * cost y ≤ reward x - lambda * budget} :=
    convexHull_min (by rintro _ ⟨i,rfl⟩; change reward (vertex i) - lambda * cost (vertex i) ≤ reward x - lambda * budget; nlinarith [hvertices i]) hhalf
  have hall (y : E) (hy : y ∈ K) :
      reward y - lambda * (cost y - budget) ≤ reward x := by
    have h := hhull hy
    change reward y - lambda * cost y ≤ reward x - lambda * budget at h
    nlinarith
  refine ⟨x, lambda, hx.1, hx.2, hl0, ?_, hall⟩
  have h := hall x hx.1
  have hn := mul_nonpos_of_nonneg_of_nonpos hl0 (sub_nonpos.mpr hx.2)
  linarith

open SafeLearning.CompleteFiniteCMDPOccupancy
  SafeLearning.CompleteFiniteCMDPFlow
  SafeLearning.CompleteFiniteCMDPLinearProgram
  SafeLearning.CompleteFiniteCMDPDeterministicVertices
  SafeLearning.CompleteFiniteCMDPVertexClassification

/-- The actual finite-CMDP feasible-flow set is the convex hull of finitely many actual
stationary deterministic occupancies, not an assumed polytope representation. -/
theorem actual_finite_CMDP_flow_set_is_generated_by_its_finite_deterministic_policies
    {S A : Type*} [Fintype S] [Fintype A]
    (M : Model S A) (gamma : ℝ) (hg0 : 0 ≤ gamma) (hg1 : gamma < 1) :
    {rho | FlowFeasible M gamma rho} =
      convexHull ℝ (range (fun d : S → A => occupancy M (purePolicy d) gamma)) := by
  classical
  have he : extremePoints ℝ {rho | FlowFeasible M gamma rho} =
      range (fun d : S → A => occupancy M (purePolicy d) gamma) := by
    ext rho
    constructor
    · intro h
      obtain ⟨d, rfl⟩ := (actual_flow_extreme_point_iff_deterministic_stationary_occupancy M gamma hg0 hg1 rho).mp h
      exact mem_range_self d
    · rintro ⟨d, rfl⟩
      exact actual_pure_policy_occupancy_is_extreme_point M d gamma hg0 hg1
  have h := closure_convexHull_extremePoints
    (actual_flow_polyhedron_compact M gamma hg1)
    (actual_nonnegative_flow_polyhedron_is_convex M gamma)
  have hclosed := (Set.finite_range (fun d : S → A => occupancy M (purePolicy d) gamma)).isClosed_convexHull ℝ
  rw [he, hclosed.closure_eq] at h
  exact h.symm

end SafeLearning.CompleteModulesFinitePolytopeDuality30


namespace SafeLearning.CompleteModulesFinitePolytopeDuality30
open SafeLearning.CompleteFiniteCMDPOccupancy SafeLearning.CompleteFiniteCMDPFlow
  SafeLearning.CompleteFiniteCMDPLinearProgram SafeLearning.CompleteFiniteCMDPRecovery
  SafeLearning.CompleteFiniteCMDPDeterministicVertices

/-- Actual feasible finite discounted CMDPs have a stationary randomized saddle policy
and a nonnegative scalar multiplier even without a strictly feasible policy. -/
theorem actual_feasible_finite_CMDP_has_a_stationary_policy_and_multiplier
    {S A : Type*} [Fintype S] [Fintype A]
    (M : Model S A) (a₀ : A) (gamma : ℝ) (hg0 : 0 ≤ gamma) (hg1 : gamma < 1)
    (reward cost : S → A → ℝ) (budget : ℝ)
    (hne : ∃ policy : Policy S A, expectedReturn M policy gamma cost ≤ budget) :
    ∃ (policy : Policy S A) (lambda : ℝ),
      (∀ n s a, policy.action n s a = policy.action 0 s a) ∧
      0 ≤ lambda ∧ expectedReturn M policy gamma cost ≤ budget ∧
      lambda * (expectedReturn M policy gamma cost - budget) = 0 ∧
      ∀ other : Policy S A,
        expectedReturn M other gamma reward -
          lambda * (expectedReturn M other gamma cost - budget) ≤
            expectedReturn M policy gamma reward := by
  classical
  let vertex := fun d : S → A => occupancy M (purePolicy d) gamma
  have hpoly := actual_finite_CMDP_flow_set_is_generated_by_its_finite_deterministic_policies
    M gamma hg0 hg1
  have hp : 0 < 1 - gamma := sub_pos.mpr hg1
  have hscale (policy : Policy S A) (r : S → A → ℝ) :
      rewardFunctional r (occupancy M policy gamma) =
        (1 - gamma) * expectedReturn M policy gamma r := by
    rw [actual_reward_return_identity M policy gamma hg0 hg1]
    change (∑ s, ∑ a, occupancy M policy gamma s a * r s a) =
      (1 - gamma) * ((∑ s, ∑ a, occupancy M policy gamma s a * r s a) / (1 - gamma))
    exact (mul_div_cancel₀ _ (ne_of_gt hp)).symm
  have hne' : ∃ rho ∈ convexHull ℝ (range vertex),
      rewardFunctional cost rho ≤ (1 - gamma) * budget := by
    obtain ⟨policy,hpolicy⟩ := hne
    refine ⟨occupancy M policy gamma, ?_, ?_⟩
    · rw [←hpoly]
      exact actual_occupancy_satisfies_flow M policy gamma hg0 hg1
    · rw [hscale]
      exact mul_le_mul_of_nonneg_left hpolicy hp.le
  obtain ⟨rho,lambda,hrho,hcost,hl0,hcomplement,hall⟩ :=
    actual_feasible_finite_polytope_has_a_single_constraint_saddle vertex
      (rewardFunctional reward) (rewardFunctional cost) ((1 - gamma) * budget)
      (actual_reward_functional_continuous reward) (actual_reward_functional_continuous cost) hne'
  have hflow : FlowFeasible M gamma rho := by
    rw [←hpoly] at hrho
    exact hrho
  let policy := recoveredPolicy a₀ rho hflow.1
  have he : occupancy M policy gamma = rho :=
    actual_every_feasible_flow_is_realized_by_recovered_stationary_policy
      M a₀ gamma hg0 hg1 rho hflow
  have hrepr (r : S → A → ℝ) : rewardFunctional r rho =
      (1 - gamma) * expectedReturn M policy gamma r := by rw [←he,hscale]
  have hfeasible : expectedReturn M policy gamma cost ≤ budget := by
    rw [hrepr] at hcost
    exact (mul_le_mul_iff_of_pos_left hp).mp hcost
  refine ⟨policy,lambda,(fun _ _ _ => rfl),hl0,hfeasible,?_,?_⟩
  · rw [hrepr] at hcomplement
    have hf : (1 - gamma) * (lambda * (expectedReturn M policy gamma cost - budget)) = 0 := by
      nlinarith [hcomplement]
    exact (mul_eq_zero.mp hf).resolve_left (ne_of_gt hp)
  · intro other
    have hother : occupancy M other gamma ∈ convexHull ℝ (range vertex) := by
      rw [←hpoly]
      exact actual_occupancy_satisfies_flow M other gamma hg0 hg1
    have h := hall (occupancy M other gamma) hother
    rw [hscale,hscale,hrepr] at h
    apply (mul_le_mul_iff_of_pos_left hp).mp
    nlinarith [h]

end SafeLearning.CompleteModulesFinitePolytopeDuality30


namespace SafeLearning.CompleteModulesFinitePolytopeDuality30
open SafeLearning.CompleteFiniteCMDPOccupancy SafeLearning.CompleteFiniteCMDPFlow
  SafeLearning.CompleteFiniteCMDPLinearProgram SafeLearning.CompleteFiniteCMDPRecovery
  SafeLearning.CompleteFiniteCMDPDeterministicVertices

def actualFinitePrimalValue {S A : Type*} [Fintype S] [Fintype A]
    (M : Model S A) (gamma : ℝ) (reward cost : S → A → ℝ) (budget : ℝ) : ℝ :=
  sSup {value | ∃ policy : Policy S A,
    expectedReturn M policy gamma cost ≤ budget ∧ value = expectedReturn M policy gamma reward}

def actualFiniteDualValue {S A : Type*} [Fintype S] [Fintype A]
    (M : Model S A) (gamma : ℝ) (reward cost : S → A → ℝ) (budget lambda : ℝ) : ℝ :=
  sSup {value | ∃ policy : Policy S A, value = expectedReturn M policy gamma reward -
    lambda * (expectedReturn M policy gamma cost - budget)}

/-- Each actual finite-model dual supremum is bounded through its compact flow set. -/
theorem actual_finite_CMDP_Lagrangian_values_are_bounded_above
    {S A : Type*} [Fintype S] [Fintype A]
    (M : Model S A) (gamma : ℝ) (hg0 : 0 ≤ gamma) (hg1 : gamma < 1)
    (reward cost : S → A → ℝ) (budget lambda : ℝ) :
    BddAbove {value | ∃ policy : Policy S A, value = expectedReturn M policy gamma reward -
      lambda * (expectedReturn M policy gamma cost - budget)} := by
  let f : (S → A → ℝ) → ℝ := fun rho =>
    rewardFunctional reward rho / (1 - gamma) -
      lambda * (rewardFunctional cost rho / (1 - gamma) - budget)
  have hf : Continuous f :=
    ((actual_reward_functional_continuous reward).div_const _).sub
      (continuous_const.mul (((actual_reward_functional_continuous cost).div_const _).sub continuous_const))
  obtain ⟨bound,hbound⟩ := (actual_flow_polyhedron_compact M gamma hg1).bddAbove_image hf.continuousOn
  refine ⟨bound, ?_⟩
  rintro value ⟨policy,rfl⟩
  apply hbound
  refine ⟨occupancy M policy gamma, actual_occupancy_satisfies_flow M policy gamma hg0 hg1, ?_⟩
  dsimp only [f]
  simp only [actual_reward_return_identity M policy gamma hg0 hg1,
    rewardFunctional, LinearMap.coe_mk, AddHom.coe_mk]

/-- Genuine primal and dual optimum values coincide and the dual infimum is attained,
with feasibility alone in the actual single-cost finite discounted model. -/
theorem actual_feasible_finite_CMDP_has_attained_strong_duality_without_Slater
    {S A : Type*} [Fintype S] [Fintype A]
    (M : Model S A) (a₀ : A) (gamma : ℝ) (hg0 : 0 ≤ gamma) (hg1 : gamma < 1)
    (reward cost : S → A → ℝ) (budget : ℝ)
    (hne : ∃ policy : Policy S A, expectedReturn M policy gamma cost ≤ budget) :
    ∃ (policy : Policy S A) (lambda : ℝ),
      (∀ n s a, policy.action n s a = policy.action 0 s a) ∧
      0 ≤ lambda ∧ expectedReturn M policy gamma cost ≤ budget ∧
      actualFinitePrimalValue M gamma reward cost budget = expectedReturn M policy gamma reward ∧
      actualFiniteDualValue M gamma reward cost budget lambda =
        actualFinitePrimalValue M gamma reward cost budget ∧
      sInf (actualFiniteDualValue M gamma reward cost budget '' Ici 0) =
        actualFinitePrimalValue M gamma reward cost budget := by
  obtain ⟨policy,lambda,hstat,hl0,hfeasible,hcomp,hall⟩ :=
    actual_feasible_finite_CMDP_has_a_stationary_policy_and_multiplier M a₀ gamma hg0 hg1
      reward cost budget hne
  have hlag : expectedReturn M policy gamma reward -
      lambda * (expectedReturn M policy gamma cost - budget) = expectedReturn M policy gamma reward := by rw [hcomp,sub_zero]
  have hprimal : IsGreatest {value | ∃ other : Policy S A,
      expectedReturn M other gamma cost ≤ budget ∧ value = expectedReturn M other gamma reward}
      (expectedReturn M policy gamma reward) := by
    refine ⟨⟨policy,hfeasible,rfl⟩, ?_⟩
    rintro value ⟨other,hother,rfl⟩
    have h := hall other
    have hn := mul_nonpos_of_nonneg_of_nonpos hl0 (sub_nonpos.mpr hother)
    linarith
  have hp : actualFinitePrimalValue M gamma reward cost budget = expectedReturn M policy gamma reward := hprimal.csSup_eq
  have hdual : IsGreatest {value | ∃ other : Policy S A, value = expectedReturn M other gamma reward -
      lambda * (expectedReturn M other gamma cost - budget)} (expectedReturn M policy gamma reward) := by
    refine ⟨⟨policy,hlag.symm⟩, ?_⟩
    rintro value ⟨other,rfl⟩
    exact hall other
  have hd : actualFiniteDualValue M gamma reward cost budget lambda = expectedReturn M policy gamma reward := hdual.csSup_eq
  have hweak (otherLambda : ℝ) (hm : 0 ≤ otherLambda) :
      expectedReturn M policy gamma reward ≤ actualFiniteDualValue M gamma reward cost budget otherLambda := by
    have hmem : expectedReturn M policy gamma reward - otherLambda *
        (expectedReturn M policy gamma cost - budget) ∈
        {value | ∃ other : Policy S A, value = expectedReturn M other gamma reward -
          otherLambda * (expectedReturn M other gamma cost - budget)} := ⟨policy,rfl⟩
    have hupper := le_csSup
      (actual_finite_CMDP_Lagrangian_values_are_bounded_above M gamma hg0 hg1 reward cost budget otherLambda) hmem
    have hn := mul_nonpos_of_nonneg_of_nonpos hm (sub_nonpos.mpr hfeasible)
    exact (by linarith : expectedReturn M policy gamma reward ≤
      expectedReturn M policy gamma reward - otherLambda * (expectedReturn M policy gamma cost - budget)).trans hupper
  have hleast : IsLeast (actualFiniteDualValue M gamma reward cost budget '' Ici 0)
      (expectedReturn M policy gamma reward) := by
    refine ⟨⟨lambda,hl0,hd⟩, ?_⟩
    rintro value ⟨otherLambda,hm,rfl⟩
    exact hweak otherLambda hm
  exact ⟨policy,lambda,hstat,hl0,hfeasible,hp,hd.trans hp.symm,hleast.csInf_eq.trans hp.symm⟩

end SafeLearning.CompleteModulesFinitePolytopeDuality30
