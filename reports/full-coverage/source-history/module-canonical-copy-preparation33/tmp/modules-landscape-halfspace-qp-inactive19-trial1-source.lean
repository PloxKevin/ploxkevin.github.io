import SafeLearning.CompleteModulesLandscapeHalfspaceQP

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Metric
open scoped Topology

namespace SafeLearning.CompleteModulesLandscapeHalfspaceQPInactive

open CompleteModulesLandscapeHalfspaceQP
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]

theorem actual_inactive_halfspace_QP_returns_the_nominal_input
    (q nominal : U) (b : ℝ) (hb : b ≤ inner ℝ q nominal) :
    controller q nominal b = nominal := by
  simp only [controller, max_eq_left (sub_nonpos.mpr hb), zero_div, zero_smul, add_zero]

/-- Zero coefficients are permitted when the constraint is actually feasible.
No nonzero coefficient is demanded at interior critical points of a barrier. -/
theorem actual_halfspace_QP_is_feasible_and_unique_when_nondegenerate_or_nominally_feasible
    (q nominal : U) (b : ℝ) (hregular : q ≠ 0 ∨ b ≤ inner ℝ q nominal) :
    (b ≤ inner ℝ q (controller q nominal b)) ∧
      ∀ v : U, b ≤ inner ℝ q v →
        (‖v - nominal‖ ^ 2 ≤ ‖controller q nominal b - nominal‖ ^ 2 ↔
          v = controller q nominal b) := by
  rcases hregular with hq | hb
  · exact actual_single_halfspace_QP_controller_is_the_unique_squared_distance_minimizer q nominal b hq
  · rw [actual_inactive_halfspace_QP_returns_the_nominal_input q nominal b hb]
    refine ⟨hb, fun v _ => ?_⟩
    simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    constructor
    · intro hnorm
      have hzero : ‖v - nominal‖ ^ 2 = 0 := le_antisymm hnorm (sq_nonneg _)
      exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hzero))
    · rintro rfl
      simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), le_refl]

/-- A genuine statewise regularity condition: nonzero coefficient, or a
strictly inactive constraint. The latter allows zeros of the coefficient and
does not demand a nonexistent nonzero barrier gradient at compact maxima. -/
theorem actual_halfspace_QP_is_locally_lipschitz_with_nondegenerate_or_strictly_inactive_constraints
    {X : Type*} [PseudoMetricSpace X] (D : Set X)
    (q nominal : X → U) (b : X → ℝ)
    (hq : LocallyLipschitzOn D q) (hn : LocallyLipschitzOn D nominal)
    (hb : LocallyLipschitzOn D b)
    (hregular : ∀ x ∈ D, q x ≠ 0 ∨ b x < inner ℝ (q x) (nominal x)) :
    LocallyLipschitzOn D (fun x => controller (q x) (nominal x) (b x)) := by
  apply locallyLipschitzOn_iff_restrict.mpr
  change LocallyLipschitz (fun x : D => controller (q x) (nominal x) (b x))
  have hinner : Continuous (fun x : D => inner ℝ (q x) (nominal x)) :=
    (hq.restrict.continuous.inner hn.restrict.continuous)
  intro x
  rcases hregular x x.property with hxq | hxinactive
  · let S : Set D := {z | q z ≠ 0}
    have hS : IsOpen S := isOpen_ne hq.restrict.continuous continuous_const
    have hfull : LocallyLipschitzOn S (fun z : D => controller (q z) (nominal z) (b z)) :=
      actual_single_halfspace_QP_optimizer_is_locally_lipschitz_under_nonzero_coefficient_regularity
        S _ _ _ hq.restrict.locallyLipschitzOn hn.restrict.locallyLipschitzOn
        hb.restrict.locallyLipschitzOn (fun _ hz => hz)
    obtain ⟨K,t,ht,hK⟩ := hfull hxq
    rw [nhdsWithin_eq_nhds.mpr (hS.mem_nhds hxq)] at ht
    exact ⟨K,t,ht,hK⟩
  · let S : Set D := {z | b z - inner ℝ (q z) (nominal z) < 0}
    have hS : S ∈ 𝓝 x :=
      (hb.restrict.continuous.sub hinner).continuousAt.preimage_mem_nhds
        (Iio_mem_nhds (sub_neg.mpr hxinactive))
    have heq : ∀ z ∈ S, controller (q z) (nominal z) (b z) = nominal z := by
      intro z hz
      exact actual_inactive_halfspace_QP_returns_the_nominal_input _ _ _ (sub_nonpos.mp hz.le)
    obtain ⟨K,t,ht,hK⟩ := hn.restrict x
    refine ⟨K,t ∩ S, inter_mem ht hS, ?_⟩
    apply LipschitzOnWith.of_dist_le_mul
    intro y hy z hz
    rw [heq y hy.2,heq z hz.2]
    exact hK.dist_le_mul y hy.1 z hz.1

end SafeLearning.CompleteModulesLandscapeHalfspaceQPInactive
