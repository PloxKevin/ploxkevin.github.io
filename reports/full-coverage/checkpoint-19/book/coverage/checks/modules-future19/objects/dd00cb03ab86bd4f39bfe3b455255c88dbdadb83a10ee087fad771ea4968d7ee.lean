import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Metric
open scoped Topology

namespace SafeLearning.CompleteModulesLandscapeHalfspaceQP

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]

/-- The actual minimum-change controller for one nondegenerate affine
constraint. The denominator is an ordinary positive squared norm. -/
def controller (q nominal : U) (b : ℝ) : U :=
  nominal + (max 0 (b - inner ℝ q nominal) / ‖q‖ ^ 2) • q

theorem actual_single_halfspace_QP_controller_satisfies_the_constraint
    (q nominal : U) (b : ℝ) (hq : q ≠ 0) :
    b ≤ inner ℝ q (controller q nominal b) := by
  have hn : ‖q‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hq)
  rw [controller, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]
  rw [div_mul_cancel₀ _ hn]
  have hm := le_max_right 0 (b - inner ℝ q nominal)
  linarith

/-- The squared-distance objective obeys a genuine strong minimum
inequality against every feasible input. -/
theorem actual_single_halfspace_QP_controller_has_the_strong_squared_distance_minimum
    (q nominal v : U) (b : ℝ) (hq : q ≠ 0) (hv : b ≤ inner ℝ q v) :
    ‖controller q nominal b - nominal‖ ^ 2 + ‖v - controller q nominal b‖ ^ 2 ≤
      ‖v - nominal‖ ^ 2 := by
  by_cases hinactive : b ≤ inner ℝ q nominal
  · have hc : controller q nominal b = nominal := by
      simp only [controller, max_eq_left (sub_nonpos.mpr hinactive), zero_div, zero_smul, add_zero]
    simp only [hc, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add, le_refl]
  · have hb : inner ℝ q nominal < b := lt_of_not_ge hinactive
    have hs : 0 ≤ b - inner ℝ q nominal := sub_nonneg.mpr hb.le
    have hn : 0 < ‖q‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hq)
    have hc : controller q nominal b - nominal =
        ((b - inner ℝ q nominal) / ‖q‖ ^ 2) • q := by
      simp only [controller, max_eq_right hs, add_sub_cancel_left]
    have hboundary : inner ℝ q (controller q nominal b) = b := by
      rw [controller, max_eq_right hs, inner_add_right, inner_smul_right,
        real_inner_self_eq_norm_sq, div_mul_cancel₀ _ hn.ne']
      ring
    have hinner : 0 ≤ inner ℝ (v - controller q nominal b) (controller q nominal b - nominal) := by
      rw [hc, inner_smul_right, real_inner_comm q (v - controller q nominal b),
        inner_sub_right, hboundary]
      exact mul_nonneg (div_nonneg hs hn.le) (sub_nonneg.mpr hv)
    have hsum : v - nominal = (v - controller q nominal b) + (controller q nominal b - nominal) := by
      abel
    rw [hsum, norm_add_sq_real]
    linarith

theorem actual_single_halfspace_QP_controller_is_the_unique_squared_distance_minimizer
    (q nominal : U) (b : ℝ) (hq : q ≠ 0) :
    (b ≤ inner ℝ q (controller q nominal b)) ∧
      ∀ v : U, b ≤ inner ℝ q v →
        (‖v - nominal‖ ^ 2 ≤ ‖controller q nominal b - nominal‖ ^ 2 ↔
          v = controller q nominal b) := by
  refine ⟨actual_single_halfspace_QP_controller_satisfies_the_constraint q nominal b hq, ?_⟩
  intro v hv
  constructor
  · intro hm
    have hs := actual_single_halfspace_QP_controller_has_the_strong_squared_distance_minimum
      q nominal v b hq hv
    have hzero : ‖v - controller q nominal b‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖v - controller q nominal b‖]
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hzero))
  · rintro rfl
    exact le_rfl

/-- Pointwise nonzero denominators and actual locally Lipschitz data give a
locally Lipschitz reciprocal; no uniform global lower bound is required. -/
private theorem reciprocal_locally_lipschitz
    {X : Type*} [PseudoMetricSpace X] (f : X → ℝ)
    (hf : LocallyLipschitz f) (hne : ∀ x, f x ≠ 0) :
    LocallyLipschitz (fun x => (f x)⁻¹) := by
  intro x
  obtain ⟨K, t, ht, hK⟩ := hf x
  have hdiff : ContDiffAt ℝ 1 (fun r : ℝ => r⁻¹) (f x) :=
    contDiffAt_id.inv (hne x)
  obtain ⟨L, s, hs, hL⟩ := hdiff.exists_lipschitzOnWith
  refine ⟨L * K, t ∩ f ⁻¹' s, inter_mem ht (hf.continuous.continuousAt hs), ?_⟩
  exact hL.comp (hK.mono inter_subset_left)
    ((mapsTo_preimage f s).mono_left inter_subset_right)

/-- Concrete sufficient regularity conditions for the actual QP optimizer:
locally Lipschitz nominal/coefficient/offset maps, and a nonzero coefficient
at every state in D. Constraint switching through max is allowed. -/
theorem actual_single_halfspace_QP_optimizer_is_locally_lipschitz_under_nonzero_coefficient_regularity
    {X : Type*} [PseudoMetricSpace X] (D : Set X)
    (q nominal : X → U) (b : X → ℝ)
    (hq : LocallyLipschitzOn D q) (hn : LocallyLipschitzOn D nominal)
    (hb : LocallyLipschitzOn D b) (hnz : ∀ x ∈ D, q x ≠ 0) :
    LocallyLipschitzOn D (fun x => controller (q x) (nominal x) (b x)) := by
  apply locallyLipschitzOn_iff_restrict.mpr
  have hi : LocallyLipschitz (fun p : U × U => inner ℝ p.1 p.2) :=
    (contDiff_inner : ContDiff ℝ 1 (fun p : U × U => inner ℝ p.1 p.2)).locallyLipschitz
  have hqn : LocallyLipschitz (fun x : D => inner ℝ (q x) (nominal x)) :=
    hi.comp (hq.restrict.prodMk hn.restrict)
  have hqq : LocallyLipschitz (fun x : D => inner ℝ (q x) (q x)) :=
    hi.comp (hq.restrict.prodMk hq.restrict)
  have hinv : LocallyLipschitz (fun x : D => (inner ℝ (q x) (q x))⁻¹) :=
    reciprocal_locally_lipschitz _ hqq (fun x => by
      rw [real_inner_self_eq_norm_sq]
      exact pow_ne_zero _ (norm_ne_zero_iff.mpr (hnz x x.property)))
  have hnum : LocallyLipschitz (fun x : D => max 0 (b x - inner ℝ (q x) (nominal x))) :=
    (hb.restrict.sub hqn).const_max 0
  have hmul : LocallyLipschitz (fun p : ℝ × ℝ => p.1 * p.2) :=
    (contDiff_fst.mul contDiff_snd : ContDiff ℝ 1 (fun p : ℝ × ℝ => p.1 * p.2)).locallyLipschitz
  have hfactor : LocallyLipschitz (fun x : D =>
      max 0 (b x - inner ℝ (q x) (nominal x)) * (inner ℝ (q x) (q x))⁻¹) :=
    hmul.comp (hnum.prodMk hinv)
  have hsmul : LocallyLipschitz (fun p : ℝ × U => p.1 • p.2) :=
    (contDiff_fst.smul contDiff_snd : ContDiff ℝ 1 (fun p : ℝ × U => p.1 • p.2)).locallyLipschitz
  have hout := hn.restrict.add (hsmul.comp (hfactor.prodMk hq.restrict))
  simpa only [Set.domRestrict_apply, Function.comp_apply, controller,
    real_inner_self_eq_norm_sq, div_eq_mul_inv] using hout

end SafeLearning.CompleteModulesLandscapeHalfspaceQP
