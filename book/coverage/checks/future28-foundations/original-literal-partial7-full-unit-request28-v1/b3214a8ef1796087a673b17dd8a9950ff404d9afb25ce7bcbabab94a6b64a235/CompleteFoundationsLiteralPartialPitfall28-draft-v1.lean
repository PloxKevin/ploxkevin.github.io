import SafeLearning.CompleteFoundationsSpectralModels
import Mathlib.Analysis.Calculus.Gradient.Basic

set_option autoImplicit false
noncomputable section
open Set
open scoped Topology

namespace SafeLearning.CompleteFoundationsLiteralPartialPitfall28
open SafeLearning.CompleteFoundationsSpectralModels (E point norm_squared_coordinates)

/-- The exact printed counterexample; Lean's real division also gives zero at
the origin, so no alternative off-origin model or completion is substituted. -/
def literalPitfall (x : E) : ℝ := x 0 * x 1 / ((x 0)^2+(x 1)^2)

theorem actual_literal_pitfall_origin_and_axis_restrictions_are_zero :
    literalPitfall 0 = 0 ∧
    (∀ t : ℝ, literalPitfall (point t 0) = 0) ∧
    (∀ t : ℝ, literalPitfall (point 0 t) = 0) := by
  simp [literalPitfall, point]

theorem actual_literal_pitfall_has_both_zero_coordinate_partials :
    HasDerivAt (fun t => literalPitfall (point t 0)) 0 0 ∧
    HasDerivAt (fun t => literalPitfall (point 0 t)) 0 0 := by
  have hx : (fun t => literalPitfall (point t 0)) = (fun _ : ℝ => (0 : ℝ)) := by
    funext t
    exact actual_literal_pitfall_origin_and_axis_restrictions_are_zero.2.1 t
  have hy : (fun t => literalPitfall (point 0 t)) = (fun _ : ℝ => (0 : ℝ)) := by
    funext t
    exact actual_literal_pitfall_origin_and_axis_restrictions_are_zero.2.2 t
  rw [hx,hy]
  exact ⟨hasDerivAt_const 0 0,hasDerivAt_const 0 0⟩

theorem actual_literal_pitfall_is_one_half_everywhere_on_the_nonzero_diagonal
    (t : ℝ) (ht : t ≠ 0) : literalPitfall (point t t) = 1/2 := by
  have hs : t^2 ≠ 0 := pow_ne_zero 2 ht
  have hd : t^2+t^2 ≠ 0 := by nlinarith [sq_pos_of_ne_zero ht]
  simp only [literalPitfall,point,WithLp.toLp_apply,Matrix.cons_val_zero,Matrix.cons_val_one]
  field_simp
  ring

theorem actual_literal_pitfall_is_not_continuous_at_the_origin :
    ¬ ContinuousAt literalPitfall (0 : E) := by
  intro h
  obtain ⟨δ,hδ,hclose⟩ := Metric.continuousAt_iff.mp h (1/4) (by norm_num)
  let t : ℝ := δ/4
  have ht : 0 < t := by dsimp [t];positivity
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hn : ‖point t t‖^2 = 2*t^2 := by
    rw [norm_squared_coordinates]
    simp [point]
    ring
  have hsmall : ‖point t t‖ < δ := by
    have := norm_nonneg (point t t)
    dsimp [t] at hn
    nlinarith
  have h := hclose (x:=point t t) (by simpa [dist_zero_right] using hsmall)
  rw [actual_literal_pitfall_is_one_half_everywhere_on_the_nonzero_diagonal t ht0,
    actual_literal_pitfall_origin_and_axis_restrictions_are_zero.1] at h
  norm_num [Real.dist_eq] at h

theorem actual_literal_zero_partials_do_not_give_differentiability_or_C1 :
    ¬ DifferentiableAt ℝ literalPitfall (0 : E) ∧
    ¬ ContDiffAt ℝ 1 literalPitfall (0 : E) := by
  constructor
  · intro h
    exact actual_literal_pitfall_is_not_continuous_at_the_origin h.continuousAt
  · intro h
    exact actual_literal_pitfall_is_not_continuous_at_the_origin h.continuousAt

/-- The source convention for C1 on a closed set is an open-neighborhood
extension. It does not assert differentiability of an arbitrary ambient
completion agreeing only on the closed set, or uniqueness of a chosen
extension's gradient on a thin set. -/
structure C1ExtensionOn (f : E → ℝ) (S : Set E) where
  extension : E → ℝ
  neighborhood : Set E
  open_neighborhood : IsOpen neighborhood
  contains : S ⊆ neighborhood
  regular : ContDiffOn ℝ 1 extension neighborhood
  agrees : EqOn extension f S

theorem actual_open_C1_extension_supplies_gradients_at_every_closed_set_point
    (f : E → ℝ) (S : Set E) (extension : C1ExtensionOn f S) :
    EqOn extension.extension f S ∧
    ∀ x ∈ S, HasGradientAt extension.extension (gradient extension.extension x) x := by
  refine ⟨extension.agrees,?_⟩
  intro x hx
  have hc : ContDiffAt ℝ 1 extension.extension x :=
    extension.regular.contDiffAt
      (extension.open_neighborhood.mem_nhds (extension.contains hx))
  exact (hc.differentiableAt (by norm_num)).hasGradientAt

theorem actual_closed_set_C1_extension_includes_every_boundary_point
    (f : E → ℝ) (S : Set E) (hclosed : IsClosed S)
    (extension : C1ExtensionOn f S) :
    ∀ x ∈ frontier S,
      extension.extension x = f x ∧
      HasGradientAt extension.extension (gradient extension.extension x) x := by
  intro x hx
  have hxS : x ∈ S := by
    have := frontier_subset_closure hx
    simpa [hclosed.closure_eq] using this
  exact ⟨extension.agrees hxS,
    (actual_open_C1_extension_supplies_gradients_at_every_closed_set_point f S extension).2 x hxS⟩

end SafeLearning.CompleteFoundationsLiteralPartialPitfall28
