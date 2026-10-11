import Mathlib

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace SafeLearning.CompleteFoundationsContinuousLevels22

variable {X : Type*} [TopologicalSpace X]

theorem actual_continuous_nonnegative_nonpositive_and_zero_levels_are_closed
    (quantity : X → ℝ) (hcontinuous : Continuous quantity) :
    IsClosed {point | 0 ≤ quantity point} ∧ IsClosed {point | quantity point ≤ 0} ∧
      IsClosed {point | quantity point=0} :=
  ⟨isClosed_le continuous_const hcontinuous,isClosed_le hcontinuous continuous_const,
    isClosed_eq hcontinuous continuous_const⟩

theorem actual_positive_level_is_open_and_is_the_complement_of_the_nonpositive_level
    (quantity : X → ℝ) (hcontinuous : Continuous quantity) :
    IsOpen {point | 0 < quantity point} ∧
      {point | 0 < quantity point}={point | quantity point ≤ 0}ᶜ := by
  refine ⟨isOpen_lt continuous_const hcontinuous,?_⟩
  ext point
  simp

theorem actual_positive_level_is_contained_in_the_superlevel_interior
    (quantity : X → ℝ) (hcontinuous : Continuous quantity) :
    {point | 0 < quantity point} ⊆ interior {point | 0 ≤ quantity point} := by
  exact (isOpen_lt continuous_const hcontinuous).subset_interior_iff.mpr
    (fun point hp => hp.le)

theorem actual_superlevel_frontier_is_the_closed_set_minus_interior_and_has_only_zeros
    (quantity : X → ℝ) (hcontinuous : Continuous quantity) :
    frontier {point | 0 ≤ quantity point}=
      {point | 0 ≤ quantity point}\interior {point | 0 ≤ quantity point} ∧
      frontier {point | 0 ≤ quantity point} ⊆ {point | quantity point=0} := by
  have hc : IsClosed {point | 0 ≤ quantity point} := isClosed_le continuous_const hcontinuous
  refine ⟨hc.frontier_eq,?_⟩
  intro point hp
  have hn : 0 ≤ quantity point := hc.frontier_subset hp
  have hnot : point ∉ interior {point | 0 ≤ quantity point} := by
    rw [hc.frontier_eq] at hp
    exact hp.2
  apply le_antisymm ?_ hn
  by_contra hpositive
  exact hnot (actual_positive_level_is_contained_in_the_superlevel_interior
    quantity hcontinuous (lt_of_not_ge hpositive))

theorem actual_sequential_nonnegative_nonpositive_and_zero_proof_routes
    (quantity : X → ℝ) (hcontinuous : Continuous quantity) (points : ℕ → X) (point : X)
    (hlimit : Tendsto points atTop (𝓝 point)) :
    Tendsto (fun n => quantity (points n)) atTop (𝓝 (quantity point)) ∧
      ((∀ n,0 ≤ quantity (points n)) → 0 ≤ quantity point) ∧
      ((∀ n,quantity (points n) ≤ 0) → quantity point ≤ 0) ∧
      ((∀ n,quantity (points n)=0) → quantity point=0) := by
  have hq := (hcontinuous.tendsto point).comp hlimit
  refine ⟨hq,?_,?_,?_⟩
  · intro hn
    exact ge_of_tendsto hq (Eventually.of_forall hn)
  · intro hn
    exact le_of_tendsto hq (Eventually.of_forall hn)
  · intro hz
    have hnon := ge_of_tendsto hq (Eventually.of_forall (fun n => (hz n).ge))
    have hpos := le_of_tendsto hq (Eventually.of_forall (fun n => (hz n).le))
    exact le_antisymm hpos hnon

theorem actual_continuity_upgrades_an_almost_everywhere_nonnegative_bound_on_full_support
    [MeasurableSpace X] (measure : Measure X) (hfull : measure.support=univ)
    (quantity : X → ℝ) (hcontinuous : Continuous quantity)
    (halmost : ∀ᵐ point ∂measure,0 ≤ quantity point) : ∀ point,0 ≤ quantity point := by
  have hsupport := measure.support_subset_of_isClosed
    (isClosed_le continuous_const hcontinuous) halmost
  intro point
  exact hsupport (by rw [hfull]; trivial)

theorem actual_every_euclidean_volume_ae_nonnegative_continuous_function_is_nonnegative_everywhere
    (dimension : ℕ) (quantity : EuclideanSpace ℝ (Fin dimension) → ℝ)
    (hcontinuous : Continuous quantity)
    (halmost : ∀ᵐ point ∂volume,0 ≤ quantity point) : ∀ point,0 ≤ quantity point := by
  apply actual_continuity_upgrades_an_almost_everywhere_nonnegative_bound_on_full_support
    volume Measure.support_eq_univ quantity hcontinuous halmost

end SafeLearning.CompleteFoundationsContinuousLevels22
