import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Metric
open scoped Topology NNReal

namespace SafeLearning.CompleteModulesLandscapeCompactEndpoint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem actual_continuous_field_has_a_uniform_norm_bound_on_a_compact_set
    (f : E → E) (C : Set E) (hC : IsCompact C) (hf : ContinuousOn f C) :
    ∃ M : ℝ≥0, ∀z ∈ C, ‖f z‖₊ ≤ M := by
  obtain ⟨B,hB⟩ := hC.bddAbove_image hf.norm
  refine ⟨⟨max B 0,le_max_right _ _⟩,?_⟩
  intro z hz
  exact_mod_cast (hB (mem_image_of_mem (fun z => ‖f z‖) hz)).trans (le_max_left B 0)

/-- A compact-trapped true ODE solution has an actual finite endpoint in the
compact set. Its endpoint derivative is obtained by derivative extension. -/
theorem actual_compact_trapped_solution_has_a_true_safe_endpoint_and_left_derivative
    (f : E → E) (D C : Set E) (hD : IsOpen D) (hf : LocallyLipschitzOn D f)
    (hC : IsCompact C) (hCD : C ⊆ D) (x : ℝ → E) (T : ℝ) (hT : 0<T)
    (hxC : MapsTo x (Ico 0 T) C)
    (hODE : ∀t ∈ Ico 0 T, HasDerivWithinAt x (f (x t)) (Ico 0 T) t) :
    ∃ X : ℝ → E, (∃ M : ℝ≥0, LipschitzWith M X) ∧ EqOn x X (Ico 0 T) ∧
      X T ∈ C ∧ Tendsto x (𝓝[<] T) (𝓝 (X T)) ∧
      (∀t ∈ Ioo 0 T, HasDerivAt X (f (X t)) t) ∧
      HasDerivWithinAt X (f (X T)) (Iic T) T := by
  obtain ⟨M,hM⟩ := actual_continuous_field_has_a_uniform_norm_bound_on_a_compact_set
    f C hC (hf.continuousOn.mono hCD)
  have hxLip : LipschitzOnWith M x (Ico 0 T) :=
    (convex_Ico (0:ℝ) T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le hODE
      (fun t ht => hM (x t) (hxC ht))
  obtain ⟨X,hX,hEq⟩ := hxLip.extend_finite_dimension
  have hnear : ∀ᶠ t : ℝ in 𝓝[<] T, t ∈ Ioo 0 T := by
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (eventually_gt_nhds hT)] with t ht hpos
    exact ⟨hpos,ht⟩
  have hEqNear : x =ᶠ[𝓝[<] T] X := by
    filter_upwards [hnear] with t ht
    exact hEq (Ioo_subset_Ico_self ht)
  have hlim : Tendsto x (𝓝[<] T) (𝓝 (X T)) :=
    (hX.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' hEqNear.symm
  have hendpoint : X T ∈ C := hC.isClosed.mem_of_tendsto hlim (by
    filter_upwards [hnear] with t ht
    exact hxC (Ioo_subset_Ico_self ht))
  have hdX : ∀t ∈ Ioo 0 T, HasDerivAt X (f (X t)) t := by
    intro t ht
    have he : X =ᶠ[𝓝 t] x := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact (hEq (Ioo_subset_Ico_self hs)).symm
    rw [← hEq (Ioo_subset_Ico_self ht)]
    exact ((hODE t (Ioo_subset_Ico_self ht)).hasDerivAt
      (mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Ioo_subset_Ico_self)).congr_of_eventuallyEq he
  have hfield : ContinuousAt (fun t => f (X t)) T :=
    (hf.continuousOn.continuousAt (hD.mem_nhds (hCD hendpoint))).comp hX.continuous.continuousAt
  have hderivlim : Tendsto (deriv X) (𝓝[<] T) (𝓝 (f (X T))) := by
    apply (hfield.tendsto.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [hnear] with t ht
    exact (hdX t ht).deriv.symm
  have hleft : HasDerivWithinAt X (f (X T)) (Iic T) T :=
    hasDerivWithinAt_Iic_of_tendsto_deriv
      (fun t ht => (hdX t ht).differentiableAt.differentiableWithinAt)
      hX.continuous.continuousAt.continuousWithinAt hnear hderivlim
  exact ⟨X,⟨_,hX⟩,hEq,hendpoint,hlim,hdX,hleft⟩

end SafeLearning.CompleteModulesLandscapeCompactEndpoint
