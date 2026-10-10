import SafeLearning.CompleteModulesLandscapeRegularBoundaryLocal
import SafeLearning.CompleteModulesLandscapeGlobalExistence

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Metric
open scoped Topology NNReal

namespace SafeLearning.CompleteModulesLandscapeRegularBoundaryInvariance

open SafeLearning.CompleteModulesLandscapeRegularBoundaryLocal
open SafeLearning.CompleteModulesLandscapeMaximalEndpoint
open SafeLearning.CompleteModulesLandscapeMaximalExistence
open SafeLearning.CompleteModulesLandscapeGlobalExistence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Time translation of an existing true solution transfers the derived weak
boundary safety prefix to any regular boundary encounter before its endpoint. -/
theorem actual_regular_boundary_encounter_has_a_safe_future_prefix
    (F : E → E) (h : E → ℝ) (D : Set E) (hD : IsOpen D)
    (hf : LocallyLipschitzOn D F) (hh : ContDiffOn ℝ 1 h D)
    (x : ℝ → E) (a b t : ℝ)
    (hx : ContinuousOn x (Icc a b)) (hxD : MapsTo x (Icc a b) D)
    (hODE : ∀ u ∈ Ico a b, HasDerivWithinAt x (F (x u)) (Ici u) u)
    (ht : t ∈ Ico a b) (hzero : h (x t) = 0)
    (hregular : fderiv ℝ h (x t) ≠ 0)
    (hinward : ∀ z ∈ D, h z = 0 → 0 ≤ fderiv ℝ h z (F z)) :
    ∃ γ > (0 : ℝ), t + γ < b ∧ ∀ u ∈ Icc 0 γ, 0 ≤ h (x (t + u)) := by
  have hshift : MapsTo (fun u : ℝ => t + u) (Icc 0 (b - t)) (Icc a b) := by
    intro u hu
    constructor <;> linarith [ht.1,hu.1,hu.2]
  have hshiftODE : ∀ u ∈ Ico 0 (b - t),
      HasDerivWithinAt (fun u => x (t + u)) (F (x (t + u))) (Ici u) u := by
    intro u hu
    have htu : t + u ∈ Ico a b := ⟨by linarith [ht.1,hu.1],by linarith [hu.2]⟩
    have htime : MapsTo (fun w : ℝ => t + w) (Ici u) (Ici (t + u)) := by
      intro w hw
      change u ≤ w at hw
      change t + u ≤ t + w
      exact add_le_add_left hw t
    simpa only [Function.comp_def,one_smul] using
      (hODE (t + u) htu).scomp u
        (((hasDerivAt_id u).const_add t).hasDerivWithinAt) htime
  obtain ⟨γ,hγ,hγb,hsafe⟩ :=
    actual_regular_boundary_only_inward_condition_gives_local_safety_of_an_existing_path
      F h D hD hf hh (fun u => x (t + u)) (b - t) (sub_pos.mpr ht.2)
      (hx.comp (continuous_const.add continuous_id).continuousOn hshift)
      (hxD.comp hshift) hshiftODE
      (by simpa only [add_zero] using hzero)
      (by simpa only [add_zero] using hregular) hinward
  exact ⟨γ,hγ,by linarith,hsafe⟩

/-- Boundary-only weak inwardness at every regular zero of a C1 defining
function keeps every existing true ODE path in the superlevel set. Local
perturbation limits supply the nontrivial boundary step of continuous induction. -/
theorem actual_regular_boundary_only_inward_condition_keeps_every_existing_path_safe
    (F : E → E) (h : E → ℝ) (D : Set E) (hD : IsOpen D)
    (hf : LocallyLipschitzOn D F) (hh : ContDiffOn ℝ 1 h D)
    (x : ℝ → E) (a b : ℝ)
    (hx : ContinuousOn x (Icc a b)) (hxD : MapsTo x (Icc a b) D)
    (hODE : ∀ t ∈ Ico a b, HasDerivWithinAt x (F (x t)) (Ici t) t)
    (hinit : 0 ≤ h (x a))
    (hregular : ∀ z ∈ D, h z = 0 → fderiv ℝ h z ≠ 0)
    (hinward : ∀ z ∈ D, h z = 0 → 0 ≤ fderiv ℝ h z (F z)) :
    ∀ t ∈ Icc a b, 0 ≤ h (x t) := by
  have hc : ContinuousOn (fun t => h (x t)) (Icc a b) := hh.continuousOn.comp hx hxD
  let S : Set ℝ := {t | 0 ≤ h (x t)}
  have hclosed : IsClosed (S ∩ Icc a b) := by
    rw [inter_comm]
    exact hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  apply hclosed.Icc_subset_of_forall_exists_gt hinit
  intro t ht y hy
  have htI : t ∈ Icc a b := Ico_subset_Icc_self ht.2
  have hyt : 0 < y - t := sub_pos.mpr hy
  have hbt : 0 < b - t := sub_pos.mpr ht.2.2
  by_cases hz : h (x t) = 0
  · obtain ⟨γ,hγ,hγb,hsafe⟩ := actual_regular_boundary_encounter_has_a_safe_future_prefix
      F h D hD hf hh x a b t hx hxD hODE ht.2 hz (hregular (x t) (hxD htI) hz) hinward
    let d : ℝ := min γ (y - t) / 2
    have hd : 0 < d := by dsimp [d]; exact half_pos (lt_min hγ hyt)
    have hdγ : d ≤ γ := by
      have hm := min_le_left γ (y - t)
      dsimp [d]; linarith
    have hdy : d ≤ y - t := by
      have hm := min_le_right γ (y - t)
      dsimp [d]; linarith
    exact ⟨t + d,hsafe d ⟨hd.le,hdγ⟩,by linarith,by linarith⟩
  · have hp : 0 < h (x t) := lt_of_le_of_ne ht.1 (Ne.symm hz)
    obtain ⟨δ,hδ,hclose⟩ := Metric.continuousWithinAt_iff.mp (hc t htI) (h (x t)) hp
    let d : ℝ := min δ (min (b - t) (y - t)) / 2
    have hd : 0 < d := by dsimp [d]; exact half_pos (lt_min hδ (lt_min hbt hyt))
    have hdδ : d < δ := by
      have hm := min_le_left δ (min (b - t) (y - t))
      dsimp [d]; linarith
    have hdb : d ≤ b - t := by
      have hm := (min_le_right δ (min (b - t) (y - t))).trans (min_le_left _ _)
      dsimp [d]; linarith
    have hdy : d ≤ y - t := by
      have hm := (min_le_right δ (min (b - t) (y - t))).trans (min_le_right _ _)
      dsimp [d]; linarith
    have htd : t + d ∈ Icc a b := ⟨by linarith [ht.2.1],by linarith⟩
    have hdist : dist (t + d) t < δ := by
      simpa only [Real.dist_eq,add_sub_cancel_left,abs_of_pos hd] using hdδ
    have hpos : 0 ≤ h (x (t + d)) := by
      have hbound := hclose htd hdist
      have hlower := (abs_lt.mp (by simpa only [Real.dist_eq] using hbound)).1
      linarith
    exact ⟨t + d,hpos,by linarith,by linarith⟩

/-- The regular-boundary theorem applies to every actual forward solution,
including its initial endpoint, and derives the invariant-set predicate. -/
theorem actual_regular_boundary_only_inward_condition_proves_forward_invariance
    (F : E → E) (h : E → ℝ) (D : Set E) (hD : IsOpen D)
    (hf : LocallyLipschitzOn D F) (hh : ContDiffOn ℝ 1 h D)
    (hregular : ∀ z ∈ D, h z = 0 → fderiv ℝ h z ≠ 0)
    (hinward : ∀ z ∈ D, h z = 0 → 0 ≤ fderiv ℝ h z (F z)) :
    IsForwardInvariant F D {z | 0 ≤ h z} := by
  intro x₀ hx₀ p t ht
  change 0 ≤ h x₀ at hx₀
  have hsubset : Icc 0 t ⊆ forwardTimeDomain p.endpoint := by
    intro s hs
    exact ⟨hs.1,(EReal.coe_le_coe hs.2).trans_lt ht.2⟩
  have hcont : ContinuousOn p.path (Icc 0 t) := by
    intro s hs
    exact ((p.ode s (hsubset hs)).mono hsubset).continuousWithinAt
  have hright : ∀ s ∈ Ico 0 t,
      HasDerivWithinAt p.path (F (p.path s)) (Ici s) s := by
    intro s hs
    have hsB := hsubset (Ico_subset_Icc_self hs)
    have hbound : {r : ℝ | (r : EReal) < p.endpoint} ∈ 𝓝 s :=
      (isOpen_lt continuous_coe_real_ereal continuous_const).mem_nhds hsB.2
    have hdomain : forwardTimeDomain p.endpoint ∈ 𝓝[Ici s] s := by
      filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds hbound] with r hr hrbound
      exact ⟨hs.1.trans hr,hrbound⟩
    exact (p.ode s hsB).mono_of_mem_nhdsWithin hdomain
  apply actual_regular_boundary_only_inward_condition_keeps_every_existing_path_safe
    F h D hD hf hh p.path 0 t hcont (p.in_domain.mono_left hsubset) hright
    (by simpa only [p.initial] using hx₀) hregular hinward t ⟨ht.1,le_rfl⟩

variable [FiniteDimensional ℝ E]

/-- A compact safe superlevel set inside the open domain has actual global
solutions under the regular-boundary-only inward condition. Invariance and
maximal existence are derived, not supplied as conclusions in the hypotheses. -/
theorem actual_compact_regular_superlevel_set_with_boundary_only_inwardness_has_global_solutions
    (F : E → E) (h : E → ℝ) (D : Set E) (hD : IsOpen D)
    (hf : LocallyLipschitzOn D F) (hh : ContDiffOn ℝ 1 h D)
    (hC : IsCompact {z | 0 ≤ h z}) (hCD : {z | 0 ≤ h z} ⊆ D)
    (hregular : ∀ z ∈ D, h z = 0 → fderiv ℝ h z ≠ 0)
    (hinward : ∀ z ∈ D, h z = 0 → 0 ≤ fderiv ℝ h z (F z))
    (x₀ : E) (hx₀ : 0 ≤ h x₀) :
    ∃ x : ℝ → E, x 0 = x₀ ∧ MapsTo x (Ici 0) {z | 0 ≤ h z} ∧
      (∀ t ∈ Ici 0, HasDerivWithinAt x (F (x t)) (Ici 0) t) ∧
      (∀ t ∈ Ioi 0, HasDerivAt x (F (x t)) t) := by
  exact actual_compact_invariant_set_yields_global_forward_solution_existence
    F D {z | 0 ≤ h z} hD hf hC hCD
    (actual_regular_boundary_only_inward_condition_proves_forward_invariance
      F h D hD hf hh hregular hinward) x₀ hx₀

end SafeLearning.CompleteModulesLandscapeRegularBoundaryInvariance
