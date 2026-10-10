import SafeLearning.CompleteModulesLandscapeGlobalExistence
import SafeLearning.CompleteBarrierVectorChainRule
import SafeLearning.CompleteBarrierNonlinearDomainComparison

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology NNReal

namespace SafeLearning.CompleteModulesLandscapeBarrierGlobal

open SafeLearning.CompleteModulesLandscapeMaximalEndpoint
open SafeLearning.CompleteModulesLandscapeMaximalExistence
open SafeLearning.CompleteModulesLandscapeGlobalExistence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- On every compact time prefix of a true forward solution, its continuous
velocity is bounded and its actual path is absolutely continuous. -/
theorem actual_forward_solution_is_absolutely_continuous_on_every_compact_time_prefix
    (F : E → E) (D : Set E) (hf : LocallyLipschitzOn D F)
    (x₀ : E) (p : ForwardSolution F D x₀) (t : ℝ)
    (ht : t ∈ forwardTimeDomain p.endpoint) :
    AbsolutelyContinuousOnInterval p.path 0 t := by
  have hsubset : Icc 0 t ⊆ forwardTimeDomain p.endpoint := by
    intro s hs
    exact ⟨hs.1, (EReal.coe_le_coe hs.2).trans_lt ht.2⟩
  have hode : ∀ s ∈ Icc 0 t,
      HasDerivWithinAt p.path (F (p.path s)) (Icc 0 t) s := by
    intro s hs
    exact (p.ode s (hsubset hs)).mono hsubset
  have hcont : ContinuousOn p.path (Icc 0 t) := by
    intro s hs
    exact (hode s hs).continuousWithinAt
  have hcompact : IsCompact (p.path '' Icc 0 t) :=
    isCompact_Icc.image_of_continuousOn hcont
  have himage : p.path '' Icc 0 t ⊆ D := by
    rintro z ⟨s, hs, rfl⟩
    exact p.in_domain (hsubset hs)
  obtain ⟨M, hM⟩ :=
    SafeLearning.CompleteModulesLandscapeCompactEndpoint.actual_continuous_field_has_a_uniform_norm_bound_on_a_compact_set
      F (p.path '' Icc 0 t) hcompact (hf.continuousOn.mono himage)
  have hlip : LipschitzOnWith M p.path (Icc 0 t) :=
    (convex_Icc (0 : ℝ) t).lipschitzOnWith_of_nnnorm_hasDerivWithin_le hode
      (fun s hs => hM (p.path s) (mem_image_of_mem p.path hs))
  apply LipschitzOnWith.absolutelyContinuousOnInterval (K := M)
  simpa only [uIcc_of_le ht.1] using hlip

/-- The actual C1 barrier inequality on an open domain proves invariance for
every true forward solution. No solution existence or invariance conclusion
is supplied as a premise. -/
theorem actual_barrier_inequality_proves_forward_invariance_of_its_superlevel_set
    (F : E → E) (D : Set E) (h : E → ℝ) (alpha : ℝ → ℝ) (J : Set ℝ)
    (hD : IsOpen D) (hf : LocallyLipschitzOn D F) (hh : ContDiffOn ℝ 1 h D)
    (hm : MonotoneOn alpha J) (ha0 : alpha 0 = 0) (hJ0 : (0 : ℝ) ∈ J)
    (hhJ : MapsTo h D J)
    (hbarrier : ∀ z ∈ D, -alpha (h z) ≤ fderiv ℝ h z (F z)) :
    IsForwardInvariant F D {z | 0 ≤ h z} := by
  intro x₀ hx₀ p t ht
  have hsubset : Icc 0 t ⊆ forwardTimeDomain p.endpoint := by
    intro s hs
    exact ⟨hs.1, (EReal.coe_le_coe hs.2).trans_lt ht.2⟩
  have hxD : MapsTo p.path (uIcc 0 t) D := by
    rw [uIcc_of_le ht.1]
    exact p.in_domain.mono_left hsubset
  have hac := actual_forward_solution_is_absolutely_continuous_on_every_compact_time_prefix
    F D hf x₀ p t ht
  have hderiv : ∀ᵐ s ∂volume, s ∈ Icc 0 t → HasDerivAt p.path (F (p.path s)) s := by
    have hne : ∀ᵐ s : ℝ ∂volume, s ≠ 0 := by simp [ae_iff]
    filter_upwards [hne] with s hs hst
    have hpos : 0 < s := lt_of_le_of_ne hst.1 (Ne.symm hs)
    have hbound : {r : ℝ | (r : EReal) < p.endpoint} ∈ 𝓝 s :=
      (isOpen_lt continuous_coe_real_ereal continuous_const).mem_nhds (hsubset hst).2
    have hdomain : forwardTimeDomain p.endpoint ∈ 𝓝 s := by
      filter_upwards [eventually_gt_nhds hpos, hbound] with r hr hrB
      exact ⟨hr.le, hrB⟩
    exact (p.ode s (hsubset hst)).hasDerivAt hdomain
  have hsafety : ∀ s ∈ Icc 0 t, 0 ≤ h (p.path s) := by
    apply CompleteBarrierNonlinearDomainComparison.genuine_nonlinear_invariance
      (h ∘ p.path) (fun s => fderiv ℝ h (p.path s) (F (p.path s)))
      alpha J 0 t ht.1 hm ha0
      (CompleteBarrierVectorChainRule.genuine_c1_ac_composition h p.path D 0 t hD hh hac hxD) hJ0
    · intro s hs
      exact hhJ (hxD (by simpa only [uIcc_of_le ht.1] using hs))
    · exact CompleteBarrierVectorChainRule.genuine_ae_vector_chain_rule
        h p.path (fun s => F (p.path s)) D 0 t hD hh ht.1 hxD hderiv
    · exact Eventually.of_forall fun s hs =>
        hbarrier (p.path s) (p.in_domain (hsubset hs))
    · change 0 ≤ h (p.path 0)
      rw [p.initial]
      exact hx₀
  exact hsafety t ⟨ht.1, le_rfl⟩

/-- Compactness and the actual barrier inequality together yield an actual
global safe solution from every safe initial state. Maximal existence and
infinite forward lifetime are derived by the preceding ODE construction. -/
theorem actual_compact_barrier_superlevel_set_has_a_global_safe_solution_from_every_safe_state
    (F : E → E) (D : Set E) (h : E → ℝ) (alpha : ℝ → ℝ) (J : Set ℝ)
    (hD : IsOpen D) (hf : LocallyLipschitzOn D F) (hh : ContDiffOn ℝ 1 h D)
    (hm : MonotoneOn alpha J) (ha0 : alpha 0 = 0) (hJ0 : (0 : ℝ) ∈ J)
    (hhJ : MapsTo h D J)
    (hbarrier : ∀ z ∈ D, -alpha (h z) ≤ fderiv ℝ h z (F z))
    (hcompact : IsCompact {z | 0 ≤ h z}) (hsubset : {z | 0 ≤ h z} ⊆ D)
    (x₀ : E) (hx₀ : 0 ≤ h x₀) :
    ∃ x : ℝ → E, x 0 = x₀ ∧ (∀ t ≥ 0, 0 ≤ h (x t)) ∧
      (∀ t ≥ 0, HasDerivWithinAt x (F (x t)) (Ici 0) t) ∧
      (∀ t > 0, HasDerivAt x (F (x t)) t) := by
  have hinvariant := actual_barrier_inequality_proves_forward_invariance_of_its_superlevel_set
    F D h alpha J hD hf hh hm ha0 hJ0 hhJ hbarrier
  obtain ⟨x, hinit, hsafe, hode, hpositive⟩ :=
    actual_compact_invariant_set_yields_global_forward_solution_existence
      F D {z | 0 ≤ h z} hD hf hcompact hsubset hinvariant x₀ hx₀
  exact ⟨x, hinit, hsafe, hode, hpositive⟩

end SafeLearning.CompleteModulesLandscapeBarrierGlobal
