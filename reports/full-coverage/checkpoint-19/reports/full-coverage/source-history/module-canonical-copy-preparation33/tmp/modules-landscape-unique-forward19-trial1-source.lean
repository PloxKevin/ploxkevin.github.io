import SafeLearning.CompleteModulesLandscapeControlAffineGlobal

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Metric
open scoped Topology

namespace SafeLearning.CompleteModulesLandscapeUniqueForward

open SafeLearning.CompleteModulesLandscapeMaximalEndpoint
open SafeLearning.CompleteModulesLandscapeMaximalExistence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual forward solutions of the same locally Lipschitz field agree on
their entire common time domain. The field need not be globally Lipschitz. -/
theorem actual_two_forward_solutions_from_the_same_initial_state_agree_on_their_common_time_domain
    (F : E → E) (D : Set E) (hf : LocallyLipschitzOn D F) (x₀ : E)
    (p q : ForwardSolution F D x₀) :
    EqOn p.path q.path (forwardTimeDomain p.endpoint ∩ forwardTimeDomain q.endpoint) := by
  intro t ht
  have hsubp : Icc 0 t ⊆ forwardTimeDomain p.endpoint := by
    intro s hs
    exact ⟨hs.1, (EReal.coe_le_coe hs.2).trans_lt ht.1.2⟩
  have hsubq : Icc 0 t ⊆ forwardTimeDomain q.endpoint := by
    intro s hs
    exact ⟨hs.1, (EReal.coe_le_coe hs.2).trans_lt ht.2.2⟩
  have hcontp : ContinuousOn p.path (Icc 0 t) := by
    intro s hs
    exact ((p.ode s (hsubp hs)).mono hsubp).continuousWithinAt
  have hcontq : ContinuousOn q.path (Icc 0 t) := by
    intro s hs
    exact ((q.ode s (hsubq hs)).mono hsubq).continuousWithinAt
  let K : Set E := (p.path '' Icc 0 t) ∪ (q.path '' Icc 0 t)
  have hcompact : IsCompact K :=
    (isCompact_Icc.image_of_continuousOn hcontp).union
      (isCompact_Icc.image_of_continuousOn hcontq)
  have hKD : K ⊆ D := by
    intro z hz
    rcases hz with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
    · exact p.in_domain (hsubp hs)
    · exact q.in_domain (hsubq hs)
  obtain ⟨M, hM⟩ := (hf.mono hKD).exists_lipschitzOnWith_of_compact hcompact
  have hd (r : ForwardSolution F D x₀)
      (hsub : Icc 0 t ⊆ forwardTimeDomain r.endpoint) :
      ∀ s ∈ Ico 0 t, HasDerivWithinAt r.path (F (r.path s)) (Ici s) s := by
    intro s hs
    have hbound : {v : ℝ | (v : EReal) < r.endpoint} ∈ 𝓝 s :=
      (isOpen_lt continuous_coe_real_ereal continuous_const).mem_nhds
        (hsub (Ico_subset_Icc_self hs)).2
    have hdomain : forwardTimeDomain r.endpoint ∈ 𝓝[Ici s] s := by
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hbound] with v hv hvB
      exact ⟨hs.1.trans hv, hvB⟩
    exact (r.ode s (hsub (Ico_subset_Icc_self hs))).mono_of_mem_nhdsWithin hdomain
  have heq : EqOn p.path q.path (Icc 0 t) :=
    ODE_solution_unique_of_mem_Icc_right (v := fun _ => F) (s := fun _ => K)
      (fun _ _ => hM) hcontp (hd p hsubp)
      (fun s hs => Or.inl (mem_image_of_mem p.path (Ico_subset_Icc_self hs)))
      hcontq (hd q hsubq)
      (fun s hs => Or.inr (mem_image_of_mem q.path (Ico_subset_Icc_self hs)))
      (p.initial.trans q.initial.symm)
  exact heq ⟨ht.1.1, le_rfl⟩

/-- Actual global forward solutions are unique at every nonnegative time;
the arbitrary values used to represent them at negative times are irrelevant. -/
theorem actual_locally_lipschitz_global_forward_solution_is_unique_on_all_nonnegative_times
    (F : E → E) (D : Set E) (hf : LocallyLipschitzOn D F)
    (x y : ℝ → E) (hinit : x 0 = y 0)
    (hxD : MapsTo x (Ici 0) D) (hyD : MapsTo y (Ici 0) D)
    (hx : ∀ t ∈ Ici 0, HasDerivWithinAt x (F (x t)) (Ici 0) t)
    (hy : ∀ t ∈ Ici 0, HasDerivWithinAt y (F (y t)) (Ici 0) t) :
    EqOn x y (Ici 0) := by
  let p : ForwardSolution F D (x 0) := {
    endpoint := ⊤
    endpoint_pos := EReal.coe_lt_top 0
    path := x
    initial := rfl
    in_domain := by simpa only [forwardTimeDomain_top] using hxD
    ode := by simpa only [forwardTimeDomain_top] using hx }
  let q : ForwardSolution F D (x 0) := {
    endpoint := ⊤
    endpoint_pos := EReal.coe_lt_top 0
    path := y
    initial := hinit.symm
    in_domain := by simpa only [forwardTimeDomain_top] using hyD
    ode := by simpa only [forwardTimeDomain_top] using hy }
  simpa only [forwardTimeDomain_top, inter_self] using
    actual_two_forward_solutions_from_the_same_initial_state_agree_on_their_common_time_domain
      F D hf (x 0) p q

/-- The compact control-affine barrier theorem constructs a safe global
solution and derives uniqueness against every other true global forward
solution in the domain from that same safe initial state. -/
theorem actual_compact_control_affine_barrier_constructs_a_unique_global_safe_forward_solution
    {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ E]
    (D : Set E) (f : E → E) (g : E → U →L[ℝ] E) (u : E → U)
    (hf : LocallyLipschitzOn D f) (hg : LocallyLipschitzOn D g)
    (hu : LocallyLipschitzOn D u) (hD : IsOpen D)
    (h : E → ℝ) (alpha : ℝ → ℝ) (J : Set ℝ)
    (hh : ContDiffOn ℝ 1 h D) (hm : MonotoneOn alpha J)
    (ha0 : alpha 0 = 0) (hJ0 : (0 : ℝ) ∈ J) (hhJ : MapsTo h D J)
    (hbarrier : ∀ z ∈ D,
      -alpha (h z) ≤ fderiv ℝ h z (f z) + fderiv ℝ h z (g z (u z)))
    (hcompact : IsCompact {z | 0 ≤ h z}) (hsubset : {z | 0 ≤ h z} ⊆ D)
    (x₀ : E) (hx₀ : 0 ≤ h x₀) :
    ∃ x : ℝ → E, x 0 = x₀ ∧ (∀ t ≥ 0, 0 ≤ h (x t)) ∧
      (∀ t ≥ 0, HasDerivWithinAt x (f (x t) + g (x t) (u (x t))) (Ici 0) t) ∧
      (∀ t > 0, HasDerivAt x (f (x t) + g (x t) (u (x t))) t) ∧
      ∀ y : ℝ → E, y 0 = x₀ → MapsTo y (Ici 0) D →
        (∀ t ≥ 0, HasDerivWithinAt y (f (y t) + g (y t) (u (y t))) (Ici 0) t) →
        EqOn x y (Ici 0) := by
  obtain ⟨x, hinit, hsafe, hode, hpositive⟩ :=
    SafeLearning.CompleteModulesLandscapeControlAffineGlobal.actual_compact_control_affine_barrier_and_locally_lipschitz_policy_have_a_global_safe_solution
      D f g u hf hg hu hD h alpha J hh hm ha0 hJ0 hhJ hbarrier hcompact hsubset x₀ hx₀
  refine ⟨x, hinit, hsafe, hode, hpositive, ?_⟩
  intro y hyinit hyD hyODE
  apply actual_locally_lipschitz_global_forward_solution_is_unique_on_all_nonnegative_times
    (fun z => f z + g z (u z)) D
    (SafeLearning.CompleteModulesLandscapeControlAffineGlobal.actual_locally_lipschitz_control_affine_components_and_policy_give_a_locally_lipschitz_closed_loop
      D f g u hf hg hu) x y (hinit.trans hyinit.symm)
    (fun t ht => hsubset (hsafe t ht)) hyD hode hyODE

end SafeLearning.CompleteModulesLandscapeUniqueForward
