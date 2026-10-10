import SafeLearning.CompleteModulesLandscapeCompactEndpoint
import SafeLearning.CompleteModulesLandscapeLocalExistence

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Metric
open scoped Topology NNReal

namespace SafeLearning.CompleteModulesLandscapeCompactContinuation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Matching left and right ODE derivatives give a true derivative at the join. -/
theorem actual_matching_one_sided_derivatives_glue
    (X W : ℝ → E) (T : ℝ) (v : E) (hmatch : W T = X T)
    (hleft : HasDerivWithinAt X v (Iic T) T)
    (hright : HasDerivWithinAt W v (Ici T) T) :
    HasDerivAt (fun t => if t ≤ T then X t else W t) v T := by
  have hl : HasDerivWithinAt (fun t => if t ≤ T then X t else W t) v (Iic T) T :=
    hleft.congr_of_mem (fun t ht => ite_eq_left ht) le_rfl
  have hr : HasDerivWithinAt (fun t => if t ≤ T then X t else W t) v (Ici T) T := by
    apply hright.congr_of_mem _ le_rfl
    intro t ht
    by_cases h : t ≤ T
    · have he : t = T := le_antisymm h ht
      subst t
      simp only [le_refl, if_true, hmatch]
    · simp only [if_neg h]
  simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hl.union hr

variable [FiniteDimensional ℝ E]

/-- A true solution of a locally Lipschitz autonomous ODE, trapped in a compact
subset of its open domain up to finite positive T, actually continues past T.
The endpoint is derived from compact trapping, and the glued solution satisfies
the ODE also at T and at the original one-sided initial time 0. This is a local
continuation theorem; a global maximal-solution construction is separate. -/
theorem actual_compact_trapped_solution_of_a_locally_lipschitz_field_continues_past_finite_time
    (f : E → E) (D C : Set E) (hD : IsOpen D) (hf : LocallyLipschitzOn D f)
    (hC : IsCompact C) (hCD : C ⊆ D) (x : ℝ → E) (T : ℝ) (hT : 0 < T)
    (hxC : MapsTo x (Ico 0 T) C)
    (hODE : ∀ t ∈ Ico 0 T, HasDerivWithinAt x (f (x t)) (Ico 0 T) t) :
    ∃ ε > (0 : ℝ), ∃ y : ℝ → E,
      EqOn x y (Ico 0 T) ∧ y T ∈ C ∧
      Tendsto x (𝓝[<] T) (𝓝 (y T)) ∧
      MapsTo y (Ico 0 (T + ε)) D ∧
      (∀ t ∈ Ico 0 (T + ε),
        HasDerivWithinAt y (f (y t)) (Ico 0 (T + ε)) t) ∧
      (∀ t ∈ Ioo 0 (T + ε), HasDerivAt y (f (y t)) t) := by
  obtain ⟨X,hXLip,hEq,hXC,hlim,hdX,hleft⟩ :=
    SafeLearning.CompleteModulesLandscapeCompactEndpoint.actual_compact_trapped_solution_has_a_true_safe_endpoint_and_left_derivative
      f D C hD hf hC hCD x T hT hxC hODE
  obtain ⟨ε,hε,W,hinit,hWD,hdW⟩ :=
    SafeLearning.CompleteModulesLandscapeLocalExistence.actual_locally_lipschitz_autonomous_field_on_an_open_domain_has_a_local_solution
      f D hD hf (X T) (hCD hXC) T
  let y : ℝ → E := fun t => if t ≤ T then X t else W t
  have hyX : ∀ t ≤ T, y t = X t := fun t ht => ite_eq_left ht
  have hyW : ∀ t ≥ T, y t = W t := by
    intro t ht
    by_cases h : t ≤ T
    · have he : t = T := le_antisymm h ht
      subst t
      exact (hyX T le_rfl).trans hinit.symm
    · exact ite_eq_right h
  have hyT : y T = X T := hyX T le_rfl
  have hxy : EqOn x y (Ico 0 T) := by
    intro t ht
    exact (hEq ht).trans (hyX t ht.2.le).symm
  have hdjoin : HasDerivAt y (f (y T)) T := by
    rw [hyT]
    apply actual_matching_one_sided_derivatives_glue X W T (f (X T)) hinit hleft
    have hWT : HasDerivAt W (f (W T)) T := hdW T (by constructor <;> linarith)
    simpa only [hinit] using hWT.hasDerivWithinAt (s := Ici T)
  have hdinterior : ∀ t ∈ Ioo 0 (T + ε), HasDerivAt y (f (y t)) t := by
    intro t ht
    rcases lt_trichotomy t T with hlt | heq | hgt
    · have he : y =ᶠ[𝓝 t] X := by
        filter_upwards [eventually_lt_nhds hlt] with s hs
        exact hyX s hs.le
      rw [hyX t hlt.le]
      exact (hdX t ⟨ht.1,hlt⟩).congr_of_eventuallyEq he
    · subst t
      exact hdjoin
    · have he : y =ᶠ[𝓝 t] W := by
        filter_upwards [eventually_gt_nhds hgt] with s hs
        exact hyW s hs.le
      rw [hyW t hgt.le]
      exact (hdW t ⟨by linarith,ht.2⟩).congr_of_eventuallyEq he
  have hdwhole : ∀ t ∈ Ico 0 (T + ε),
      HasDerivWithinAt y (f (y t)) (Ico 0 (T + ε)) t := by
    intro t ht
    by_cases hzero : t = 0
    · subst t
      have hold : Ico 0 T ∈ 𝓝[Ico 0 (T + ε)] (0 : ℝ) := by
        filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (eventually_lt_nhds hT)] with s hs hst
        exact ⟨hs.1,hst⟩
      have he : y =ᶠ[𝓝[Ico 0 (T + ε)] (0 : ℝ)] x := by
        filter_upwards [hold] with s hs
        exact (hxy hs).symm
      have h0 : (0 : ℝ) ∈ Ico 0 T := ⟨le_rfl,hT⟩
      rw [← hxy h0]
      exact ((hODE 0 h0).mono_of_mem_nhdsWithin hold).congr_of_eventuallyEq he (hxy h0).symm
    · exact (hdinterior t ⟨lt_of_le_of_ne ht.1 (Ne.symm hzero),ht.2⟩).hasDerivWithinAt
  refine ⟨ε,hε,y,hxy,?_,?_,?_,hdwhole,hdinterior⟩
  · simpa only [hyT] using hXC
  · simpa only [hyT] using hlim
  · intro t ht
    by_cases h : t < T
    · rw [← hxy ⟨ht.1,h⟩]
      exact hCD (hxC ⟨ht.1,h⟩)
    · rw [hyW t (le_of_not_gt h)]
      exact hWD t

end SafeLearning.CompleteModulesLandscapeCompactContinuation
