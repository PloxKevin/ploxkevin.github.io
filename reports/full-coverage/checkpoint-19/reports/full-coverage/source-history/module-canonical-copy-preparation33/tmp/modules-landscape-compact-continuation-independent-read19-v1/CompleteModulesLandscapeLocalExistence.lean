import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Metric
open scoped Topology NNReal

namespace SafeLearning.CompleteModulesLandscapeLocalExistence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The actual Picard fixed point stays in the ball used to certify its field. -/
theorem actual_picard_solution_exists_and_stays_in_its_certified_ball
    (f : ℝ → E → E) {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (x₀ : E)
    (a L K : ℝ≥0) (hf : IsPicardLindelof f t₀ x₀ a 0 L K) :
    ∃ x : ℝ → E, x t₀=x₀ ∧
      (∀t : ℝ, x t ∈ closedBall x₀ a) ∧
      ∀t ∈ Icc tmin tmax, HasDerivWithinAt x (f t (x t)) (Icc tmin tmax) t := by
  obtain ⟨x,hx⟩ := ODE.FunSpace.exists_isFixedPt_next hf (mem_closedBall_self le_rfl)
  refine ⟨x.compProj,?_,?_,?_⟩
  · rw [ODE.FunSpace.compProj_val,← hx,ODE.FunSpace.next_apply₀]
  · intro t
    exact x.compProj_mem_closedBall hf.mul_max_le
  · intro t ht
    apply (ODE.hasDerivWithinAt_picard_Icc t₀.2 hf.continuousOn_uncurry
      x.continuous_compProj.continuousOn
      (fun _ _ => x.compProj_mem_closedBall hf.mul_max_le) x₀ ht).congr_of_mem _ ht
    intro s hs
    nth_rw 1 [← hx]
    rw [ODE.FunSpace.compProj_of_mem hs,ODE.FunSpace.next_apply]

/-- Local autonomous existence follows from the stated local Lipschitz condition,
without strengthening it to C1 or a global Lipschitz condition. -/
theorem actual_locally_lipschitz_autonomous_field_on_an_open_domain_has_a_local_solution
    (f : E → E) (D : Set E) (hD : IsOpen D) (hf : LocallyLipschitzOn D f)
    (x₀ : E) (hx₀ : x₀ ∈ D) (t₀ : ℝ) :
    ∃ ε > (0:ℝ), ∃ x : ℝ → E, x t₀=x₀ ∧
      (∀t : ℝ, x t ∈ D) ∧
      ∀t ∈ Ioo (t₀-ε) (t₀+ε), HasDerivAt x (f (x t)) t := by
  obtain ⟨K,s,hs,hL⟩ := hf hx₀
  have hs' : s ∈ 𝓝 x₀ := by
    rwa [nhdsWithin_eq_nhds.mpr (hD.mem_nhds hx₀)] at hs
  obtain ⟨a,ha,has⟩ := Metric.mem_nhds_iff.mp (inter_mem hs' (hD.mem_nhds hx₀))
  have hbsubset : closedBall x₀ (a/2) ⊆ s ∩ D :=
    (closedBall_subset_ball (half_lt_self ha)).trans has
  let L : ℝ := K*a+‖f x₀‖+1
  have hLpos : 0<L := by dsimp [L]; positivity
  have hb : ∀x ∈ closedBall x₀ (a/2), ‖f x‖ ≤ L := by
    intro x hx
    calc
      ‖f x‖ ≤ ‖f x-f x₀‖+‖f x₀‖ := norm_le_norm_sub_add _ _
      _ ≤ K*‖x-x₀‖+‖f x₀‖ := by
        gcongr
        exact hL.norm_sub_le (hbsubset hx).1 (mem_of_mem_nhds hs')
      _ ≤ K*a+‖f x₀‖ := by
        gcongr
        exact (mem_closedBall_iff_norm.mp hx).trans (half_le_self ha.le)
      _ ≤ L := by dsimp [L]; linarith
  let ε : ℝ := (a/2)/L
  have hε : 0<ε := by dsimp [ε]; positivity
  let aNN : ℝ≥0 := ⟨a/2,(half_pos ha).le⟩
  let LNN : ℝ≥0 := ⟨L,hLpos.le⟩
  let tinit : Icc (t₀-ε) (t₀+ε) := ⟨t₀,by constructor <;> linarith⟩
  have hPL : IsPicardLindelof (fun _ => f) tinit x₀ aNN 0 LNN K := by
    apply IsPicardLindelof.of_time_independent hb
      (hL.mono (fun x hx => (hbsubset hx).1))
    change L*max (t₀+ε-t₀) (t₀-(t₀-ε)) ≤ a/2-0
    rw [show t₀+ε-t₀=ε by ring,show t₀-(t₀-ε)=ε by ring,max_self,sub_zero]
    dsimp [ε]
    rw [mul_div_cancel₀ _ (ne_of_gt hLpos)]
  obtain ⟨x,hinit,hball,hderiv⟩ :=
    actual_picard_solution_exists_and_stays_in_its_certified_ball (fun _ => f) tinit x₀ aNN LNN K hPL
  refine ⟨ε,hε,x,hinit,fun t => (hbsubset (hball t)).2,?_⟩
  intro t ht
  exact (hderiv t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

end SafeLearning.CompleteModulesLandscapeLocalExistence
