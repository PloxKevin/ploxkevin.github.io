import SafeLearning.CompleteAppliedScalarTrajectories
import SafeLearning.CompleteAppliedGlobalLipschitzACUniqueness

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace SafeLearning.CompleteAppliedComparisonFilter

def comparison (t : ℝ) : ℝ := 1/2+(5/2)*Real.exp (-2*t)
def field (x : ℝ) : ℝ := min 1 (2*(1-x))
def filteredTrajectory (t : ℝ) : ℝ :=
  if t ≤ 1/2 then t else 1-(1/2)*Real.exp (-2*(t-1/2))

theorem actual_affine_comparison_field_is_lipschitz :
    LipschitzWith 2 (fun x : ℝ => -2*x+1) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  change |-2*x+1-(-2*y+1)| ≤ 2*|x-y|
  rw [show -2*x+1-(-2*y+1)=-2*(x-y) by ring,abs_mul]
  norm_num

theorem actual_comparison_initial_and_ODE (t : ℝ) :
    comparison 0=3 ∧ HasDerivAt comparison (-2*comparison t+1) t := by
  constructor
  · norm_num [comparison]
  · unfold comparison
    convert ((((hasDerivAt_id t).const_mul (-2)).exp).const_mul (5/2)).const_add (1/2)
      using 1 <;> (try ext s) <;> simp only [id_eq] <;> ring

theorem actual_every_classical_subsolution_obeys_the_comparison
    (v dv : ℝ → ℝ) (horizon : ℝ)
    (hc : ContinuousOn v (Icc 0 horizon)) (h0 : v 0=3)
    (hd : ∀ t ∈ Ico 0 horizon,HasDerivAt v (dv t) t)
    (hb : ∀ t ∈ Ico 0 horizon,dv t ≤ -2*v t+1) :
    ∀ t ∈ Icc 0 horizon,v t ≤ comparison t := by
  have h := CompleteAppliedScalarTrajectories.actual_scalar_derivative_comparison
    (fun t => v t-1/2) dv (-2) horizon (hc.sub continuousOn_const)
    (fun t ht => (hd t ht).sub_const (1/2)) (by intro t ht;linarith [hb t ht])
  intro t ht
  have hh := h t ht
  rw [h0] at hh
  dsimp [comparison] at *
  linarith

theorem actual_filter_constraint_and_values (x u : ℝ) :
    (-u+2*(1-x) ≥ 0 ↔ u ≤ 2*(1-x)) ∧
    field 0=1 ∧ field (4/5)=2/5 ∧
    (2*(1-x) ≥ 1 ↔ x ≤ 1/2) := by
  refine ⟨by constructor <;> intro h <;> linarith,?_,?_,?_⟩
  · norm_num [field]
  · norm_num [field]
  · constructor <;> intro h <;> linarith

theorem actual_filtered_field_is_globally_lipschitz : LipschitzWith 2 field := by
  have h : LipschitzWith 2 (fun x : ℝ => 2*(1-x)) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    change |2*(1-x)-2*(1-y)| ≤ 2*|x-y|
    rw [show 2*(1-x)-2*(1-y)=-2*(x-y) by ring,abs_mul]
    norm_num
  exact h.const_min 1

theorem actual_filtered_trajectory_initial : filteredTrajectory 0=0 := by
  norm_num [filteredTrajectory]

theorem actual_post_switch_branch_derivative (t : ℝ) :
    HasDerivAt (fun s : ℝ => 1-(1/2)*Real.exp (-2*(s-1/2)))
      (Real.exp (-2*(t-1/2))) t := by
  convert ((((hasDerivAt_id t).sub_const (1/2)).const_mul (-2)).exp.const_mul (1/2)).const_sub 1
    using 1 <;> (try ext s) <;> simp only [id_eq] <;> ring

theorem actual_filtered_trajectory_ODE_at_every_time (t : ℝ) :
    HasDerivAt filteredTrajectory (field (filteredTrajectory t)) t := by
  rcases lt_trichotomy t (1/2:ℝ) with ht | ht | ht
  · have hf : filteredTrajectory =ᶠ[𝓝 t] fun s : ℝ => s := by
      filter_upwards [eventually_lt_nhds ht] with s hs
      dsimp only [filteredTrajectory]
      rw [if_pos hs.le]
    have hv : field (filteredTrajectory t)=1 := by
      simp only [filteredTrajectory,if_pos ht.le,field]
      rw [min_eq_left (by linarith)]
    rw [hv]
    exact (hasDerivAt_id t).congr_of_eventuallyEq hf
  · subst t
    have hp : filteredTrajectory (1/2)=1/2 := by norm_num [filteredTrajectory]
    have hl : HasDerivWithinAt filteredTrajectory 1 (Iic (1/2:ℝ)) (1/2) := by
      apply (hasDerivAt_id (1/2:ℝ)).hasDerivWithinAt.congr
      · intro s hs
        dsimp only [filteredTrajectory]
        rw [if_pos (show s ≤ 1/2 from hs)]
        rfl
      · exact hp
    have hr : HasDerivWithinAt filteredTrajectory 1 (Ici (1/2:ℝ)) (1/2) := by
      have h := actual_post_switch_branch_derivative (1/2)
      norm_num at h
      apply h.hasDerivWithinAt.congr
      · intro s hs
        by_cases he : s=1/2
        · subst s;norm_num [filteredTrajectory]
        · have hgt : 1/2<s := lt_of_le_of_ne hs (Ne.symm he)
          dsimp only [filteredTrajectory]
          rw [if_neg (not_le.mpr hgt)]
          simp only [neg_mul]
      · norm_num [hp]
    have h := hl.union hr
    rw [Iic_union_Ici,hasDerivWithinAt_univ] at h
    rw [hp]
    norm_num [field]
    exact h
  · have hf : filteredTrajectory =ᶠ[𝓝 t]
        fun s : ℝ => 1-(1/2)*Real.exp (-2*(s-1/2)) := by
      filter_upwards [eventually_gt_nhds ht] with s hs
      dsimp only [filteredTrajectory]
      rw [if_neg (not_le.mpr hs)]
    have hv : field (filteredTrajectory t)=Real.exp (-2*(t-1/2)) := by
      have he : Real.exp (-2*(t-1/2)) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        linarith
      simp only [field,filteredTrajectory,if_neg (not_le.mpr ht)]
      rw [show 2*(1-(1-(1/2)*Real.exp (-2*(t-1/2))))=
        Real.exp (-2*(t-1/2)) by ring,min_eq_right he]
    rw [hv]
    exact (actual_post_switch_branch_derivative t).congr_of_eventuallyEq hf

theorem actual_filtered_trajectory_is_C1 : ContDiff ℝ 1 filteredTrajectory := by
  rw [contDiff_one_iff_deriv]
  have hd : Differentiable ℝ filteredTrajectory :=
    fun t => (actual_filtered_trajectory_ODE_at_every_time t).differentiableAt
  refine ⟨hd,?_⟩
  have he : deriv filteredTrajectory = field ∘ filteredTrajectory := by
    funext t
    exact (actual_filtered_trajectory_ODE_at_every_time t).deriv
  rw [he]
  exact actual_filtered_field_is_globally_lipschitz.continuous.comp hd.continuous

theorem actual_filtered_trajectory_is_locally_absolutely_continuous (horizon : ℝ) :
    AbsolutelyContinuousOnInterval filteredTrajectory 0 horizon :=
  actual_filtered_trajectory_is_C1.contDiffOn.absolutelyContinuousOnInterval

theorem actual_every_existing_AC_filtered_trajectory_is_the_constructed_one
    (x : ℝ → ℝ) (horizon : ℝ) (hT : 0 ≤ horizon)
    (hx : AbsolutelyContinuousOnInterval x 0 horizon) (h0 : x 0=0)
    (hODE : ∀ᵐ t ∂volume,t ∈ Icc 0 horizon → HasDerivAt x (field (x t)) t) :
    ∀ t ∈ Icc 0 horizon,x t=filteredTrajectory t := by
  apply CompleteAppliedGlobalLipschitzACUniqueness.actual_globally_lipschitz_field_has_unique_existing_ac_solutions
    field 2 actual_filtered_field_is_globally_lipschitz x filteredTrajectory horizon hT hx
    (actual_filtered_trajectory_is_locally_absolutely_continuous horizon) hODE
    (Filter.Eventually.of_forall (fun t _ => actual_filtered_trajectory_ODE_at_every_time t))
  rw [h0,actual_filtered_trajectory_initial]

theorem actual_filtered_barrier_stays_strictly_positive (t : ℝ) (ht : 0 ≤ t) :
    0 < 1-filteredTrajectory t := by
  by_cases hs : t ≤ 1/2
  · simp only [filteredTrajectory,if_pos hs]
    linarith
  · simp only [filteredTrajectory,if_neg hs]
    nlinarith [Real.exp_pos (-2*(t-1/2))]

theorem actual_filtered_barrier_obeys_the_source_exponential_bound
    (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (-2*t) ≤ 1-filteredTrajectory t := by
  have h := CompleteAppliedScalarTrajectories.actual_continuously_enforced_safety
    filteredTrajectory (fun s => field (filteredTrajectory s)) t
    actual_filtered_trajectory_is_C1.continuous.continuousOn
    (by rw [actual_filtered_trajectory_initial];norm_num)
    (fun s _ => actual_filtered_trajectory_ODE_at_every_time s)
    (fun s _ => min_le_right 1 (2*(1-filteredTrajectory s))) t ⟨ht,le_rfl⟩
  simpa [actual_filtered_trajectory_initial] using h.1

end SafeLearning.CompleteAppliedComparisonFilter
