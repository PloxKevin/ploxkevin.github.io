import Mathlib
import SafeLearning.CompleteFoundationsContinuousLevels22
import SafeLearning.CompleteModulesLandscapeRegularBoundaryInvariance

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Metric
open scoped Topology Gradient

namespace SafeLearning.CompleteFoundationsRegularBoundary30

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem actual_gradient_line_derivative_is_the_squared_gradient_norm
    (h : E → ℝ) (x : E) (hh : DifferentiableAt ℝ h x) :
    HasDerivAt (fun s : ℝ => h (x + s • gradient h x)) (‖gradient h x‖^2) 0 := by
  have hs : HasDerivAt (fun s : ℝ => x + s • gradient h x) (gradient h x) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (gradient h x)).const_add x
  have hh' : HasFDerivAt h (fderiv ℝ h x) (x + (0 : ℝ) • gradient h x) := by simpa using hh.hasFDerivAt
  have hd := hh'.comp_hasDerivAt (0 : ℝ) hs
  simpa only [Function.comp_def, ← inner_gradient_left, real_inner_self_eq_norm_sq] using hd

theorem actual_positive_derivative_at_a_zero_gives_negative_left_values
    (g : ℝ → ℝ) (d : ℝ) (hzero : g 0 = 0) (hd : HasDerivAt g d 0) (hpos : 0 < d) :
    ∀ᶠ s : ℝ in 𝓝[<] 0, g s < 0 := by
  have hs := hd.tendsto_slope_zero_left.eventually (Ioi_mem_nhds hpos)
  filter_upwards [hs, self_mem_nhdsWithin] with s hs hnegative
  have hslope : 0 < g s / s := by
    simpa [hzero, smul_eq_mul, div_eq_mul_inv, mul_comm] using hs
  have hn : s < 0 := hnegative
  exact (div_pos_iff.mp hslope).resolve_left (fun hp => (not_lt_of_ge hn.le) hp.2) |>.1

theorem actual_every_ball_at_a_regular_zero_has_a_negative_gradient_line_point
    (h : E → ℝ) (x : E) (hh : DifferentiableAt ℝ h x)
    (hzero : h x = 0) (hregular : gradient h x ≠ 0) (r : ℝ) (hr : 0 < r) :
    ∃ s : ℝ, s < 0 ∧ x + s • gradient h x ∈ ball x r ∧ h (x + s • gradient h x) < 0 := by
  have hp : 0 < ‖gradient h x‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hregular)
  have hn := actual_positive_derivative_at_a_zero_gives_negative_left_values
    (fun s : ℝ => h (x + s • gradient h x)) (‖gradient h x‖^2)
    (by simpa using hzero) (actual_gradient_line_derivative_is_the_squared_gradient_norm h x hh) hp
  have hcontinuous : Continuous (fun s : ℝ => x + s • gradient h x) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hc : Tendsto (fun s : ℝ => x + s • gradient h x) (𝓝 0) (𝓝 x) := by
    simpa using hcontinuous.tendsto (0 : ℝ)
  have hb := hc.eventually (ball_mem_nhds x hr)
  have hleft : ∀ᶠ s : ℝ in 𝓝[<] 0, s < 0 := self_mem_nhdsWithin
  obtain ⟨s,hs,hnegative,hball⟩ := (hleft.and (hn.and (hb.filter_mono nhdsWithin_le_nhds))).exists
  exact ⟨s,hs,hball,hnegative⟩

theorem actual_regular_zero_is_not_in_the_superlevel_interior
    (h : E → ℝ) (x : E) (hh : DifferentiableAt ℝ h x)
    (hzero : h x = 0) (hregular : gradient h x ≠ 0) :
    x ∉ interior {z | 0 ≤ h z} := by
  intro hx
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  obtain ⟨s,hs,hinside,hnegative⟩ :=
    actual_every_ball_at_a_regular_zero_has_a_negative_gradient_line_point h x hh hzero hregular r hr
  have hnonnegative : 0 ≤ h (x + s • gradient h x) := hball hinside
  exact (not_le_of_gt hnegative) hnonnegative

theorem actual_regular_zero_superlevel_frontier_and_interior_identities
    (h : E → ℝ) (hh : ContDiff ℝ 1 h)
    (hregular : ∀ x, h x = 0 → gradient h x ≠ 0) :
    frontier {x | 0 ≤ h x} = {x | h x = 0} ∧
      interior {x | 0 ≤ h x} = {x | 0 < h x} := by
  have hc : Continuous h := hh.continuous
  have hf := SafeLearning.CompleteFoundationsContinuousLevels22.actual_superlevel_frontier_is_the_closed_set_minus_interior_and_has_only_zeros h hc
  have hd : Differentiable ℝ h := hh.differentiable (by norm_num)
  have hznot : ∀ x, h x = 0 → x ∉ interior {z | 0 ≤ h z} :=
    fun x hx => actual_regular_zero_is_not_in_the_superlevel_interior h x (hd x) hx (hregular x hx)
  constructor
  · apply subset_antisymm hf.2
    intro x hx
    change h x = 0 at hx
    exact (mem_frontier_iff_notMem_interior (show x ∈ {z | 0 ≤ h z} from by change 0 ≤ h x; rw [hx])).mpr (hznot x hx)
  · apply subset_antisymm
    · intro x hx
      have hnonnegative : 0 ≤ h x := interior_subset (s := {z : E | 0 ≤ h z}) hx
      exact lt_of_le_of_ne hnonnegative (fun heq => hznot x heq.symm hx)
    · exact SafeLearning.CompleteFoundationsContinuousLevels22.actual_positive_level_is_contained_in_the_superlevel_interior h hc

theorem actual_square_nonregular_zero_has_no_safe_set_boundary :
    ContDiff ℝ 1 (fun x : ℝ => x^2) ∧
    {x : ℝ | 0 ≤ x^2} = univ ∧ frontier {x : ℝ | 0 ≤ x^2} = ∅ ∧
      (0 : ℝ)^2 = 0 ∧ gradient (fun x : ℝ => x^2) 0 = 0 := by
  have hc : {x : ℝ | 0 ≤ x^2} = univ := by ext x; simp [sq_nonneg]
  have hd : HasDerivAt (fun x : ℝ => x^2) 0 0 := by
    convert! (hasDerivAt_id' (0 : ℝ)).pow 2 using 1 <;> norm_num
  exact ⟨contDiff_id.pow 2,hc,by rw [hc]; simp,by norm_num,by rw [gradient_eq_deriv',hd.deriv]⟩

theorem actual_negative_cubic_safe_set_boundary_derivative_and_immediate_escape :
    ContDiff ℝ 1 (fun x : ℝ => -(x^3)) ∧
    {x : ℝ | 0 ≤ -(x^3)} = Iic 0 ∧
    (∀ x : ℝ, HasDerivAt (fun y : ℝ => -(y^3)) (-3*x^2) x) ∧
    gradient (fun x : ℝ => -(x^3)) 0 = 0 ∧
    (∀ t : ℝ, HasDerivAt (fun s : ℝ => s) 1 t) ∧
    (0 : ℝ) ∈ {x : ℝ | 0 ≤ -(x^3)} ∧
    ∀ t : ℝ, 0 < t → t ∉ {x : ℝ | 0 ≤ -(x^3)} := by
  have hd : ∀ x : ℝ, HasDerivAt (fun y : ℝ => -(y^3)) (-3*x^2) x := by
    intro x
    convert! ((hasDerivAt_id' x).pow 3).neg using 1 <;> simp <;> ring
  have hc : {x : ℝ | 0 ≤ -(x^3)} = Iic 0 := by
    ext x
    simpa only [mem_ofPred_eq, neg_nonneg, mem_Iic] using (show Odd (3 : ℕ) from by decide).pow_nonpos_iff
  refine ⟨(contDiff_id.pow 3).neg,hc,hd,?_,fun t => hasDerivAt_id t,by norm_num,?_⟩
  · rw [gradient_eq_deriv',(hd 0).deriv]; norm_num
  · intro t ht
    rw [hc]
    exact not_le_of_gt ht

theorem actual_continuous_path_from_a_closed_set_to_its_complement_meets_frontier
    {X : Type*} [TopologicalSpace X] (C : Set X) (_hC : IsClosed C)
    (x : ℝ → X) (a b : ℝ) (hab : a ≤ b)
    (hx : ContinuousOn x (Icc a b)) (ha : x a ∈ C) (hb : x b ∉ C) :
    ∃ t ∈ Icc a b, x t ∈ frontier C := by
  by_contra hn
  push Not at hn
  let S : Set X := x '' Icc a b
  have hconn : IsPreconnected S := isPreconnected_Icc.image x hx
  have hcover : S ⊆ interior C ∪ interior Cᶜ := by
    rintro z ⟨t,ht,rfl⟩
    exact (compl_frontier_eq_union_interior (s := C) ▸ (hn t ht))
  have hdisjoint : Disjoint (interior C) (interior Cᶜ) := by
    apply Set.disjoint_left.mpr
    intro z hz hzc
    exact (interior_subset hzc) (interior_subset hz)
  have haint : x a ∈ interior C := (mem_interior_iff_notMem_frontier ha).mpr (hn a (left_mem_Icc.mpr hab))
  have hsub := hconn.subset_left_of_subset_union isOpen_interior isOpen_interior hdisjoint hcover
    ⟨x a,⟨a,left_mem_Icc.mpr hab,rfl⟩,haint⟩
  exact hb (interior_subset (hsub ⟨b,right_mem_Icc.mpr hab,rfl⟩))

theorem actual_continuous_barrier_path_crosses_a_regular_zero_boundary
    (h : E → ℝ) (hh : ContDiff ℝ 1 h)
    (hregular : ∀ z, h z = 0 → gradient h z ≠ 0)
    (x : ℝ → E) (a b : ℝ) (hab : a ≤ b) (hx : ContinuousOn x (Icc a b))
    (ha : 0 ≤ h (x a)) (hb : h (x b) < 0) :
    ∃ t ∈ Icc a b, h (x t) = 0 ∧ x t ∈ frontier {z | 0 ≤ h z} := by
  obtain ⟨t,ht,hzero⟩ := intermediate_value_Icc' hab (hh.continuous.continuousOn.comp hx (mapsTo_univ _ _))
    (show (0 : ℝ) ∈ Icc (h (x b)) (h (x a)) from ⟨hb.le,ha⟩)
  refine ⟨t,ht,hzero,?_⟩
  rw [(actual_regular_zero_superlevel_frontier_and_interior_identities h hh hregular).1]
  exact hzero

theorem actual_global_regular_boundary_only_check_keeps_every_existing_ode_path_safe
    (F : E → E) (h : E → ℝ) (hF : LocallyLipschitzOn univ F) (hh : ContDiff ℝ 1 h)
    (hregular : ∀ z, h z = 0 → gradient h z ≠ 0)
    (hinward : ∀ z, h z = 0 → 0 ≤ inner ℝ (gradient h z) (F z))
    (x : ℝ → E) (a b : ℝ) (hx : ContinuousOn x (Icc a b))
    (hODE : ∀ t ∈ Ico a b, HasDerivWithinAt x (F (x t)) (Ici t) t)
    (hinit : 0 ≤ h (x a)) : ∀ t ∈ Icc a b, 0 ≤ h (x t) := by
  apply SafeLearning.CompleteModulesLandscapeRegularBoundaryInvariance.actual_regular_boundary_only_inward_condition_keeps_every_existing_path_safe
    F h univ isOpen_univ hF hh.contDiffOn x a b hx (mapsTo_univ _ _) hODE hinit
  · intro z hz hzero heq
    apply hregular z hzero
    rw [gradient,heq]
    exact map_zero _
  · intro z hz hzero
    simpa only [← inner_gradient_left] using hinward z hzero


theorem actual_regular_boundary_check_derives_true_forward_invariance
    (F : E → E) (h : E → ℝ) (hF : LocallyLipschitzOn univ F) (hh : ContDiff ℝ 1 h)
    (hregular : ∀ z, h z = 0 → gradient h z ≠ 0)
    (hinward : ∀ z, h z = 0 → 0 ≤ inner ℝ (gradient h z) (F z)) :
    SafeLearning.CompleteModulesLandscapeGlobalExistence.IsForwardInvariant F univ {z | 0 ≤ h z} := by
  apply SafeLearning.CompleteModulesLandscapeRegularBoundaryInvariance.actual_regular_boundary_only_inward_condition_proves_forward_invariance
    F h univ isOpen_univ hF hh.contDiffOn
  · intro z hz hzero heq
    apply hregular z hzero
    rw [gradient,heq]
    exact map_zero _
  · intro z hz hzero
    simpa only [← inner_gradient_left] using hinward z hzero

theorem actual_negative_cubic_boundary_check_is_satisfied_but_the_true_path_escapes :
    frontier {x : ℝ | 0 ≤ -(x^3)} = {0} ∧
      (∀ x ∈ frontier {x : ℝ | 0 ≤ -(x^3)}, 0 ≤ (-3*x^2) * 1) ∧
      (∀ t : ℝ, HasDerivAt (fun s : ℝ => s) 1 t) ∧
      (∀ t : ℝ, 0 < t → -(t^3) < 0) := by
  have hc := actual_negative_cubic_safe_set_boundary_derivative_and_immediate_escape.2.1
  have hf : frontier {x : ℝ | 0 ≤ -(x^3)} = {0} := by rw [hc]; exact frontier_Iic
  refine ⟨hf,?_,fun t => hasDerivAt_id t,?_⟩
  · intro x hx
    rw [hf] at hx
    have hx0 : x = 0 := mem_singleton_iff.mp hx
    rw [hx0]; norm_num
  · intro t ht
    exact neg_neg_of_pos (pow_pos ht 3)

end SafeLearning.CompleteFoundationsRegularBoundary30
