import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Set Filter
open scoped Topology
namespace SafeLearning.CompleteFoundationsCosineContraction

def sourceInterval : Set ℝ := Icc (Real.cos 1) 1

theorem actual_cosine_one_positive_and_below_one :
    0<Real.cos 1 ∧ Real.cos 1<1 := by
  constructor
  · apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_gt_three]
  · have h := Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0:ℝ)≤0)
      (by linarith [Real.pi_gt_three] : (1:ℝ)≤Real.pi) (by norm_num : (0:ℝ)<1)
    simpa using h

theorem actual_sine_one_strict_contraction_range : 0<Real.sin 1 ∧ Real.sin 1<1 := by
  constructor
  · exact Real.sin_pos_of_pos_of_lt_pi (by norm_num) (by linarith [Real.pi_gt_three])
  · have h := Real.strictMonoOn_sin
      (show (1:ℝ)∈Icc (-(Real.pi/2)) (Real.pi/2) from
        ⟨by linarith [Real.pi_gt_three],by linarith [Real.pi_gt_three]⟩)
      (show Real.pi/2∈Icc (-(Real.pi/2)) (Real.pi/2) from
        ⟨by linarith [Real.pi_gt_three],le_rfl⟩)
      (by linarith [Real.pi_gt_three] : (1:ℝ)<Real.pi/2)
    simpa using h

def sourceConstant : NNReal := ⟨Real.sin 1,actual_sine_one_strict_contraction_range.1.le⟩

theorem actual_interval_closed_nonempty_and_forward_invariant :
    IsClosed sourceInterval ∧ (1:ℝ)∈sourceInterval ∧ MapsTo Real.cos sourceInterval sourceInterval := by
  refine ⟨isClosed_Icc,⟨actual_cosine_one_positive_and_below_one.2.le,le_rfl⟩,?_⟩
  intro x hx
  have hx0 : 0≤x := actual_cosine_one_positive_and_below_one.1.le.trans hx.1
  exact ⟨Real.cos_le_cos_of_nonneg_of_le_pi hx0
    (by linarith [Real.pi_gt_three]) hx.2,Real.cos_le_one x⟩

theorem actual_interval_exact_cosine_image :
    Real.cos '' sourceInterval=Icc (Real.cos 1) (Real.cos (Real.cos 1)) := by
  apply Real.continuous_cos.continuousOn.image_Icc_of_antitoneOn
    actual_cosine_one_positive_and_below_one.2.le
  intro x hx y hy hxy
  exact Real.cos_le_cos_of_nonneg_of_le_pi
    (actual_cosine_one_positive_and_below_one.1.le.trans hx.1)
    (hy.2.trans (by linarith [Real.pi_gt_three])) hxy

theorem actual_interval_derivative_bound (x : ℝ) (hx : x∈sourceInterval) :
    ‖-Real.sin x‖₊ ≤ sourceConstant := by
  apply NNReal.coe_le_coe.mpr
  change |-Real.sin x|≤Real.sin 1
  have hx0 := actual_cosine_one_positive_and_below_one.1.le.trans hx.1
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hx0
    (hx.2.trans (by linarith [Real.pi_gt_three]))
  rw [abs_neg,abs_of_nonneg hs0]
  exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_gt_three])
    (by linarith [Real.pi_gt_three]) hx.2

theorem actual_interval_lipschitz_by_mean_value :
    LipschitzOnWith sourceConstant Real.cos sourceInterval := by
  apply (convex_Icc (Real.cos 1) 1).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun x _ => Real.hasDerivAt_cos x |>.hasDerivWithinAt)
  exact actual_interval_derivative_bound

def sourceMap (x : sourceInterval) : sourceInterval :=
  ⟨Real.cos x,actual_interval_closed_nonempty_and_forward_invariant.2.2 x.prop⟩
def sourceOne : sourceInterval := ⟨1,actual_interval_closed_nonempty_and_forward_invariant.2.1⟩

instance : Nonempty sourceInterval := ⟨sourceOne⟩
instance : CompleteSpace sourceInterval :=
  actual_interval_closed_nonempty_and_forward_invariant.1.isComplete.completeSpace_coe

theorem actual_source_map_is_contraction : ContractingWith sourceConstant sourceMap := by
  constructor
  · exact actual_sine_one_strict_contraction_range.2
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    exact actual_interval_lipschitz_by_mean_value.dist_le_mul x x.prop y y.prop

def sourceFixedPoint : sourceInterval := ContractingWith.fixedPoint sourceMap actual_source_map_is_contraction

theorem actual_fixed_point_and_uniqueness :
    Real.cos (sourceFixedPoint:ℝ)=(sourceFixedPoint:ℝ) ∧
    ∀ x∈sourceInterval,Real.cos x=x → x=(sourceFixedPoint:ℝ) := by
  have hf := actual_source_map_is_contraction.fixedPoint_isFixedPt
  constructor
  · exact congrArg Subtype.val hf
  · intro x hx hfix
    have he : Function.IsFixedPt sourceMap (⟨x,hx⟩ : sourceInterval) := Subtype.ext hfix
    exact congrArg Subtype.val (actual_source_map_is_contraction.fixedPoint_unique he)

theorem actual_real_iterates_are_the_subtype_iterates (n : ℕ) :
    ((sourceMap^[n] sourceOne : sourceInterval):ℝ)=Real.cos^[n] 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
    change Real.cos (sourceMap^[n] sourceOne)=Real.cos (Real.cos^[n] 1)
    rw [ih]

theorem actual_apriori_bound_for_every_initial_point (x : sourceInterval) (n : ℕ) :
    dist (sourceMap^[n] x) sourceFixedPoint≤
      dist x (sourceMap x)*(Real.sin 1)^n/(1-Real.sin 1) :=
  actual_source_map_is_contraction.apriori_dist_iterate_fixedPoint_le x n

theorem actual_source_apriori_bound (n : ℕ) :
    |Real.cos^[n] 1-(sourceFixedPoint:ℝ)|≤
      (1-Real.cos 1)*(Real.sin 1)^n/(1-Real.sin 1) := by
  have h := actual_apriori_bound_for_every_initial_point sourceOne n
  have hdist : dist sourceOne (sourceMap sourceOne)=1-Real.cos 1 := by
    change |1-Real.cos 1|=1-Real.cos 1
    exact abs_of_nonneg (sub_nonneg.mpr actual_cosine_one_positive_and_below_one.2.le)
  rw [hdist] at h
  change |((sourceMap^[n] sourceOne : sourceInterval):ℝ)-(sourceFixedPoint:ℝ)|≤(1-Real.cos 1)*(Real.sin 1)^n/(1-Real.sin 1) at h
  simpa only [actual_real_iterates_are_the_subtype_iterates] using h


theorem actual_every_initial_iteration_converges (x : sourceInterval) :
    Tendsto (fun n => sourceMap^[n] x) atTop (𝓝 sourceFixedPoint) :=
  actual_source_map_is_contraction.tendsto_iterate_fixedPoint x

theorem actual_fixed_point_is_interior_and_has_smaller_slope :
    Real.cos 1<(sourceFixedPoint:ℝ) ∧ (sourceFixedPoint:ℝ)<1 ∧
    Real.sin (sourceFixedPoint:ℝ)<Real.sin 1 := by
  have hm := sourceFixedPoint.prop
  have hf := actual_fixed_point_and_uniqueness.1
  have hp0 := actual_cosine_one_positive_and_below_one.1.le.trans hm.1
  have hupper : (sourceFixedPoint:ℝ)<1 := by
    by_contra h
    have he : (sourceFixedPoint:ℝ)=1 := le_antisymm hm.2 (le_of_not_gt h)
    rw [he] at hf
    linarith [actual_cosine_one_positive_and_below_one.2]
  have hlower : Real.cos 1<(sourceFixedPoint:ℝ) := by
    have hh := Real.cos_lt_cos_of_nonneg_of_le_pi hp0
      (by linarith [Real.pi_gt_three] : (1:ℝ)≤Real.pi) hupper
    rwa [hf] at hh
  refine ⟨hlower,hupper,?_⟩
  exact Real.strictMonoOn_sin ⟨by linarith [Real.pi_gt_three],by linarith [Real.pi_gt_three]⟩
    ⟨by linarith [Real.pi_gt_three],by linarith [Real.pi_gt_three]⟩ hupper

theorem actual_subtype_aposteriori_previous_step_bound (x : sourceInterval) (n : ℕ) :
    dist (sourceMap^[n+1] x) sourceFixedPoint≤
      (Real.sin 1)/(1-Real.sin 1)*dist (sourceMap^[n+1] x) (sourceMap^[n] x) := by
  have h0 := actual_source_map_is_contraction.dist_fixedPoint_le (sourceMap^[n+1] x)
  have hraw := actual_source_map_is_contraction.dist_le_mul (sourceMap^[n] x) (sourceMap^[n+1] x)
  have hc : (sourceConstant:ℝ)=Real.sin 1 := rfl
  rw [hc] at hraw h0
  have hstep : dist (sourceMap^[n+1] x) (sourceMap^[n+2] x)≤
      (Real.sin 1)*dist (sourceMap^[n] x) (sourceMap^[n+1] x) := by
    simpa only [Function.iterate_succ_apply'] using hraw
  calc
    _≤dist (sourceMap^[n+1] x) (sourceMap^[n+2] x)/(1-Real.sin 1) := by
      simpa only [sourceFixedPoint,Function.iterate_succ_apply'] using h0
    _≤((Real.sin 1)*dist (sourceMap^[n] x) (sourceMap^[n+1] x))/(1-Real.sin 1) :=
      div_le_div_of_nonneg_right hstep (sub_nonneg.mpr actual_sine_one_strict_contraction_range.2.le)
    _=(Real.sin 1)/(1-Real.sin 1)*dist (sourceMap^[n+1] x) (sourceMap^[n] x) := by
      rw [dist_comm (sourceMap^[n] x)]
      ring

theorem actual_real_aposteriori_previous_step_bound (n : ℕ) :
    |Real.cos^[n+1] 1-(sourceFixedPoint:ℝ)|≤
      (Real.sin 1)/(1-Real.sin 1)*|Real.cos^[n+1] 1-Real.cos^[n] 1| := by
  have h := actual_subtype_aposteriori_previous_step_bound sourceOne n
  simpa only [Subtype.dist_eq,Real.dist_eq,actual_real_iterates_are_the_subtype_iterates] using h

theorem actual_endpoint_derivative_attains_worst_interval_slope :
    IsGreatest {r : ℝ | ∃ x∈sourceInterval,r=‖deriv Real.cos x‖} (Real.sin 1) := by
  constructor
  · refine ⟨1,actual_interval_closed_nonempty_and_forward_invariant.2.1,?_⟩
    rw [(Real.hasDerivAt_cos 1).deriv]
    simp only [norm_neg,Real.norm_eq_abs,abs_of_nonneg actual_sine_one_strict_contraction_range.1.le]
  · rintro r ⟨x,hx,rfl⟩
    rw [(Real.hasDerivAt_cos x).deriv]
    exact actual_interval_derivative_bound x hx

end SafeLearning.CompleteFoundationsCosineContraction
