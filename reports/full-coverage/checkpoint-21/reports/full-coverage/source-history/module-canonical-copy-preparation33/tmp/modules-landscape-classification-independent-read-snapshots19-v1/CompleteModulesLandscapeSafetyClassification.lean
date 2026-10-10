import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteModulesLandscapeSafetyClassification

def sourceClip (x : ℝ) : ℝ := max (-3/20) (min (3/20) (30*x))

theorem actual_source_clipped_steep_function_has_the_printed_range (x : ℝ) :
    sourceClip x ∈ Icc (-3/20 : ℝ) (3/20) := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem actual_source_clipped_steep_function_moves_at_most_point_three_everywhere
    (x y : ℝ) : |sourceClip x-sourceClip y| ≤ (3/10 : ℝ) := by
  have hx := actual_source_clipped_steep_function_has_the_printed_range x
  have hy := actual_source_clipped_steep_function_has_the_printed_range y
  rw [abs_le]
  constructor <;> linarith [hx.1,hx.2,hy.1,hy.2]

theorem actual_source_clipped_steep_function_is_globally_thirty_lipschitz :
    LipschitzWith 30 sourceClip := by
  have hm : LipschitzWith 30 (fun x : ℝ => 30*x) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    simp only [Real.dist_eq, ← mul_sub, abs_mul]
    norm_num
  exact (hm.const_min (3/20)).const_max (-3/20)

theorem actual_source_clipped_function_literal_unsaturated_secant :
    sourceClip 0=0 ∧ sourceClip (1/1000 : ℝ)=3/100 ∧
    |sourceClip (1/1000 : ℝ)-sourceClip 0|=30*|(1/1000 : ℝ)-0| := by
  norm_num [sourceClip]

theorem actual_source_clipped_function_has_least_global_lipschitz_constant_thirty
    (L : NNReal) : LipschitzWith L sourceClip ↔ 30 ≤ L := by
  constructor
  · intro h
    have hb := h.dist_le_mul (1/1000 : ℝ) 0
    norm_num [sourceClip,Real.dist_eq] at hb
    exact_mod_cast (show (30 : ℝ) ≤ L by linarith)
  · intro h
    exact actual_source_clipped_steep_function_is_globally_thirty_lipschitz.weaken h

theorem actual_point_three_output_certificate_on_radius_point_one_does_not_force_gain_three :
    (∀ x y : ℝ, |x-y| ≤ (1/10 : ℝ) → |sourceClip x-sourceClip y| ≤ 3/10) ∧
    ¬LipschitzWith 3 sourceClip := by
  constructor
  · intro x y _
    exact actual_source_clipped_steep_function_moves_at_most_point_three_everywhere x y
  · rw [actual_source_clipped_function_has_least_global_lipschitz_constant_thirty]
    norm_num

theorem actual_global_gain_three_implies_the_printed_local_output_certificate
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (f : X → Y) (L : NNReal) (hL : L ≤ 3) (hf : LipschitzWith L f)
    (x y : X) (hxy : dist x y ≤ (1/10 : ℝ)) :
    dist (f x) (f y) ≤ (3/10 : ℝ) := by
  have hbound := hf.dist_le_mul x y
  have hreal : (L : ℝ) ≤ 3 := by exact_mod_cast hL
  have hn := dist_nonneg (x:=x) (y:=y)
  calc
    dist (f x) (f y) ≤ (L : ℝ)*dist x y := hbound
    _ ≤ 3*dist x y := mul_le_mul_of_nonneg_right hreal hn
    _ ≤ 3/10 := by linarith

end SafeLearning.CompleteModulesLandscapeSafetyClassification
