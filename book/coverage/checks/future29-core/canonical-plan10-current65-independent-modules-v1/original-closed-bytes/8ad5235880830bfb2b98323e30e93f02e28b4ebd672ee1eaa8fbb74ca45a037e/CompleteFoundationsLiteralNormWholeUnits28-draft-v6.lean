import SafeLearning.CompleteFoundationsNormExercises
import Mathlib.Analysis.Normed.Module.Convex

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Set
open scoped BigOperators ENNReal

namespace SafeLearning.CompleteFoundationsLiteralNorm28
open CompleteFoundationsNormDuality

section Finite
variable {I : Type*} [Fintype I] [DecidableEq I]

def sourcePNorm (p : ℝ≥0∞) (x : I → ℝ) : ℝ :=
  ‖(WithLp.toLp p x : PiLp p (fun _ : I => ℝ))‖

theorem actual_every_source_p_norm_has_all_three_norm_axioms (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (x y : I → ℝ) (a : ℝ) :
    (sourcePNorm p x=0 ↔ x=0) ∧
    sourcePNorm p (a • x)=|a| * sourcePNorm p x ∧
    sourcePNorm p (x+y) ≤ sourcePNorm p x+sourcePNorm p y := by
  refine ⟨by simp [sourcePNorm],?_,?_⟩
  · simp [sourcePNorm,norm_smul,Real.norm_eq_abs]
  · simpa [sourcePNorm] using
      norm_add_le (WithLp.toLp p x : PiLp p (fun _ : I => ℝ)) (WithLp.toLp p y)

theorem actual_all_finite_source_p_norms_have_the_printed_rpow_formula (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (hp : p≠∞) (x : I → ℝ) :
    sourcePNorm p x=(∑ i,|x i|^p.toReal)^(1/p.toReal) := by
  simpa only [sourcePNorm,Real.norm_eq_abs,PiLp.toLp_apply] using
    PiLp.norm_eq_sum (p.toReal_pos_iff_ne_top.mpr hp)
      (WithLp.toLp p x : PiLp p (fun _ : I => ℝ))

theorem actual_infinity_source_norm_is_the_coordinate_supremum (x : I → ℝ) :
    sourcePNorm ∞ x=‖x‖ ∧ sourcePNorm ∞ x=⨆ i,|x i| := by
  refine ⟨PiLp.norm_toLp x,?_⟩
  simpa only [sourcePNorm,Real.norm_eq_abs,PiLp.toLp_apply] using
    PiLp.norm_eq_ciSup (WithLp.toLp ∞ x : PiLp ∞ (fun _ : I => ℝ))

theorem actual_infinity_source_norm_attains_the_coordinate_maximum [Nonempty I]
    (x : I → ℝ) : ∃ i : I, sourcePNorm ∞ x=|x i| ∧ ∀ j,|x j| ≤ |x i| := by
  obtain ⟨i,hi,hm⟩ := Finset.exists_max_image Finset.univ (fun j : I => |x j|)
    Finset.univ_nonempty
  have hmax : ∀ j,|x j| ≤ |x i| := fun j => hm j (Finset.mem_univ j)
  refine ⟨i,?_,hmax⟩
  rw [(actual_infinity_source_norm_is_the_coordinate_supremum x).1]
  apply le_antisymm
  · exact (pi_norm_le_iff_of_nonneg (abs_nonneg (x i))).mpr
      (fun j => by simpa only [Real.norm_eq_abs] using hmax j)
  · simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i

theorem actual_one_source_norm_is_sum_absolute_values (x : I → ℝ) :
    sourcePNorm 1 x=∑ i,|x i| := by
  simpa only [sourcePNorm,Real.norm_eq_abs,PiLp.toLp_apply] using
    PiLp.norm_eq_of_L1 (WithLp.toLp 1 x : PiLp 1 (fun _ : I => ℝ))

theorem actual_nonnegative_vector_has_source_one_norm_equal_to_sum (x : I → ℝ)
    (hx : ∀ i,0 ≤ x i) : sourcePNorm 1 x=∑ i,x i := by
  rw [actual_one_source_norm_is_sum_absolute_values]
  apply Finset.sum_congr rfl
  intro i hi
  exact abs_of_nonneg (hx i)

theorem actual_euclidean_source_two_norm_equals_the_selected_euclidean_norm (x : I → ℝ) :
    sourcePNorm 2 x=l2Norm x := rfl

theorem actual_source_unit_ball_is_convex_for_every_p (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Convex ℝ {x : I → ℝ | sourcePNorm p x ≤ 1} := by
  intro x hx y hy a b ha hb hab
  change sourcePNorm p (a • x+b • y) ≤ 1
  have ht := (actual_every_source_p_norm_has_all_three_norm_axioms p (a • x) (b • y) 1).2.2
  have hax := (actual_every_source_p_norm_has_all_three_norm_axioms p x y a).2.1
  have hby := (actual_every_source_p_norm_has_all_three_norm_axioms p y x b).2.1
  rw [hax,hby,abs_of_nonneg ha,abs_of_nonneg hb] at ht
  calc
    sourcePNorm p (a • x+b • y) ≤ a*sourcePNorm p x+b*sourcePNorm p y := ht
    _  ≤  a*1+b*1 := add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
    _ = 1 := by nlinarith

theorem actual_source_unit_ball_is_symmetric_for_every_p (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (x : I → ℝ) : sourcePNorm p (-x)=sourcePNorm p x ∧
    ((-x)∈{y : I → ℝ | sourcePNorm p y ≤ 1} ↔ x∈{y : I → ℝ | sourcePNorm p y ≤ 1}) := by
  have h : sourcePNorm p (-x)=sourcePNorm p x := by simp [sourcePNorm]
  exact ⟨h,by simp only [mem_setOf_eq,h]⟩

theorem actual_source_unit_balls_have_the_printed_nesting :
    {x : I → ℝ | sourcePNorm 1 x ≤ 1}⊆{x | sourcePNorm 2 x ≤ 1} ∧
    {x : I → ℝ | sourcePNorm 2 x ≤ 1}⊆{x | sourcePNorm ∞ x ≤ 1} := by
  constructor
  · intro x hx
    change l2Norm x ≤ 1
    have h := CompleteFoundationsNormExercises.actual_euclidean_norm_at_most_one_norm x
    exact h.trans hx
  · intro x hx
    change sourcePNorm ∞ x ≤ 1
    rw [(actual_infinity_source_norm_is_the_coordinate_supremum x).1]
    exact (CompleteFoundationsNormExercises.actual_infinity_norm_at_most_euclidean_norm x).trans hx

theorem actual_source_p_norm_unit_ball_is_exactly_a_norm_closed_ball (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (x : I → ℝ) :
    sourcePNorm p x ≤ 1 ↔
      (WithLp.toLp p x : PiLp p (fun _ : I => ℝ))∈Metric.closedBall 0 1 := by
  simp only [Metric.mem_closedBall,dist_zero_right,sourcePNorm]
end Finite

def sourceExample : Fin 2 → ℝ := ![3,-4]

theorem actual_printed_vector_has_one_norm_seven : sourcePNorm 1 sourceExample=7 := by
  rw [actual_one_source_norm_is_sum_absolute_values]
  norm_num [sourceExample,Fin.sum_univ_two]

theorem actual_printed_vector_has_two_norm_five : sourcePNorm 2 sourceExample=5 := by
  rw [actual_euclidean_source_two_norm_equals_the_selected_euclidean_norm]
  have hs := actual_l2_norm_squared sourceExample
  norm_num [sourceExample,Fin.sum_univ_two] at hs
  have hn : 0 ≤ l2Norm sourceExample := norm_nonneg _
  have hsq : l2Norm sourceExample^2=25 := hs
  nlinarith [hsq]

theorem actual_printed_vector_has_infinity_norm_four : sourcePNorm ∞ sourceExample=4 := by
  rw [(actual_infinity_source_norm_is_the_coordinate_supremum sourceExample).1]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 4)).mpr
    intro i
    fin_cases i <;> norm_num [sourceExample]
  · have h := norm_le_pi_norm sourceExample 1
    norm_num [sourceExample] at h
    exact h

theorem actual_two_dimensional_one_ball_is_the_printed_diamond :
    {x : Fin 2 → ℝ | sourcePNorm 1 x ≤ 1}={x | |x 0|+|x 1| ≤ 1} := by
  ext x
  simp [actual_one_source_norm_is_sum_absolute_values,Fin.sum_univ_two]

theorem actual_two_dimensional_two_ball_is_the_printed_disc :
    {x : Fin 2 → ℝ | sourcePNorm 2 x ≤ 1}={x | (x 0)^2+(x 1)^2 ≤ 1} := by
  ext x
  change l2Norm x ≤ 1 ↔ (x 0)^2+(x 1)^2 ≤ 1
  have hs := actual_l2_norm_squared x
  simp only [Fin.sum_univ_two] at hs
  have hn : 0 ≤ l2Norm x := norm_nonneg _
  constructor <;> intro h <;> nlinarith

theorem actual_two_dimensional_infinity_ball_is_the_printed_square :
    {x : Fin 2 → ℝ | sourcePNorm ∞ x ≤ 1}={x | |x 0| ≤ 1 ∧ |x 1| ≤ 1} := by
  ext x
  change sourcePNorm ∞ x ≤ 1 ↔ |x 0| ≤ 1 ∧ |x 1| ≤ 1
  rw [(actual_infinity_source_norm_is_the_coordinate_supremum x).1]
  constructor
  · intro h
    exact ⟨(by simpa only [Real.norm_eq_abs] using (norm_le_pi_norm x 0).trans h),
      (by simpa only [Real.norm_eq_abs] using (norm_le_pi_norm x 1).trans h)⟩
  · rintro ⟨h0,h1⟩
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
    simpa only [Real.norm_eq_abs, Fin.forall_fin_two] using And.intro h0 h1

end SafeLearning.CompleteFoundationsLiteralNorm28
