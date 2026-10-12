import SafeLearning.CompleteFoundationsNormExercises

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace SafeLearning.CompleteFoundationsLiteralNormComparisonProof29
open CompleteFoundationsNormDuality CompleteFoundationsNormExercises
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem actual_each_coordinate_square_is_at_most_the_sum (x : I → ℝ) (i : I) :
    (x i)^2 ≤ ∑ j,(x j)^2 := by
  exact Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)

theorem actual_sum_square_expansion_and_nonnegative_cross_terms (x : I → ℝ) :
    (∀ i j,0 ≤ |x i| *|x j|) ∧
    (∑ i,|x i|)^2=(∑ i,∑ j,|x i| *|x j|) ∧
    (∑ i,(x i)^2) ≤ (∑ i,|x i|)^2 := by
  refine ⟨fun i j => mul_nonneg (abs_nonneg _) (abs_nonneg _),?_,?_⟩
  · simp [pow_two,Finset.sum_mul,Finset.mul_sum]
  · calc
      ∑ i,(x i)^2 = ∑ i,|x i| *|x i| := by simp [←pow_two,sq_abs]
      _ ≤ ∑ i,|x i| *(∑ j,|x j|) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left
          (Finset.single_le_sum (fun j _ => abs_nonneg (x j)) (Finset.mem_univ i))
          (abs_nonneg (x i))
      _ = (∑ i,|x i|)^2 := by rw [←Finset.sum_mul,pow_two]

theorem actual_sum_squares_at_most_dimension_times_max_square (x : I → ℝ) :
    (∑ i,(x i)^2) ≤ (Fintype.card I:ℝ)*‖x‖^2 := by
  calc
    ∑ i,(x i)^2 ≤ ∑ _i:I,‖x‖^2 := by
      apply Finset.sum_le_sum
      intro i _
      have h : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
      nlinarith [abs_nonneg (x i),norm_nonneg x,sq_abs (x i)]
    _ = (Fintype.card I:ℝ)*‖x‖^2 := by simp

theorem actual_max_coordinate_square_is_the_infinity_norm_square [Nonempty I]
    (x : I → ℝ) : ∃ j,(x j)^2=‖x‖^2 ∧ ∀ i,(x i)^2 ≤ (x j)^2 := by
  obtain ⟨j,hj⟩ := actual_largest_absolute_coordinate_exists x
  refine ⟨j,?_,?_⟩
  · rw [←hj,sq_abs]
  · intro i
    have h : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
    rw [←hj] at h
    nlinarith [abs_nonneg (x i),abs_nonneg (x j),sq_abs (x i),sq_abs (x j)]

theorem actual_printed_absolute_coordinate_and_ones_cauchy_schwarz (x : I → ℝ) :
    ⟪euclidean (fun i => |x i|),euclidean (fun _:I => (1:ℝ))⟫=∑ i,|x i| ∧
    ‖euclidean (fun _:I => (1:ℝ))‖=Real.sqrt (Fintype.card I) ∧
    ∑ i,|x i| ≤ l2Norm x * Real.sqrt (Fintype.card I) := by
  have hip : ⟪euclidean (fun i => |x i|),euclidean (fun _:I => (1:ℝ))⟫=∑ i,|x i| := by
    rw [actual_euclidean_pairing_is_dot]
    simp [dotProduct]
  have hone : ‖euclidean (fun _:I => (1:ℝ))‖=Real.sqrt (Fintype.card I) := by
    simpa only [l2Norm,mul_one] using
      (actual_constant_vector_attains_dimension_conversion (n:=I) 1 (by norm_num))
  have habs : ‖euclidean (fun i => |x i|)‖=l2Norm x := by
    simp [euclidean,l2Norm,EuclideanSpace.norm_eq,Real.norm_eq_abs,sq_abs]
  refine ⟨hip,hone,?_⟩
  have h:=abs_real_inner_le_norm (euclidean (fun i => |x i|))
    (euclidean (fun _:I => (1:ℝ)))
  rw [hip,abs_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg (x i)),habs,hone] at h
  exact h

theorem actual_full_norm_comparison_bounds (x : I → ℝ) :
    ‖x‖ ≤ l2Norm x ∧ l2Norm x ≤ l1Norm x ∧
    l1Norm x ≤ Real.sqrt (Fintype.card I)*l2Norm x ∧
    l2Norm x ≤ Real.sqrt (Fintype.card I)*‖x‖ ∧
    l1Norm x ≤ (Fintype.card I:ℝ)*‖x‖ := by
  refine ⟨actual_infinity_norm_at_most_euclidean_norm x,
    actual_euclidean_norm_at_most_one_norm x,
    actual_one_norm_at_most_dimension_factor_euclidean_norm x,
    actual_infinity_ball_in_euclidean_ball x ‖x‖ (norm_nonneg _) le_rfl,?_⟩
  rw [actual_l1_norm_is_sum_absolute_values]
  calc
    ∑ i,|x i| ≤ ∑ _i:I,‖x‖ := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
    _ = (Fintype.card I:ℝ)*‖x‖ := by simp

def printedComparisonVector : Fin 3 → ℝ := ![3,-4,12]

theorem actual_printed_vector_has_exact_norms_and_square_sums :
    ‖printedComparisonVector‖=12 ∧ l2Norm printedComparisonVector=13 ∧
    l1Norm printedComparisonVector=19 ∧
    (∑ i,(printedComparisonVector i)^2)=169 ∧
    (∑ i,|printedComparisonVector i|)^2=361 := by
  have hinf : ‖printedComparisonVector‖=12 := by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 12)).mpr
      intro i
      fin_cases i <;> norm_num [printedComparisonVector]
    · simpa [printedComparisonVector] using norm_le_pi_norm printedComparisonVector (2:Fin 3)
  have htwo : l2Norm printedComparisonVector=13 := by
    have hs : l2Norm printedComparisonVector^2=169 := by
      norm_num [actual_l2_norm_squared,printedComparisonVector,Fin.sum_univ_succ]
    have hp : 0 ≤ l2Norm printedComparisonVector := norm_nonneg _
    nlinarith
  refine ⟨hinf,htwo,?_,?_,?_⟩
  all_goals norm_num [actual_l1_norm_is_sum_absolute_values,printedComparisonVector,Fin.sum_univ_succ]

theorem actual_printed_numeric_chain_and_nearest_tenth :
    (12:ℝ) ≤ 13 ∧ (13:ℝ) ≤ 19 ∧ (19:ℝ) ≤ 13*Real.sqrt 3 ∧
    |13*Real.sqrt 3-22.5| < 0.05 := by
  have hs:=Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have hp:=Real.sqrt_nonneg (3:ℝ)
  refine ⟨by norm_num,by norm_num,by nlinarith,?_⟩
  apply abs_lt.mpr
  constructor <;> nlinarith
end SafeLearning.CompleteFoundationsLiteralNormComparisonProof29
