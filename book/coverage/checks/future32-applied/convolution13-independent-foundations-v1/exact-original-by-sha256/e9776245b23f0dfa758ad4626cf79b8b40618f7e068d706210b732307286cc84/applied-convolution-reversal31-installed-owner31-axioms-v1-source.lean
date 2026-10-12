import Mathlib
import SafeLearning.CompleteAppliedExerciseModels

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SafeLearning.CompleteAppliedConvolutionReversalBridge31

/-- The actual finite kernel reversal, not a definition of convolution. -/
def reverseKernel {k : ℕ} (w : Fin k → ℝ) : Fin k → ℝ := fun j => w j.rev

/-- Positive tap offsets, the neural-network cross-correlation convention. -/
def correlationAt {k : ℕ} (x : ℤ → ℝ) (w : Fin k → ℝ) (d t : ℤ) : ℝ :=
  ∑ j, w j * x (t + d * (j.val : ℤ))

/-- Negative tap offsets, the mathematical convolution convention. -/
def convolutionAt {k : ℕ} (x : ℤ → ℝ) (w : Fin k → ℝ) (d t : ℤ) : ℝ :=
  ∑ j, w j * x (t - d * (j.val : ℤ))

theorem actual_reverse_kernel_is_an_involution {k : ℕ} (w : Fin k → ℝ) :
    reverseKernel (reverseKernel w) = w := by
  funext j
  simp [reverseKernel]

theorem actual_reversed_tap_has_the_opposite_finite_index {k : ℕ} (j : Fin k) :
    (j.rev.val : ℤ) = (k : ℤ) - 1 - j.val := by
  simp only [Fin.rev]
  omega

/-- Reindexing an actual finite sum proves the convention bridge. The right edge
is translated by d*(k-1); no kernel symmetry or assumed bridge is needed. -/
theorem actual_finite_convolution_is_correlation_with_the_reversed_kernel
    {k : ℕ} (x : ℤ → ℝ) (w : Fin k → ℝ) (d t : ℤ) :
    convolutionAt x w d (t + d * ((k : ℤ) - 1)) =
      correlationAt x (reverseKernel w) d t := by
  unfold convolutionAt correlationAt reverseKernel
  apply Fintype.sum_equiv (Fin.revPerm : Fin k ≃ Fin k)
  intro j
  simp only [Fin.revPerm_apply, Fin.rev_rev]
  congr 2
  rw [actual_reversed_tap_has_the_opposite_finite_index]
  ring

theorem actual_finite_correlation_is_convolution_with_the_reversed_kernel
    {k : ℕ} (x : ℤ → ℝ) (w : Fin k → ℝ) (d t : ℤ) :
    correlationAt x w d t =
      convolutionAt x (reverseKernel w) d (t + d * ((k : ℤ) - 1)) := by
  rw [actual_finite_convolution_is_correlation_with_the_reversed_kernel,
    actual_reverse_kernel_is_an_involution]

/-- Stride selects starting positions and does not change which taps reverse. -/
theorem actual_stride_dilation_and_bias_preserve_the_reversal_bridge
    {k : ℕ} (x : ℤ → ℝ) (w : Fin k → ℝ) (d s p b : ℤ) (bias : ℝ) :
    (fun i : ℤ => convolutionAt x w d (s*i-p+d*((k:ℤ)-1)) + bias) =
      (fun i : ℤ => correlationAt x (reverseKernel w) d (s*i-p) + bias) := by
  funext i
  rw [actual_finite_convolution_is_correlation_with_the_reversed_kernel]

def forwardWindowIndex {n k : ℕ} (i : Fin (n+1)) (j : Fin (k+1)) :
    Fin (n+k+1) := ⟨i.val+j.val, by omega⟩

def backwardWindowIndex {n k : ℕ} (i : Fin (n+1)) (j : Fin (k+1)) :
    Fin (n+k+1) := ⟨i.val+k-j.val, by omega⟩

/-- Both maps use the same finite input and have exactly n+1 valid windows. -/
def validCorrelation {n k : ℕ} (x : Fin (n+k+1) → ℝ) (w : Fin (k+1) → ℝ) :
    Fin (n+1) → ℝ := fun i => ∑ j, w j * x (forwardWindowIndex i j)

/-- The convolution value is evaluated at the right edge i+k of each window. -/
def validConvolution {n k : ℕ} (x : Fin (n+k+1) → ℝ) (w : Fin (k+1) → ℝ) :
    Fin (n+1) → ℝ := fun i => ∑ j, w j * x (backwardWindowIndex i j)

theorem actual_forward_and_backward_window_indices_agree_after_reversal
    {n k : ℕ} (i : Fin (n+1)) (j : Fin (k+1)) :
    forwardWindowIndex i j.rev = backwardWindowIndex i j := by
  apply Fin.ext
  simp only [forwardWindowIndex, backwardWindowIndex, Fin.rev]
  omega

theorem actual_full_finite_valid_window_reversal_bridge
    {n k : ℕ} (x : Fin (n+k+1) → ℝ) (w : Fin (k+1) → ℝ) :
    validConvolution x w = validCorrelation x (reverseKernel w) := by
  funext i
  unfold validConvolution validCorrelation reverseKernel
  apply Fintype.sum_equiv (Fin.revPerm : Fin (k+1) ≃ Fin (k+1))
  intro j
  simp only [Fin.revPerm_apply, Fin.rev_rev]
  rw [actual_forward_and_backward_window_indices_agree_after_reversal]

theorem actual_full_finite_valid_window_reverse_bridge
    {n k : ℕ} (x : Fin (n+k+1) → ℝ) (w : Fin (k+1) → ℝ) :
    validCorrelation x w = validConvolution x (reverseKernel w) := by
  rw [actual_full_finite_valid_window_reversal_bridge,
    actual_reverse_kernel_is_an_involution]

/-- Both maps use the one kernel w at every output position. -/
theorem actual_shared_kernel_and_finite_dimensions
    {n k : ℕ} (x : Fin (n+k+1) → ℝ) (w : Fin (k+1) → ℝ) :
    (∀ i : Fin (n+1), validCorrelation x w i =
      ∑ j : Fin (k+1), w j * x (forwardWindowIndex i j)) ∧
    (∀ i : Fin (n+1), validConvolution x w i =
      ∑ j : Fin (k+1), w j * x (backwardWindowIndex i j)) ∧
    Fintype.card (Fin (n+k+1)) = n+k+1 ∧ Fintype.card (Fin (n+1)) = n+1 := by
  simp [validCorrelation, validConvolution]

theorem actual_printed_kernel_reversal :
    reverseKernel (![1,-1] : Fin 2 → ℝ) = ![-1,1] := by
  ext j; fin_cases j <;> norm_num [reverseKernel, Fin.rev]

theorem actual_printed_correlation_is_the_given_three_by_four_matrix
    (x : Fin 4 → ℝ) :
    validCorrelation (n:=2) (k:=1) x ![1,-1] =
      SafeLearning.CompleteAppliedExercises.correlationMatrix.mulVec x := by
  rw [SafeLearning.CompleteAppliedExerciseModels.correlation_arbitrary_window]
  ext i; fin_cases i <;>
    simp [validCorrelation, forwardWindowIndex, Fin.sum_univ_succ] <;> ring

theorem actual_printed_mathematical_convolution_reverses_the_matrix_orientation
    (x : Fin 4 → ℝ) :
    validConvolution (n:=2) (k:=1) x ![1,-1] = ![x 1-x 0,x 2-x 1,x 3-x 2] ∧
    validConvolution (n:=2) (k:=1) x ![-1,1] =
      SafeLearning.CompleteAppliedExercises.correlationMatrix.mulVec x := by
  constructor
  · ext i; fin_cases i <;>
      simp [validConvolution, backwardWindowIndex, Fin.sum_univ_succ] <;> ring
  · rw [← actual_printed_kernel_reversal,
      ← actual_full_finite_valid_window_reverse_bridge,
      actual_printed_correlation_is_the_given_three_by_four_matrix]

theorem actual_printed_example_conventions_give_distinct_outputs :
    validCorrelation (n:=2) (k:=1) (![1,2,3,4] : Fin 4 → ℝ) ![1,-1] = ![-1,-1,-1] ∧
    validConvolution (n:=2) (k:=1) (![1,2,3,4] : Fin 4 → ℝ) ![1,-1] = ![1,1,1] ∧
    validConvolution (n:=2) (k:=1) (![1,2,3,4] : Fin 4 → ℝ) ![-1,1] = ![-1,-1,-1] ∧
    Fintype.card (Fin 4) = 4 ∧ Fintype.card (Fin 3) = 3 := by
  rw [actual_printed_correlation_is_the_given_three_by_four_matrix,
    SafeLearning.CompleteAppliedExercises.correlation_matrix_output]
  have h := actual_printed_mathematical_convolution_reverses_the_matrix_orientation
    (![1,2,3,4] : Fin 4 → ℝ)
  rw [h.1, h.2, SafeLearning.CompleteAppliedExercises.correlation_matrix_output]
  norm_num

end SafeLearning.CompleteAppliedConvolutionReversalBridge31

#print axioms SafeLearning.CompleteAppliedConvolutionReversalBridge31.actual_reverse_kernel_is_an_involution
#print axioms SafeLearning.CompleteAppliedConvolutionReversalBridge31.actual_reversed_tap_has_the_opposite_finite_index
#print axioms SafeLearning.CompleteAppliedConvolutionReversalBridge31.actual_finite_convolution_is_correlation_with_the_reversed_kernel
#print axioms SafeLearning.CompleteAppliedConvolutionReversalBridge31.actual_finite_correlation_is_convolution_with_the_reversed_kernel
#print axioms SafeLearning.CompleteAppliedConvolutionReversalBridge31.actual_stride_dilation_and_bias_preserve_the_reversal_bridge
#print axioms SafeLearning.CompleteAppliedConvolutionReversalBridge31.actual_forward_and_backward_window_indices_agree_after_reversal
#print axioms SafeLearning.CompleteAppliedConvolutionReversalBridge31.actual_full_finite_valid_window_reversal_bridge
#print axioms SafeLearning.CompleteAppliedConvolutionReversalBridge31.actual_full_finite_valid_window_reverse_bridge
#print axioms SafeLearning.CompleteAppliedConvolutionReversalBridge31.actual_shared_kernel_and_finite_dimensions
#print axioms SafeLearning.CompleteAppliedConvolutionReversalBridge31.actual_printed_kernel_reversal
#print axioms SafeLearning.CompleteAppliedConvolutionReversalBridge31.actual_printed_correlation_is_the_given_three_by_four_matrix
#print axioms SafeLearning.CompleteAppliedConvolutionReversalBridge31.actual_printed_mathematical_convolution_reverses_the_matrix_orientation
#print axioms SafeLearning.CompleteAppliedConvolutionReversalBridge31.actual_printed_example_conventions_give_distinct_outputs
