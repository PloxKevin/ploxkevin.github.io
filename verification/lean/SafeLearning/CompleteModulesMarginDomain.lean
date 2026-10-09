import SafeLearning.CompleteModulesMarginCorollaries

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
namespace SafeLearning.CompleteModulesMarginDomain
open CompleteModulesGeneralMargin CompleteModulesMarginCorollaries
variable {O X : Type*} [Fintype O] [DecidableEq O] [PseudoMetricSpace X]

theorem actual_at_least_two_classes_iff_nonempty_competitors (winner : O) :
    2 ≤ Fintype.card O ↔ (Finset.univ.erase winner).Nonempty := by
  rw [← Finset.card_pos,Finset.card_erase_of_mem (Finset.mem_univ winner),Finset.card_univ]
  omega

theorem actual_nonnegative_logit_bound_can_be_replaced_by_positive_bound
    (logits : X → O → ℝ) (gain : ℝ) (hgain : 0 ≤ gain)
    (hbound : ∀ first second,‖WithLp.toLp 2 (logits first-logits second)‖ ≤ gain*dist first second) :
    ∃ positiveGain : ℝ,0 < positiveGain ∧
      ∀ first second,‖WithLp.toLp 2 (logits first-logits second)‖ ≤ positiveGain*dist first second := by
  refine ⟨gain+1,by linarith,?_⟩
  intro first second
  exact (hbound first second).trans
    (mul_le_mul_of_nonneg_right (by linarith) (dist_nonneg (x := first) (y := second)))

theorem actual_nonnegative_pair_gap_bound_can_be_replaced_by_positive_bound
    (logits : X → O → ℝ) (winner other : O) (gain : ℝ) (hgain : 0 ≤ gain)
    (hbound : ∀ first second,
      |(logits first winner-logits first other)-(logits second winner-logits second other)| ≤ gain*dist first second) :
    ∃ positiveGain : ℝ,0 < positiveGain ∧
      ∀ first second,
        |(logits first winner-logits first other)-(logits second winner-logits second other)| ≤ positiveGain*dist first second := by
  refine ⟨gain+1,by linarith,?_⟩
  intro first second
  exact (hbound first second).trans
    (mul_le_mul_of_nonneg_right (by linarith) (dist_nonneg (x := first) (y := second)))

theorem actual_zero_pair_gap_bound_makes_gap_constant
    (logits : X → O → ℝ) (winner other : O)
    (hbound : ∀ first second,
      |(logits first winner-logits first other)-(logits second winner-logits second other)| ≤ 0)
    (first second : X) :
    logits first winner-logits first other=logits second winner-logits second other := by
  have h := abs_eq_zero.mp (le_antisymm (hbound first second) (abs_nonneg _))
  linarith

end SafeLearning.CompleteModulesMarginDomain
