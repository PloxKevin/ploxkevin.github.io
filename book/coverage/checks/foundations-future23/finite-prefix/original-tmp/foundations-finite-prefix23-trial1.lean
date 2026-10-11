import SafeLearning.CompleteFoundationsSequences

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter
open scoped Topology

namespace SafeLearning.CompleteFoundationsFinitePrefix23

/-- The printed sequence really has distinct even/odd limiting values. -/
theorem printed_additive_sequence_even_and_odd_limits :
    Tendsto (fun n => SafeLearning.CompleteFoundationsSequences.additiveAlternation (2*n))
      atTop (𝓝 (1 : ℝ)) ∧
    Tendsto (fun n => SafeLearning.CompleteFoundationsSequences.additiveAlternation (2*n+1))
      atTop (𝓝 (-1 : ℝ)) :=
  SafeLearning.CompleteFoundationsSequences.additive_alternation_subsequences

/-- Removing any fixed finite initial segment changes no extended limit superior. -/
theorem any_extended_limsup_is_unchanged_by_removing_a_finite_beginning
    (a : ℕ → EReal) (N : ℕ) :
    limsup (fun n => a (n+N)) atTop = limsup a atTop :=
  limsup_nat_add a N

/-- The corresponding lower limit ignores every fixed finite initial segment. -/
theorem any_extended_liminf_is_unchanged_by_removing_a_finite_beginning
    (a : ℕ → EReal) (N : ℕ) :
    liminf (fun n => a (n+N)) atTop = liminf a atTop :=
  liminf_nat_add a N

/-- Arbitrary values in a finite prefix cannot alter an extended limit superior. -/
theorem any_extended_limsup_is_unchanged_by_replacing_a_finite_beginning
    (a b : ℕ → EReal) (N : ℕ) (h : ∀ n ≥ N, a n = b n) :
    limsup a atTop = limsup b atTop := by
  apply limsup_congr
  exact eventually_atTop.mpr ⟨N,h⟩

/-- Arbitrary values in a finite prefix cannot alter an extended limit inferior. -/
theorem any_extended_liminf_is_unchanged_by_replacing_a_finite_beginning
    (a b : ℕ → EReal) (N : ℕ) (h : ∀ n ≥ N, a n = b n) :
    liminf a atTop = liminf b atTop := by
  apply liminf_congr
  exact eventually_atTop.mpr ⟨N,h⟩

/-- Every actual tail of the printed real sequence still has limsup 1 and liminf -1. -/
theorem every_actual_printed_sequence_tail_has_the_same_upper_and_lower_limits
    (N : ℕ) :
    limsup (fun n => SafeLearning.CompleteFoundationsSequences.additiveAlternation (n+N))
      atTop = (1 : ℝ) ∧
    liminf (fun n => SafeLearning.CompleteFoundationsSequences.additiveAlternation (n+N))
      atTop = (-1 : ℝ) := by
  simpa only [limsup_nat_add,liminf_nat_add] using
    And.intro SafeLearning.CompleteFoundationsSequences.additive_alternation_lims.1
      SafeLearning.CompleteFoundationsSequences.additive_alternation_lims.2.1

end SafeLearning.CompleteFoundationsFinitePrefix23
