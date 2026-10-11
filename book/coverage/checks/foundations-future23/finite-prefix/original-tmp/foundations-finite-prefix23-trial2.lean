import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter
open scoped Topology

namespace SafeLearning.CompleteFoundationsFinitePrefix23

def printedAdditiveSequence (n : ℕ) : ℝ := (-1)^n+1/((n : ℝ)+1)

/-- The printed sequence really has distinct even/odd limiting values. -/
theorem printed_additive_sequence_even_and_odd_limits :
    Tendsto (fun n => printedAdditiveSequence (2*n)) atTop (𝓝 (1 : ℝ)) ∧
    Tendsto (fun n => printedAdditiveSequence (2*n+1)) atTop (𝓝 (-1 : ℝ)) := by
  have he : Tendsto (fun n : ℕ => 2*n) atTop atTop :=
    tendsto_atTop_mono (fun n => by simp only [id_eq]; omega) tendsto_id
  have ho : Tendsto (fun n : ℕ => 2*n+1) atTop atTop :=
    tendsto_atTop_mono (fun n => by simp only [id_eq]; omega) tendsto_id
  have hz : Tendsto (fun n : ℕ => 1/((n : ℝ)+1)) atTop (𝓝 0) := by
    simpa only [one_div,Function.comp_def] using
      tendsto_inv_atTop_zero.comp
        (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
  constructor
  · have h := (tendsto_const_nhds (x := (1 : ℝ))).add (hz.comp he)
    simpa [printedAdditiveSequence,Function.comp_def,pow_mul] using h
  · have h := (tendsto_const_nhds (x := (-1 : ℝ))).add (hz.comp ho)
    simpa [printedAdditiveSequence,Function.comp_def,pow_succ,pow_mul] using h

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

/-- Each actual printed-sequence tail preserves both extended limiting bounds. -/
theorem every_actual_printed_sequence_tail_has_unchanged_extended_limiting_bounds
    (N : ℕ) :
    limsup (fun n => (printedAdditiveSequence (n+N) : EReal)) atTop =
      limsup (fun n => (printedAdditiveSequence n : EReal)) atTop ∧
    liminf (fun n => (printedAdditiveSequence (n+N) : EReal)) atTop =
      liminf (fun n => (printedAdditiveSequence n : EReal)) atTop :=
  ⟨limsup_nat_add _ N,liminf_nat_add _ N⟩

end SafeLearning.CompleteFoundationsFinitePrefix23
