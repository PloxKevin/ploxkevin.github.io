import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace SafeLearning.CompleteAppliedGaussianSmallTail24

theorem actual_standard_gaussian_has_its_true_subgaussian_MGF :
    HasSubgaussianMGF id 1 (gaussianReal 0 1) := by
  constructor
  · intro t
    exact integrable_exp_mul_gaussianReal t
  · intro t
    rw [mgf_id_gaussianReal]
    simp

theorem actual_standard_gaussian_absolute_tail_ten_is_small :
    (gaussianReal 0 1).real {x | (10:ℝ) < |x|} < 1/50000 := by
  let μ := gaussianReal 0 1
  have hg := actual_standard_gaussian_has_its_true_subgaussian_MGF
  have hp := hg.measure_ge_le (ε:=(10:ℝ)) (by norm_num)
  have hn := hg.neg.measure_ge_le (ε:=(10:ℝ)) (by norm_num)
  norm_num at hp hn
  have hs : {x : ℝ | (10:ℝ) < |x|} ⊆ {x | (10:ℝ) ≤ x} ∪ {x | (10:ℝ) ≤ -x} := by
    intro x hx
    rw [mem_setOf_eq, lt_abs] at hx
    simp only [mem_union, mem_setOf_eq]
    rcases hx with hx | hx
    · exact Or.inl hx.le
    · exact Or.inr hx.le
  have hm := measureReal_mono hs (μ:=μ)
  have hu := measureReal_union_le (μ:=μ) {x | (10:ℝ) ≤ x} {x | (10:ℝ) ≤ -x}
  have he10 := Real.add_one_le_exp (10:ℝ)
  have he50 : (161051:ℝ) ≤ Real.exp 50 := by
    have hpow := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 11) (by linarith : (11:ℝ) ≤ Real.exp 10) 5
    have he := Real.exp_nat_mul (10:ℝ) 5
    norm_num at hpow he
    simpa only [he] using hpow
  have he : Real.exp (-50:ℝ) < (1/100000:ℝ) := by
    rw [Real.exp_neg, ← one_div, div_lt_iff₀ (Real.exp_pos _)]
    nlinarith
  change μ.real {x | (10:ℝ) < |x|} < _
  change μ.real {x | (10:ℝ) ≤ x} ≤ Real.exp (-50) at hp
  change μ.real {x | (10:ℝ) ≤ -x} ≤ Real.exp (-50) at hn
  linarith

end SafeLearning.CompleteAppliedGaussianSmallTail24
