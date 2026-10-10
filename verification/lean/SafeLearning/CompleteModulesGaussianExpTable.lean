import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators
namespace SafeLearning.CompleteModulesGaussianExpTable

def actualExpPolynomial (x : ℝ) : ℝ := ∑ i ∈ Finset.range 30, x^i/(i.factorial:ℝ)
def actualExpArgument (k : Fin 13) : ℝ := -(k.val:ℝ)^2/200
def actualExpApproximation : Fin 13 → ℝ := ![(100000000000000000000000000000000/100000000000000000000000000000000:ℝ),
  (99501247919268231335256424623250/100000000000000000000000000000000:ℝ),
  (98019867330675530222081410422531/100000000000000000000000000000000:ℝ),
  (95599748183309990701392762949807/100000000000000000000000000000000:ℝ),
  (92311634638663578291075984957239/100000000000000000000000000000000:ℝ),
  (88249690258459540286489214322905/100000000000000000000000000000000:ℝ),
  (83527021141127202131238497401878/100000000000000000000000000000000:ℝ),
  (78270453824186816771086598546541/100000000000000000000000000000000:ℝ),
  (72614903707369092485504752942358/100000000000000000000000000000000:ℝ),
  (66697681085847440014028909296679/100000000000000000000000000000000:ℝ),
  (60653065971263342360379953499118/100000000000000000000000000000000:ℝ),
  (54607442663970941345857205251034/100000000000000000000000000000000:ℝ),
  (48675225595997165005616764799563/100000000000000000000000000000000:ℝ)]

theorem actual_thirtieth_exponential_polynomial_error_on_the_unit_interval
    (x : ℝ) (hx : |x| ≤ 1) :
    |Real.exp x-actualExpPolynomial x| ≤ 1/100000000000000000000000000000000 := by
  have hr : ‖(x:ℂ)‖/(30+1:ℝ) ≤ 1/2 := by
    rw [Complex.norm_real,Real.norm_eq_abs]
    norm_num
    linarith
  have he := Complex.exp_bound' (x := (x:ℂ)) (n := 30) (by norm_num at hr ⊢; exact hr)
  have heReal : |Real.exp x-actualExpPolynomial x| ≤ |x|^30/(30:ℕ).factorial*2 := by
    convert he using 1 <;> norm_cast
  have hp := pow_le_pow_left₀ (abs_nonneg x) hx 30
  norm_num [Nat.factorial] at heReal hp
  nlinarith

theorem actual_thirteen_gaussian_exponential_table_entries_have_rigorous_error_bounds
    (k : Fin 13) :
    |Real.exp (actualExpArgument k)-actualExpApproximation k| ≤
      1/10000000000000000000000000000000 := by
  have hx : |actualExpArgument k| ≤ 1 := by
    fin_cases k <;> norm_num [actualExpArgument]
  have he := actual_thirtieth_exponential_polynomial_error_on_the_unit_interval
    (actualExpArgument k) hx
  have hp : |actualExpPolynomial (actualExpArgument k)-actualExpApproximation k| ≤
      1/100000000000000000000000000000000 := by
    fin_cases k <;> norm_num [actualExpArgument,actualExpApproximation,actualExpPolynomial,
      Finset.sum_range_succ,Nat.factorial]
  calc
    _ ≤ |Real.exp (actualExpArgument k)-actualExpPolynomial (actualExpArgument k)|+
        |actualExpPolynomial (actualExpArgument k)-actualExpApproximation k| :=
      abs_sub_le _ _ _
    _ ≤ _ := by linarith

end SafeLearning.CompleteModulesGaussianExpTable
