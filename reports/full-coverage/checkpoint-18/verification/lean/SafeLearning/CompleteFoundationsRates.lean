import SafeLearning.PrimersFoundations

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Asymptotics
open scoped BigOperators Topology

namespace SafeLearning.CompleteFoundationsRates

def growthPolynomial (n : ℕ) : ℝ := 2*(n : ℝ)^2+3*(n : ℝ)+1
def squareGrowth (n : ℕ) : ℝ := (n : ℝ)^2

theorem polynomial_explicit_growth (n : ℕ) (hn : 1 ≤ n) :
    2*squareGrowth n ≤ growthPolynomial n ∧ growthPolynomial n ≤ 6*squareGrowth n := by
  have hreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact SafeLearning.PrimersFoundations.polynomial_growth (n : ℝ) hreal

theorem polynomial_bigO_with_six : IsBigOWith 6 atTop growthPolynomial squareGrowth := by
  apply IsBigOWith.of_bound
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hp : 0 ≤ growthPolynomial n := by unfold growthPolynomial; positivity
  have hs : 0 ≤ squareGrowth n := by unfold squareGrowth; positivity
  simpa [Real.norm_eq_abs,abs_of_nonneg hp,abs_of_nonneg hs] using
    (polynomial_explicit_growth n hn).2

theorem polynomial_reciprocal_bigO_with_half :
    IsBigOWith (1/2) atTop squareGrowth growthPolynomial := by
  apply IsBigOWith.of_bound
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hp : 0 ≤ growthPolynomial n := by unfold growthPolynomial; positivity
  have hs : 0 ≤ squareGrowth n := by unfold squareGrowth; positivity
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hp,abs_of_nonneg hs]
  linarith [(polynomial_explicit_growth n hn).1]

theorem polynomial_theta : IsTheta atTop growthPolynomial squareGrowth :=
  ⟨polynomial_bigO_with_six.isBigO,polynomial_reciprocal_bigO_with_half.isBigO⟩

theorem polynomial_exact_ratio_limit :
    Tendsto (fun n => growthPolynomial n/squareGrowth n) atTop (𝓝 (2 : ℝ)) := by
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h := ((tendsto_const_nhds (x := (2 : ℝ))).add (hi.const_mul 3)).add (hi.pow 2)
  norm_num at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hne : (n : ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn)
  dsimp [growthPolynomial,squareGrowth]
  field_simp

theorem polynomial_not_littleO : ¬ IsLittleO atTop growthPolynomial squareGrowth := by
  intro h
  have hz := h.tendsto_div_nhds_zero
  have he := tendsto_nhds_unique polynomial_exact_ratio_limit hz
  norm_num at he

theorem cost_comparison_under_models (iterationsA iterationsB costA costB : ℕ)
    (ha : iterationsA=1600) (hb : iterationsB=80) (hca : costA=100) (hcb : costB=1000) :
    iterationsB*costB < iterationsA*costA ∧ iterationsA*costA=2*(iterationsB*costB) := by
  subst iterationsA; subst iterationsB; subst costA; subst costB
  norm_num

end SafeLearning.CompleteFoundationsRates
