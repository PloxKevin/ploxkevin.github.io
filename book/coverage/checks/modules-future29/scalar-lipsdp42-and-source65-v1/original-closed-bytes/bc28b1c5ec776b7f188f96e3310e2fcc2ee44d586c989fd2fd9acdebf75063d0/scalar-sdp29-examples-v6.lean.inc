
theorem actual_monotone_bound_implies_zero_lower_slope_restriction
    (phi : ℝ → ℝ) (beta : ℝ) (hm : Monotone phi) (hb : realLipschitzBound phi beta) :
    slopeRestricted phi 0 beta := by
  intro x y hxy
  have h := hb.2 x y
  rcases lt_or_gt_of_ne hxy with hlt|hgt
  · have hnum : phi x-phi y≤0 := sub_nonpos.mpr (hm hlt.le)
    have hden : x-y<0 := sub_neg.mpr hlt
    rw [abs_of_nonpos hnum,abs_of_nonpos hden.le] at h
    exact ⟨div_nonneg_of_nonpos hnum hden.le,(div_le_iff_of_neg hden).mpr (by linarith)⟩
  · have hnum : 0≤phi x-phi y := sub_nonneg.mpr (hm hgt.le)
    have hden : 0<x-y := sub_pos.mpr hgt
    rw [abs_of_nonneg hnum,abs_of_nonneg hden.le] at h
    exact ⟨div_nonneg hnum hden.le,(div_le_iff₀ hden).mpr h⟩

theorem actual_nonnegative_bounded_derivatives_give_source_slope_restriction
    (phi dphi : ℝ → ℝ) (beta : ℝ) (hbeta : 0≤beta)
    (hd : ∀ x : ℝ,HasDerivAt phi (dphi x) x)
    (hb : ∀ x : ℝ,0≤dphi x ∧ dphi x≤beta) : slopeRestricted phi 0 beta := by
  have hm : Monotone phi := monotone_of_deriv_nonneg
    (fun x=>(hd x).differentiableAt) (fun x=>by rw [(hd x).deriv];exact (hb x).1)
  have hl : LipschitzWith (Real.toNNReal beta) phi := by
    apply lipschitzWith_of_nnnorm_deriv_le (fun x=>(hd x).differentiableAt)
    intro x
    apply NNReal.coe_le_coe.mp
    simpa only [coe_nnnorm,Real.norm_eq_abs,(hd x).deriv,abs_of_nonneg (hb x).1,
      Real.coe_toNNReal beta hbeta] using (hb x).2
  exact actual_monotone_bound_implies_zero_lower_slope_restriction phi beta hm
    ((actual_real_bound_iff_mathlib_lipschitz phi beta hbeta).mpr hl)

theorem actual_sharp_derivative_witness_identifies_the_supremum
    (phi : ℝ → ℝ) (beta u : ℝ) (hbeta : 0<beta)
    (hp : slopeRestricted phi 0 beta) (hd : HasDerivAt phi beta u) :
    derivativeSupremum phi=beta := by
  have hs := actual_derivative_supremum_is_the_least_activation_lipschitz_constant
    phi 0 beta (by norm_num) hbeta hp
  have hb := (actual_slope_restriction_implies_monotonicity_and_global_bound
    phi 0 beta (by norm_num) hbeta hp).2
  have hu := hs.2 hb
  have hl := (actual_real_bound_iff_mathlib_lipschitz phi (derivativeSupremum phi) hs.1.1).mp hs.1
  have hn := hd.le_of_lipschitz hl
  have hlo : beta≤derivativeSupremum phi := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg hbeta.le,
      Real.coe_toNNReal _ hs.1.1] using hn
  exact le_antisymm hu hlo

theorem actual_relu_slope_restriction_and_sharp_constant :
    slopeRestricted (fun x : ℝ=>max x 0) 0 1 ∧
      derivativeSupremum (fun x : ℝ=>max x 0)=1 := by
  have hm : Monotone (fun x : ℝ=>max x 0) := fun x y h=>max_le_max h le_rfl
  have hb : realLipschitzBound (fun x : ℝ=>max x 0) 1 := by
    constructor
    · norm_num
    · intro x y
      simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using
        (LipschitzWith.id.max_const (0:ℝ)).dist_le_mul x y
  have hp := actual_monotone_bound_implies_zero_lower_slope_restriction _ 1 hm hb
  have hd : HasDerivAt (fun x : ℝ=>max x 0) 1 1 := by
    apply (hasDerivAt_id (1:ℝ)).congr_of_eventuallyEq
    exact (lt_mem_nhds (by norm_num : (0:ℝ)<1)).mono (fun y hy=>max_eq_left hy.le)
  exact ⟨hp,actual_sharp_derivative_witness_identifies_the_supremum _ 1 1 (by norm_num) hp hd⟩

theorem actual_tanh_derivative_and_its_sharp_interval (x : ℝ) :
    HasDerivAt Real.tanh (1/(Real.cosh x)^2) x ∧
      0≤1/(Real.cosh x)^2 ∧ 1/(Real.cosh x)^2≤1 := by
  have hc : Real.cosh x≠0 := (Real.cosh_pos x).ne'
  constructor
  · have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hc
    convert h using 1
    · ext z
      exact Real.tanh_eq_sinh_div_cosh
    · field_simp [hc]
      nlinarith [Real.cosh_sq_sub_sinh_sq x]
  · constructor
    · positivity
    · apply (div_le_one (sq_pos_of_ne_zero hc)).mpr
      nlinarith [Real.one_le_cosh x]

theorem actual_tanh_slope_restriction_and_sharp_constant :
    slopeRestricted Real.tanh 0 1 ∧ derivativeSupremum Real.tanh=1 := by
  have hp : slopeRestricted Real.tanh 0 1 :=
    actual_nonnegative_bounded_derivatives_give_source_slope_restriction
      Real.tanh (fun x=>1/(Real.cosh x)^2) 1 (by norm_num)
      (fun x=>(actual_tanh_derivative_and_its_sharp_interval x).1)
      (fun x=>(actual_tanh_derivative_and_its_sharp_interval x).2)
  have hd : HasDerivAt Real.tanh 1 0 := by
    simpa using (actual_tanh_derivative_and_its_sharp_interval 0).1
  exact ⟨hp,actual_sharp_derivative_witness_identifies_the_supremum _ 1 0 (by norm_num) hp hd⟩

theorem actual_sigmoid_slope_restriction_and_sharp_constant :
    slopeRestricted Real.sigmoid 0 (1/4) ∧ derivativeSupremum Real.sigmoid=1/4 := by
  have hb : ∀ x : ℝ,0≤Real.sigmoid x*(1-Real.sigmoid x) ∧
      Real.sigmoid x*(1-Real.sigmoid x)≤1/4 := by
    intro x
    constructor
    · exact mul_nonneg (Real.sigmoid_nonneg x) (by linarith [Real.sigmoid_le_one x])
    · nlinarith [sq_nonneg (Real.sigmoid x-1/2)]
  have hp : slopeRestricted Real.sigmoid 0 (1/4) :=
    actual_nonnegative_bounded_derivatives_give_source_slope_restriction
      Real.sigmoid (fun x=>Real.sigmoid x*(1-Real.sigmoid x)) (1/4) (by norm_num)
      Real.hasDerivAt_sigmoid hb
  have hd : HasDerivAt Real.sigmoid (1/4) 0 := by
    simpa only [Real.sigmoid_zero] using Real.hasDerivAt_sigmoid 0
  exact ⟨hp,actual_sharp_derivative_witness_identifies_the_supremum _ (1/4) 0 (by norm_num) hp hd⟩

theorem actual_three_example_network_constants (w0 w1 b c : ℝ) (hw0 : w0≠0) (hw1 : w1≠0) :
    IsLeast {L : ℝ | realLipschitzBound (scalarNetwork (fun x=>max x 0) w0 w1 b c) L}
      |w0*w1| ∧
    IsLeast {L : ℝ | realLipschitzBound (scalarNetwork Real.tanh w0 w1 b c) L}
      |w0*w1| ∧
    IsLeast {L : ℝ | realLipschitzBound (scalarNetwork Real.sigmoid w0 w1 b c) L}
      ((1/4)*|w0*w1|) := by
  constructor
  · simpa only [actual_relu_slope_restriction_and_sharp_constant.2,mul_one] using
      actual_derivative_supremum_gives_the_exact_network_constant (fun x=>max x 0)
        0 1 w0 w1 b c (by norm_num) (by norm_num)
        actual_relu_slope_restriction_and_sharp_constant.1 hw0 hw1
  · constructor
    · simpa only [actual_tanh_slope_restriction_and_sharp_constant.2,mul_one] using
        actual_derivative_supremum_gives_the_exact_network_constant Real.tanh
          0 1 w0 w1 b c (by norm_num) (by norm_num)
          actual_tanh_slope_restriction_and_sharp_constant.1 hw0 hw1
    · simpa only [actual_sigmoid_slope_restriction_and_sharp_constant.2,mul_comm] using
        actual_derivative_supremum_gives_the_exact_network_constant Real.sigmoid
          0 (1/4) w0 w1 b c (by norm_num) (by norm_num)
          actual_sigmoid_slope_restriction_and_sharp_constant.1 hw0 hw1

theorem actual_larger_supplied_upper_slope_has_the_printed_positive_ratio
    (phi : ℝ → ℝ) (beta w0 w1 : ℝ) (hs : 0<derivativeSupremum phi)
    (hw0 : w0≠0) (hw1 : w1≠0) :
    (beta*|w0*w1|)/(|w0*w1| * derivativeSupremum phi)=beta/derivativeSupremum phi := by
  field_simp [hs.ne',abs_ne_zero.mpr (mul_ne_zero hw0 hw1)]

theorem actual_constant_activation_is_the_zero_constant_exception (k : ℝ) :
    slopeRestricted (fun _ : ℝ=>k) 0 1 ∧
    derivativeSupremum (fun _ : ℝ=>k)=0 ∧
    IsLeast {L : ℝ | realLipschitzBound (scalarNetwork (fun _=>k) 1 1 0 0) L} 0 := by
  constructor
  · intro x y hxy
    norm_num
  · constructor
    · simp [derivativeSupremum]
    · constructor
      · constructor
        · norm_num
        · intro x y
          simp [scalarNetwork]
      · intro L h
        exact h.1

theorem actual_printed_relu_multiplier_squared_bound_and_gain :
    optimalMultiplier 0 1 (-7/10)=49/100 ∧
    (1:ℝ)^2*(13/10)^2*(-7/10)^2=8281/10000 ∧
    |(13/10:ℝ)*(-7/10)|=91/100 ∧
    (91/100:ℝ)^2=8281/10000 := by
  norm_num [optimalMultiplier]

theorem actual_printed_relu_source_matrix :
    sourceMatrix 0 1 (49/100) (8281/10000) (13/10) (-7/10)=
      (!![-8281/10000,637/1000;637/1000,-49/100]:Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [sourceMatrix]

theorem actual_printed_matrix_characteristic_polynomial :
    (sourceMatrix 0 1 (49/100) (8281/10000) (13/10) (-7/10)).charpoly=
      Polynomial.X*(Polynomial.X+Polynomial.C (13181/10000:ℝ)) := by
  rw [Matrix.charpoly_fin_two,actual_printed_relu_source_matrix]
  norm_num [Matrix.trace,Matrix.det_fin_two,Fin.sum_univ_succ]
  ring

theorem actual_printed_matrix_has_exactly_the_two_stated_eigenvalue_roots (z : ℝ) :
    (sourceMatrix 0 1 (49/100) (8281/10000) (13/10) (-7/10)).charpoly.IsRoot z ↔
      z=0 ∨ z= -13181/10000 := by
  rw [actual_printed_matrix_characteristic_polynomial]
  simp only [Polynomial.IsRoot,Polynomial.eval_mul,Polynomial.eval_X,
    Polynomial.eval_add,Polynomial.eval_C,mul_eq_zero]
  constructor
  · rintro (h|h)
    · exact Or.inl h
    · exact Or.inr (by linarith)
  · rintro (h|h)
    · exact Or.inl h
    · exact Or.inr (by linarith)

theorem actual_printed_matrix_two_genuine_eigenvectors :
    let M := sourceMatrix 0 1 (49/100) (8281/10000) (13/10) (-7/10)
    M *ᵥ (![7/10,91/100]:Fin 2 → ℝ)=0 ∧
    M *ᵥ (![91/100,-7/10]:Fin 2 → ℝ)=
      (-13181/10000:ℝ) • (![91/100,-7/10]:Fin 2 → ℝ) ∧
    (![7/10,91/100]:Fin 2 → ℝ)≠0 ∧ (![91/100,-7/10]:Fin 2 → ℝ)≠0 := by
  dsimp
  constructor
  · ext i
    fin_cases i <;> norm_num [sourceMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  · constructor
    · ext i
      fin_cases i <;> norm_num [sourceMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
    · constructor
      · intro h
        have h0 := congrFun h 0
        norm_num at h0
      · intro h
        have h0 := congrFun h 0
        norm_num at h0

theorem actual_printed_negative_eigenvalue_three_decimal_enclosure :
    |(-13181/10000:ℝ)-(-659/500)|<1/2000 ∧
      (-13181/10000:ℝ)≠-659/500 := by norm_num

def printedMultiplierGrid : Finset ℕ :=
  (Finset.range 4001).filter (fun k=>((49/100:ℝ)^2)/2<(k:ℝ)/1000)

/-- Explicit exact rational grid with step.001; the domain test uses w1²=.49. -/
def printedValidMultiplierGrid : Finset ℕ :=
  (Finset.range 4001).filter (fun k=>(49/100:ℝ)/2<(k:ℝ)/1000)

theorem actual_exact_grid_contains_the_unique_optimizer :
    (490:ℕ)∈printedValidMultiplierGrid ∧
      IsLeast {rho : ℝ | ∃ k : ℕ,k∈printedValidMultiplierGrid ∧
        rho=(13/10)^2*objective 0 1 (-7/10) ((k:ℝ)/1000)} (8281/10000) := by
  have hg : (490:ℕ)∈printedValidMultiplierGrid := by
    norm_num [printedValidMultiplierGrid]
  constructor
  · exact hg
  · constructor
    · refine ⟨490,hg,?_⟩
      norm_num [objective]
    · rintro rho ⟨k,hk,rfl⟩
      have ht : (-7/10:ℝ)^2/2<(k:ℝ)/1000 := by
        have h := (Finset.mem_filter.mp hk).2
        norm_num at h ⊢
        exact h
      have h := (actual_global_objective_bound_and_exact_equality 0 1 (-7/10)
        ((k:ℝ)/1000) (by norm_num) (by norm_num) ht).1
      have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0≤(13/10:ℝ)^2)
      norm_num at hm
      exact hm
