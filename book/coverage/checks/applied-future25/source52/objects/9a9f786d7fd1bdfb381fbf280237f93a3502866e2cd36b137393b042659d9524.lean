import SafeLearning.CompleteFoundationsCalculusModels

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Set Filter
open scoped BigOperators Topology Matrix

namespace SafeLearning.CompleteFoundationsTaylorModels

abbrev E := EuclideanSpace ℝ (Fin 2)
open SafeLearning.CompleteFoundationsSpectralModels (point applyMatrix matrix_coordinate_action inner_coordinate_formula)
open SafeLearning.CompleteFoundationsCalculusModels (coordinate)

def objective (x : E) : ℝ := Real.exp (x 0)+(x 1)^2
def sourceGradient (x : E) : E := point (Real.exp (x 0)) (2*x 1)
def sourceHessian (x : E) : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![Real.exp (x 0),2]
def model (x : E) : ℝ := 1+x 0+(x 0)^2/2+(x 1)^2

theorem actual_gradient (x : E) : HasGradientAt objective (sourceGradient x) x := by
  have h0 := (coordinate 0).hasFDerivAt (x := x)
  have h1 := (coordinate 1).hasFDerivAt (x := x)
  have hf : HasFDerivAt objective ((Real.exp (x 0)) • coordinate 0+(2*x 1) • coordinate 1) x := by
    convert h0.exp.add (h1.pow 2) using 1
    · rfl
    · ext u
      simp [coordinate,PiLp.proj,PiLp.projₗ]
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hf using 1
  ext u
  simp [sourceGradient,point,coordinate,InnerProductSpace.toDual_apply_apply,
    PiLp.inner_apply,Fin.sum_univ_succ,PiLp.proj,PiLp.projₗ]
  ring

theorem actual_hessian (x : E) :
    HasFDerivAt (gradient objective) (applyMatrix (sourceHessian x)) x := by
  have he : gradient objective=(fun z : E => Real.exp (z 0) • point 1 0+(2*z 1) • point 0 1) := by
    funext z
    rw [(actual_gradient z).gradient]
    ext i
    fin_cases i <;> simp [sourceGradient,point]
  rw [he]
  have h0 := (coordinate 0).hasFDerivAt (x := x)
  have h1 := (coordinate 1).hasFDerivAt (x := x)
  convert (h0.exp.smul_const (point 1 0)).add ((h1.const_mul 2).smul_const (point 0 1)) using 1
  · rfl
  · ext u i
    rw [matrix_coordinate_action]
    fin_cases i <;> simp [coordinate,sourceHessian,point,PiLp.proj,PiLp.projₗ,Matrix.diagonal]

theorem actual_origin_data :
    objective 0=1 ∧ gradient objective 0=point 1 0 ∧ sourceHessian 0=Matrix.diagonal ![1,2] := by
  rw [(actual_gradient 0).gradient]
  norm_num [objective,sourceGradient,sourceHessian,point]

theorem actual_taylor_model (x : E) :
    model x=objective 0+inner ℝ (gradient objective 0) x+
      (1/2 : ℝ)*inner ℝ x (applyMatrix (sourceHessian 0) x) := by
  rw [actual_origin_data.1,actual_origin_data.2.1,actual_origin_data.2.2,
    matrix_coordinate_action,inner_coordinate_formula,inner_coordinate_formula]
  simp [model,point,Matrix.diagonal]
  ring

theorem actual_remainder_identity (x : E) :
    objective x-model x=Real.exp (x 0)-(1+x 0+(x 0)^2/2) := by
  unfold objective model
  ring

theorem actual_iterated_exponential_derivative (n : ℕ) : iteratedDeriv n Real.exp=Real.exp := by
  rw [iteratedDeriv_eq_iterate,Real.iter_deriv_exp]

theorem actual_scalar_taylor_polynomial (x : ℝ) (hx : 0 < x) :
    taylorWithinEval Real.exp 2 (Icc 0 x) 0 x=1+x+x^2/2 := by
  have hi : ∀ n : ℕ,iteratedDerivWithin n Real.exp (Icc 0 x) 0=1 := by
    intro n
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hx)
      Real.contDiff_exp.contDiffAt (by exact ⟨le_rfl,hx.le⟩),actual_iterated_exponential_derivative]
    norm_num
  rw [taylor_within_apply]
  norm_num [Finset.sum_range_succ,hi]
  ring

theorem actual_positive_scalar_lagrange_remainder (x : ℝ) (hx : 0 < x) :
    ∃ c ∈ Ioo 0 x,Real.exp x-(1+x+x^2/2)=Real.exp c*x^3/6 := by
  have h := taylor_mean_remainder_lagrange_iteratedDeriv (f := Real.exp) (x₀ := 0) (x := x) (n := 2)
    hx.ne Real.contDiff_exp.contDiffOn
  rcases h with ⟨c,hc,he⟩
  have hc' : c ∈ Ioo 0 x := by simpa [Set.uIoo_of_lt hx] using hc
  refine ⟨c,hc',?_⟩
  rw [Set.uIcc_of_le hx.le,actual_scalar_taylor_polynomial x hx,actual_iterated_exponential_derivative] at he
  norm_num at he
  exact he

theorem actual_positive_remainder_bound (x : ℝ) (hx : 0 < x) :
    0≤Real.exp x-(1+x+x^2/2) ∧ Real.exp x-(1+x+x^2/2)≤Real.exp x*x^3/6 := by
  obtain ⟨c,hc,he⟩ := actual_positive_scalar_lagrange_remainder x hx
  rw [he]
  constructor
  · positivity
  · apply div_le_div_of_nonneg_right _ (by norm_num)
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hc.2.le) (pow_nonneg hx.le 3)

theorem actual_third_derivative_and_interval_bound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (1/10)) :
    iteratedDeriv 3 Real.exp t=Real.exp t ∧ Real.exp t≤Real.exp (1/10) := by
  rw [actual_iterated_exponential_derivative]
  exact ⟨rfl,Real.exp_le_exp.mpr ht.2⟩

theorem actual_source_model_value : model (point (1/10) (1/5))=229/200 := by
  norm_num [model,point]

theorem actual_source_remainder :
    0≤objective (point (1/10) (1/5))-model (point (1/10) (1/5)) ∧
    objective (point (1/10) (1/5))-model (point (1/10) (1/5))≤Real.exp (1/10)/6000 := by
  rw [actual_remainder_identity]
  have h := actual_positive_remainder_bound (1/10) (by norm_num)
  norm_num [point] at h ⊢
  have he : Real.exp (1/10)*(1/1000)/6=Real.exp (1/10)/6000 := by ring
  rwa [he] at h

theorem actual_exp_tenth_decimal : |Real.exp (1/10)-(1105170918/1000000000 : ℝ)|<1/2000000000 := by
  have h := Real.exp_bound (x := (1/10 : ℝ)) (by norm_num) (n := 8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  rw [abs_lt]
  constructor <;> nlinarith [(abs_le.mp h).1,(abs_le.mp h).2]

theorem actual_source_decimal_values :
    |objective (point (1/10) (1/5))-(1145170918/1000000000 : ℝ)|<1/2000000000 ∧
    |(objective (point (1/10) (1/5))-model (point (1/10) (1/5)))-
      (170918/1000000000 : ℝ)|<1/2000000000 ∧
    |Real.exp (1/10)/6000-(184195/1000000000 : ℝ)|<1/2000000000 := by
  have h := abs_lt.mp actual_exp_tenth_decimal
  simp [objective,model,point]
  rw [abs_lt,abs_lt,abs_lt]
  constructor
  · constructor <;> linarith
  constructor
  · constructor <;> linarith
  · constructor <;> linarith

def omittedHalfModel (x : E) : ℝ := 1+x 0+(x 0)^2+2*(x 1)^2

theorem actual_omitted_half_error (x : E) :
    omittedHalfModel x-model x=(x 0)^2/2+(x 1)^2 := by
  unfold omittedHalfModel model
  ring

theorem actual_source_omitted_half_value :
    omittedHalfModel (point (1/10) (1/5))=119/100 ∧
    omittedHalfModel (point (1/10) (1/5))-model (point (1/10) (1/5))=9/200 ∧
    objective (point (1/10) (1/5))<omittedHalfModel (point (1/10) (1/5)) := by
  have h := (abs_lt.mp actual_source_decimal_values.1).2
  constructor
  · norm_num [omittedHalfModel,point]
  constructor
  · norm_num [omittedHalfModel,model,point]
  · have hm : omittedHalfModel (point (1/10) (1/5))=119/100 := by norm_num [omittedHalfModel,point]
    rw [hm]
    linarith

end SafeLearning.CompleteFoundationsTaylorModels
