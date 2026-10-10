import SafeLearning.CompleteAppliedCovarianceConsequences

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators
namespace SafeLearning.CompleteAppliedCorrelation
open CompleteAppliedCovarianceMatrix

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

def correlation (X Y : Ω → ℝ) (μ : Measure Ω) (sigmaX sigmaY : ℝ) : ℝ :=
  cov[X,Y;μ]/(sigmaX*sigmaY)

lemma actual_variance_of_standardized_quantity
    (X : Ω → ℝ) (sigma : ℝ) (hs : 0<sigma) (hv : Var[X;μ]=sigma^2) :
    Var[fun ω => X ω/sigma;μ]=1 := by
  simp_rw [div_eq_mul_inv,mul_comm (X _) sigma⁻¹]
  rw [variance_const_mul,hv]
  field_simp

theorem actual_correlation_is_the_covariance_of_standardized_variables
    (X Y : Ω → ℝ) (sigmaX sigmaY : ℝ) :
    cov[fun ω => X ω/sigmaX,fun ω => Y ω/sigmaY;μ]=
      correlation X Y μ sigmaX sigmaY := by
  rw [covariance_fun_div_left,covariance_fun_div_right]
  simp only [correlation,div_div]
  congr 1
  ring

theorem actual_standardized_sum_and_difference_have_the_literal_variances
    (X Y : Ω → ℝ) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (sigmaX sigmaY : ℝ) (hsX : 0<sigmaX) (hsY : 0<sigmaY)
    (hvX : Var[X;μ]=sigmaX^2) (hvY : Var[Y;μ]=sigmaY^2) :
    Var[fun ω => X ω/sigmaX+Y ω/sigmaY;μ]=2*(1+correlation X Y μ sigmaX sigmaY) ∧
    Var[fun ω => X ω/sigmaX-Y ω/sigmaY;μ]=2*(1-correlation X Y μ sigmaX sigmaY) := by
  have hx : MemLp (fun ω => X ω/sigmaX) 2 μ := by
    simpa only [div_eq_mul_inv,mul_comm] using hX.const_mul sigmaX⁻¹
  have hy : MemLp (fun ω => Y ω/sigmaY) 2 μ := by
    simpa only [div_eq_mul_inv,mul_comm] using hY.const_mul sigmaY⁻¹
  rw [variance_fun_add hx hy,variance_fun_sub hx hy,
    actual_variance_of_standardized_quantity X sigmaX hsX hvX,
    actual_variance_of_standardized_quantity Y sigmaY hsY hvY,
    actual_correlation_is_the_covariance_of_standardized_variables]
  constructor <;> ring

theorem actual_correlation_lies_in_the_closed_unit_interval
    (X Y : Ω → ℝ) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (sigmaX sigmaY : ℝ) (hsX : 0<sigmaX) (hsY : 0<sigmaY)
    (hvX : Var[X;μ]=sigmaX^2) (hvY : Var[Y;μ]=sigmaY^2) :
    -1≤correlation X Y μ sigmaX sigmaY ∧ correlation X Y μ sigmaX sigmaY≤1 := by
  have h := actual_standardized_sum_and_difference_have_the_literal_variances
    X Y hX hY sigmaX sigmaY hsX hsY hvX hvY
  have hp := variance_nonneg (fun ω => X ω/sigmaX+Y ω/sigmaY) μ
  have hm := variance_nonneg (fun ω => X ω/sigmaX-Y ω/sigmaY) μ
  rw [h.1] at hp
  rw [h.2] at hm
  constructor <;> linarith

lemma actual_covariance_respects_almost_sure_equality_on_the_right
    (X Y Z : Ω → ℝ) (h : Y =ᵐ[μ] Z) : cov[X,Y;μ]=cov[X,Z;μ] := by
  unfold covariance
  rw [integral_congr_ae h]
  apply integral_congr_ae
  filter_upwards [h] with ω hω
  rw [hω]

lemma actual_affine_almost_sure_relation_gives_covariance_and_variance
    (X Y : Ω → ℝ) (hX : MemLp X 2 μ) (a b : ℝ)
    (h : Y =ᵐ[μ] fun ω => a*X ω+b) :
    cov[X,Y;μ]=a*Var[X;μ] ∧ Var[Y;μ]=a^2*Var[X;μ] := by
  constructor
  · rw [actual_covariance_respects_almost_sure_equality_on_the_right X Y _ h,
      covariance_add_const_right ((hX.const_mul a).integrable (by norm_num)),
      covariance_const_mul_right,covariance_self hX.aemeasurable]
  · rw [variance_congr h,
      CompleteAppliedCovarianceConsequences.actual_scalar_affine_variance_is_the_literal_squared_scale X hX]

theorem actual_correlation_one_iff_a_positive_slope_almost_sure_affine_relation
    (X Y : Ω → ℝ) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (sigmaX sigmaY : ℝ) (hsX : 0<sigmaX) (hsY : 0<sigmaY)
    (hvX : Var[X;μ]=sigmaX^2) (hvY : Var[Y;μ]=sigmaY^2) :
    correlation X Y μ sigmaX sigmaY=1 ↔
      ∃ a b : ℝ,0<a ∧ Y =ᵐ[μ] fun ω => a*X ω+b := by
  have hnX := ne_of_gt hsX
  have hnY := ne_of_gt hsY
  constructor
  · intro hr
    have hx : MemLp (fun ω => X ω/sigmaX) 2 μ := by
      simpa only [div_eq_mul_inv,mul_comm] using hX.const_mul sigmaX⁻¹
    have hy : MemLp (fun ω => Y ω/sigmaY) 2 μ := by
      simpa only [div_eq_mul_inv,mul_comm] using hY.const_mul sigmaY⁻¹
    have hz := (actual_standardized_sum_and_difference_have_the_literal_variances
      X Y hX hY sigmaX sigmaY hsX hsY hvX hvY).2
    rw [hr] at hz
    norm_num at hz
    obtain ⟨c,hc⟩ := (actual_finite_second_moment_variance_zero_iff_almost_sure_constant _
      (hx.sub hy)).1 hz
    refine ⟨sigmaY/sigmaX,-sigmaY*c,div_pos hsY hsX,?_⟩
    filter_upwards [hc] with ω hω
    dsimp at hω ⊢
    field_simp at hω ⊢
    nlinarith
  · rintro ⟨a,b,ha,hab⟩
    obtain ⟨hc,hv⟩ := actual_affine_almost_sure_relation_gives_covariance_and_variance X Y hX a b hab
    rw [hvX,hvY] at hv
    have he : a*sigmaX=sigmaY := by
      have hp := mul_pos ha hsX
      nlinarith [sq_nonneg (a*sigmaX-sigmaY)]
    unfold correlation
    rw [hc,hvX]
    apply (div_eq_one_iff_eq (mul_ne_zero hnX hnY)).2
    nlinarith [congrArg (fun z : ℝ => sigmaX*z) he]

theorem actual_correlation_negative_one_iff_a_negative_slope_almost_sure_affine_relation
    (X Y : Ω → ℝ) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (sigmaX sigmaY : ℝ) (hsX : 0<sigmaX) (hsY : 0<sigmaY)
    (hvX : Var[X;μ]=sigmaX^2) (hvY : Var[Y;μ]=sigmaY^2) :
    correlation X Y μ sigmaX sigmaY= -1 ↔
      ∃ a b : ℝ,a<0 ∧ Y =ᵐ[μ] fun ω => a*X ω+b := by
  have hnX := ne_of_gt hsX
  have hnY := ne_of_gt hsY
  constructor
  · intro hr
    have hx : MemLp (fun ω => X ω/sigmaX) 2 μ := by
      simpa only [div_eq_mul_inv,mul_comm] using hX.const_mul sigmaX⁻¹
    have hy : MemLp (fun ω => Y ω/sigmaY) 2 μ := by
      simpa only [div_eq_mul_inv,mul_comm] using hY.const_mul sigmaY⁻¹
    have hz := (actual_standardized_sum_and_difference_have_the_literal_variances
      X Y hX hY sigmaX sigmaY hsX hsY hvX hvY).1
    rw [hr] at hz
    norm_num at hz
    obtain ⟨c,hc⟩ := (actual_finite_second_moment_variance_zero_iff_almost_sure_constant _
      (hx.add hy)).1 hz
    refine ⟨-sigmaY/sigmaX,sigmaY*c,div_neg_of_neg_of_pos (neg_neg_of_pos hsY) hsX,?_⟩
    filter_upwards [hc] with ω hω
    dsimp at hω ⊢
    field_simp at hω ⊢
    nlinarith
  · rintro ⟨a,b,ha,hab⟩
    obtain ⟨hc,hv⟩ := actual_affine_almost_sure_relation_gives_covariance_and_variance X Y hX a b hab
    rw [hvX,hvY] at hv
    have he : a*sigmaX= -sigmaY := by
      have hp := mul_neg_of_neg_of_pos ha hsX
      nlinarith [sq_nonneg (a*sigmaX+sigmaY)]
    unfold correlation
    rw [hc,hvX]
    apply (div_eq_iff (mul_ne_zero hnX hnY)).2
    nlinarith [congrArg (fun z : ℝ => sigmaX*z) he]

theorem actual_pair_covariance_matrix_has_the_literal_correlation_entries
    (X Y : Ω → ℝ) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (sigmaX sigmaY : ℝ) (hsX : 0<sigmaX) (hsY : 0<sigmaY)
    (hvX : Var[X;μ]=sigmaX^2) (hvY : Var[Y;μ]=sigmaY^2) :
    covarianceMatrix (![X,Y]) μ=
      !![sigmaX^2,correlation X Y μ sigmaX sigmaY*sigmaX*sigmaY;
        correlation X Y μ sigmaX sigmaY*sigmaX*sigmaY,sigmaY^2] := by
  have he : correlation X Y μ sigmaX sigmaY*sigmaX*sigmaY=cov[X,Y;μ] := by
    unfold correlation
    field_simp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [covarianceMatrix,covariance_self hX.aemeasurable,covariance_self hY.aemeasurable,
      covariance_comm,hvX,hvY,he]

end SafeLearning.CompleteAppliedCorrelation
