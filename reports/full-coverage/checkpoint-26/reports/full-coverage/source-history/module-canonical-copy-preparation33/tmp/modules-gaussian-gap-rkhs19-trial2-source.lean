import SafeLearning.CompleteModulesSafeOptGaussianGapFeatures

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators Topology
namespace SafeLearning.CompleteModulesSafeOptGaussianGapRKHS
open CompleteModulesSafeOptGaussianGapSeries CompleteModulesSafeOptGaussianGapFeatures

def actualScaledCoefficient (coefficient : ActualCoefficientSpace) (n : ℕ) : ℝ :=
  coefficient n/Real.sqrt (n.factorial:ℝ)
def actualCoefficientPowerSeries (coefficient : ActualCoefficientSpace) :
    FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ (actualScaledCoefficient coefficient)

theorem actual_coefficient_power_series_has_positive_radius
    (coefficient : ActualCoefficientSpace) :
    (1:ENNReal) ≤ (actualCoefficientPowerSeries coefficient).radius := by
  apply (actualCoefficientPowerSeries coefficient).le_radius_of_bound ‖coefficient‖ (r := 1)
  intro n
  have hf : (1:ℝ) ≤ (n.factorial:ℝ) := by exact_mod_cast n.factorial_pos
  have hs := Real.sq_sqrt (le_trans (by norm_num : (0:ℝ) ≤ 1) hf)
  have hn := Real.sqrt_nonneg (n.factorial:ℝ)
  have hge : (1:ℝ) ≤ Real.sqrt (n.factorial:ℝ) := by nlinarith
  have hc := lp.norm_apply_le_norm (by norm_num : (2:ENNReal) ≠ 0) coefficient n
  simp only [actualCoefficientPowerSeries,FormalMultilinearSeries.ofScalars_norm,
    NNReal.coe_one,one_pow,mul_one,actualScaledCoefficient,Real.norm_eq_abs,abs_div,
    abs_of_nonneg hn]
  exact (div_le_self (abs_nonneg _) hge).trans (by simpa only [Real.norm_eq_abs] using hc)

theorem actual_gaussian_feature_evaluation_zero_at_every_real_point_forces_zero_coefficient
    (coefficient : ActualCoefficientSpace)
    (hzero : ∀ x : ℝ, inner ℝ coefficient (actualFeatureVector x)=0) :
    coefficient=0 := by
  let p := actualCoefficientPowerSeries coefficient
  have hradius : (1:ENNReal) ≤ p.radius := actual_coefficient_power_series_has_positive_radius coefficient
  have hpos : 0 < p.radius := lt_of_lt_of_le (by norm_num : (0:ENNReal) < 1) hradius
  have hp := (p.hasFPowerSeriesOnBall hpos).hasFPowerSeriesAt
  have hloc : p.sum =ᶠ[nhds (0:ℝ)] 0 := by
    filter_upwards [Metric.ball_mem_nhds (0:ℝ) (by norm_num : (0:ℝ) < 1)] with x hx
    have hx1 : edist x (0:ℝ) < (1:NNReal) := by
      rw [edist_lt_coe]
      exact hx
    have hxrad : x ∈ Metric.eball (0:ℝ) p.radius :=
      (Metric.mem_eball).mpr (lt_of_lt_of_le hx1 hradius)
    have hseries : HasSum (fun n => actualScaledCoefficient coefficient n*x^n) (p.sum x) := by
      simpa only [p,actualCoefficientPowerSeries,FormalMultilinearSeries.ofScalars_apply_eq,
        smul_eq_mul] using p.hasSum hxrad
    have hinner : HasSum (fun n => coefficient n*actualGaussianFeature n x) 0 := by
      simpa only [RCLike.inner_apply,conj_trivial,mul_comm,
        actual_feature_vector_coordinates,hzero x] using lp.hasSum_inner (𝕜:=ℝ) coefficient (actualFeatureVector x)
    have hscaled : HasSum (fun n => actualScaledCoefficient coefficient n*x^n) 0 := by
      convert hinner.mul_left (Real.exp (x^2/2)) using 1
      · funext n
        have he : Real.exp (x^2/2)*Real.exp (-(x^2)/2)=1 := by
          rw [← Real.exp_add]
          convert Real.exp_zero using 1
          ring
        dsimp only [actualScaledCoefficient,actualGaussianFeature]
        calc
          _ = (Real.exp (x^2/2)*Real.exp (-(x^2)/2))*(coefficient n/Real.sqrt (n.factorial:ℝ))*x^n := by
            rw [he,one_mul]
          _ = _ := by ring
      · simp
    exact hseries.unique hscaled
  have hpzero : p=0 := hp.eq_zero_of_eventually hloc
  have hscaledzero : actualScaledCoefficient coefficient=0 := by
    exact (FormalMultilinearSeries.ofScalars_series_eq_zero ℝ).mp hpzero
  ext n
  have h := congrFun hscaledzero n
  have hs : Real.sqrt (n.factorial:ℝ) ≠ 0 := by
    apply ne_of_gt (Real.sqrt_pos.mpr _)
    exact_mod_cast n.factorial_pos
  change coefficient n=0
  exact (div_eq_zero_iff.mp h).resolve_right hs

def actualGaussianEvaluation : ActualCoefficientSpace →L[ℝ] ℝ → ℝ :=
  ContinuousLinearMap.pi (fun x => innerSL ℝ (actualFeatureVector x))

theorem actual_gaussian_function_evaluation_is_injective :
    Function.Injective actualGaussianEvaluation := by
  intro a b hequal
  have hz : a-b=0 := by
    apply actual_gaussian_feature_evaluation_zero_at_every_real_point_forces_zero_coefficient
    intro x
    have h := congrFun hequal x
    change inner ℝ (actualFeatureVector x) a=inner ℝ (actualFeatureVector x) b at h
    rw [real_inner_comm,inner_sub_right,h,sub_self]
  exact sub_eq_zero.mp hz

@[instance_reducible]
def actualGaussianRKHS : RKHS ℝ ActualCoefficientSpace ℝ ℝ where
  coeCLM := actualGaussianEvaluation
  coeCLM_injective := actual_gaussian_function_evaluation_is_injective

def actualGaussianHilbertBasis : HilbertBasis ℕ ℝ ActualCoefficientSpace :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℝ ActualCoefficientSpace)

theorem actual_constructed_rkhs_has_the_literal_gaussian_kernel :
    letI : RKHS ℝ ActualCoefficientSpace ℝ ℝ := actualGaussianRKHS
    ∀ x y : ℝ, (RKHS.kernel ActualCoefficientSpace x y) 1=actualGaussianKernel x y := by
  letI : RKHS ℝ ActualCoefficientSpace ℝ ℝ := actualGaussianRKHS
  have heval (c : ActualCoefficientSpace) (x : ℝ) :
      (RKHS.coeCLM ℝ) c x=inner ℝ (actualFeatureVector x) c := rfl
  have hker (x : ℝ) : RKHS.kerFun ActualCoefficientSpace x (1:ℝ)=actualFeatureVector x := by
    apply ext_inner_right ℝ
    intro c
    have h := RKHS.kerFun_inner (H:=ActualCoefficientSpace) x (1:ℝ) c
    change inner ℝ (RKHS.kerFun ActualCoefficientSpace x (1:ℝ)) c=
      inner ℝ (1:ℝ) ((RKHS.coeCLM ℝ) c x) at h
    rw [heval] at h
    simpa only [RCLike.inner_apply,conj_trivial,one_mul] using h
  intro x y
  have h := RKHS.kernel_inner (H:=ActualCoefficientSpace) x y (1:ℝ) (1:ℝ)
  rw [hker x,hker y] at h
  have hsym : actualGaussianKernel y x=actualGaussianKernel x y := by
    unfold actualGaussianKernel
    congr 1
    ring
  simpa only [RCLike.inner_apply,conj_trivial,one_mul,mul_one,
    actual_infinite_hilbert_feature_inner_product_is_the_literal_gaussian_kernel,hsym] using h

theorem actual_printed_infinite_features_are_the_function_values_of_an_orthonormal_hilbert_basis :
    letI : RKHS ℝ ActualCoefficientSpace ℝ ℝ := actualGaussianRKHS
    Orthonormal ℝ actualGaussianHilbertBasis ∧
      (∀ n x, (RKHS.coeCLM ℝ) (actualGaussianHilbertBasis n) x=actualGaussianFeature n x) := by
  letI : RKHS ℝ ActualCoefficientSpace ℝ ℝ := actualGaussianRKHS
  refine ⟨actualGaussianHilbertBasis.orthonormal,?_⟩
  intro n x
  have hb : actualGaussianHilbertBasis n=lp.single 2 n (1:ℝ) := by
    rw [← actualGaussianHilbertBasis.repr_symm_single n]
    rfl
  rw [hb]
  change inner ℝ (actualFeatureVector x) (lp.single 2 n (1:ℝ))=actualGaussianFeature n x
  rw [real_inner_comm]
  simp only [lp.inner_single_left,RCLike.inner_apply,conj_trivial,one_mul,
    actual_feature_vector_coordinates]

theorem actual_source_function_belongs_to_the_genuine_gaussian_rkhs_with_exact_norm :
    letI : RKHS ℝ ActualCoefficientSpace ℝ ℝ := actualGaussianRKHS
    (∀ x : ℝ, (RKHS.coeCLM ℝ) actualSourceCoefficient x=actualGapFunction x) ∧
      ‖actualSourceCoefficient‖=Real.sqrt (326409/160000:ℝ) ∧
      |‖actualSourceCoefficient‖-(357/250:ℝ)| < 1/2000 := by
  letI : RKHS ℝ ActualCoefficientSpace ℝ ℝ := actualGaussianRKHS
  have hn : ‖actualSourceCoefficient‖=Real.sqrt (326409/160000:ℝ) := by
    rw [← actual_source_coefficient_has_exact_squared_hilbert_norm,Real.sqrt_sq (norm_nonneg _)]
  refine ⟨?_,hn,?_⟩
  · intro x
    change inner ℝ (actualFeatureVector x) actualSourceCoefficient=actualGapFunction x
    rw [real_inner_comm,actual_source_coefficient_evaluates_to_the_printed_gap_function]
  · rw [hn]
    exact actual_source_coefficient_squared_norm_and_nearest_three_decimal_norm_are_exact.2

end SafeLearning.CompleteModulesSafeOptGaussianGapRKHS
