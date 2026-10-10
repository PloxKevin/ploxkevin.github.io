import SafeLearning.CompleteAppliedCovariance
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedCorrelation
open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal

def correlation {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X Y : Ω → ℝ) (sx sy : ℝ) : ℝ := covariance X Y μ/(sx*sy)

theorem variance_formulas {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : MemLp X 2 μ)
    (a b : ℝ) :
    variance X μ=(∫ omega,(X omega-(∫ w,X w ∂μ))^2 ∂μ) ∧
    variance X μ=(∫ omega,(X omega)^2 ∂μ)-(∫ w,X w ∂μ)^2 ∧
    variance (fun omega => a*X omega+b) μ=a^2*variance X μ := by
  refine ⟨variance_eq_integral hX.aemeasurable,variance_eq_sub hX,?_⟩
  rw [variance_add_const (hX.const_mul a).aestronglyMeasurable,
    variance_const_mul]

theorem covariance_standardized {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X Y : Ω → ℝ) (sx sy : ℝ) :
    covariance (fun omega => X omega/sx) (fun omega => Y omega/sy) μ=
      correlation μ X Y sx sy := by
  simp_rw [div_eq_mul_inv,mul_comm _ sx⁻¹,mul_comm _ sy⁻¹,
    covariance_const_mul_left,covariance_const_mul_right]
  unfold correlation
  ring

theorem correlation_variance_identity {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (sx sy s : ℝ)
    (hx : 0<sx) (hy : 0<sy) (hvx : variance X μ=sx^2)
    (hvy : variance Y μ=sy^2) (hs : s=1 ∨ s=-1) :
    variance (fun omega => (1/sy)*Y omega-s*(1/sx)*X omega) μ=
      2*(1-s*correlation μ X Y sx sy) := by
  have hs2 : s^2=1 := by rcases hs with rfl|rfl <;> norm_num
  change variance ((fun omega => (1/sy)*Y omega)-
    (fun omega => (s*(1/sx))*X omega)) μ= _
  rw [variance_sub (hY.const_mul _) (hX.const_mul _),variance_const_mul,
    variance_const_mul,covariance_const_mul_left,covariance_const_mul_right,
    covariance_comm Y X,hvx,hvy]
  unfold correlation
  field_simp
  rw [hs2]
  ring

theorem correlation_interval {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (sx sy : ℝ)
    (hx : 0<sx) (hy : 0<sy) (hvx : variance X μ=sx^2)
    (hvy : variance Y μ=sy^2) : |correlation μ X Y sx sy|≤1 := by
  have hp := variance_nonneg (fun omega => (1/sy)*Y omega-(1:ℝ)*(1/sx)*X omega) μ
  have hn := variance_nonneg (fun omega => (1/sy)*Y omega-(-1:ℝ)*(1/sx)*X omega) μ
  rw [correlation_variance_identity μ X Y hX hY sx sy 1 hx hy hvx hvy (Or.inl rfl)] at hp
  rw [correlation_variance_identity μ X Y hX hY sx sy (-1) hx hy hvx hvy (Or.inr rfl)] at hn
  rw [abs_le]
  constructor <;> linarith

theorem correlation_extreme_iff_affine {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (sx sy s : ℝ)
    (hx : 0<sx) (hy : 0<sy) (hvx : variance X μ=sx^2)
    (hvy : variance Y μ=sy^2) (hs : s=1 ∨ s=-1) :
    correlation μ X Y sx sy=s ↔
      ∃ b : ℝ,Y=ᵐ[μ] fun omega => (s*sy/sx)*X omega+b := by
  have hs2 : s^2=1 := by rcases hs with rfl|rfl <;> norm_num
  let Z : Ω → ℝ := fun omega => (1/sy)*Y omega-s*(1/sx)*X omega
  have hZ : MemLp Z 2 μ := (hY.const_mul (1/sy)).sub (hX.const_mul (s*(1/sx)))
  have hv : variance Z μ=2*(1-s*correlation μ X Y sx sy) :=
    correlation_variance_identity μ X Y hX hY sx sy s hx hy hvx hvy hs
  constructor
  · intro h
    have hz : variance Z μ=0 := by rw [hv,h];nlinarith [hs2]
    obtain ⟨c,hc⟩ := (SafeLearning.CompleteAppliedCovariance.variance_zero_iff_constant μ Z hZ).mp hz
    refine ⟨sy*c,?_⟩
    filter_upwards [hc] with omega homega
    dsimp [Z] at homega
    field_simp at homega ⊢
    nlinarith
  · rintro ⟨b,hb⟩
    have hc : Z=ᵐ[μ] fun _ => b/sy := by
      filter_upwards [hb] with omega homega
      dsimp [Z]
      rw [homega]
      field_simp
      ring
    have hz := (SafeLearning.CompleteAppliedCovariance.variance_zero_iff_constant μ Z hZ).mpr ⟨b/sy,hc⟩
    rw [hv] at hz
    rcases hs with rfl|rfl <;> linarith

theorem covariance_quadratic_centered_outer_products {Ω I : Type*}
    [MeasurableSpace Ω] [Fintype I] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : I → Ω → ℝ) (hX : ∀ i,MemLp (X i) 2 μ) (v : I → ℝ) :
    dotProduct v ((SafeLearning.CompleteAppliedCovariance.covarianceMatrix μ X).mulVec v)=
      ∫ omega,(∑ i,v i*(X i omega-(∫ w,X i w ∂μ)))^2 ∂μ := by
  rw [SafeLearning.CompleteAppliedCovariance.covariance_quadratic_is_variance μ X hX v]
  have hZ : MemLp (fun omega => ∑ i,v i*X i omega) 2 μ := by
    simpa only [Finset.sum_fn] using
      (memLp_finsetSum' Finset.univ (fun i _ => (hX i).const_mul (v i)))
  rw [variance_eq_integral hZ.aemeasurable,
    integral_finsetSum Finset.univ (fun i _ => (hX i).integrable (by norm_num) |>.const_mul (v i))]
  simp_rw [integral_const_mul,mul_sub,Finset.sum_sub_distrib]

theorem covariance_matrix_invertible_iff {Ω I : Type*} [MeasurableSpace Ω]
    [Fintype I] [DecidableEq I] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : I → Ω → ℝ) (hX : ∀ i,MemLp (X i) 2 μ) :
    IsUnit (SafeLearning.CompleteAppliedCovariance.covarianceMatrix μ X) ↔
      ∀ v : I → ℝ,v≠0 → ¬ ∃ c : ℝ,
        (fun omega => ∑ i,v i*X i omega)=ᵐ[μ] fun _ => c := by
  rw [← (SafeLearning.CompleteAppliedCovariance.covariance_matrix_posSemidef μ X hX).posDef_iff_isUnit]
  exact SafeLearning.CompleteAppliedCovariance.covariance_posDef_iff_no_constant_combination μ X hX

theorem standard_deviation_example : Real.sqrt (1/100:ℝ)=1/10 := by
  rw [show (1/100:ℝ)=(1/10:ℝ)^2 by norm_num,Real.sqrt_sq (by norm_num)]

theorem covariance_pair_matrix {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (sx sy : ℝ)
    (hx : 0<sx) (hy : 0<sy) (hvx : variance X μ=sx^2)
    (hvy : variance Y μ=sy^2) :
    SafeLearning.CompleteAppliedCovariance.covarianceMatrix μ (![X,Y] : Fin 2 → Ω → ℝ)=
      !![sx^2,correlation μ X Y sx sy*sx*sy;
        correlation μ X Y sx sy*sx*sy,sy^2] := by
  ext i j
  fin_cases i <;> fin_cases j
  · change covariance X X μ=sx^2
    exact (covariance_self hX.aemeasurable).trans hvx
  · change covariance X Y μ=correlation μ X Y sx sy*sx*sy
    unfold correlation;field_simp
  · change covariance Y X μ=correlation μ X Y sx sy*sx*sy
    rw [covariance_comm Y X];unfold correlation;field_simp
  · change covariance Y Y μ=sy^2
    exact (covariance_self hY.aemeasurable).trans hvy

theorem covariance_isotropic_entries {Ω I : Type*} [MeasurableSpace Ω]
    [Fintype I] [DecidableEq I] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : I → Ω → ℝ) (hX : ∀ i,MemLp (X i) 2 μ) (sigma : ℝ) :
    SafeLearning.CompleteAppliedCovariance.covarianceMatrix μ X=sigma^2 • (1:Matrix I I ℝ) ↔
      (∀ i,variance (X i) μ=sigma^2) ∧
      (∀ i j,i≠j → covariance (X i) (X j) μ=0) := by
  constructor
  · intro h
    constructor
    · intro i
      have hh := congrArg (fun M : Matrix I I ℝ => M i i) h
      simpa [SafeLearning.CompleteAppliedCovariance.covarianceMatrix,
        covariance_self (hX i).aemeasurable] using hh
    · intro i j hij
      have hh := congrArg (fun M : Matrix I I ℝ => M i j) h
      simpa [SafeLearning.CompleteAppliedCovariance.covarianceMatrix,Matrix.one_apply,hij] using hh
  · rintro ⟨hv,hc⟩
    ext i j
    by_cases hij : i=j
    · subst j
      simpa [SafeLearning.CompleteAppliedCovariance.covarianceMatrix,
        covariance_self (hX i).aemeasurable] using hv i
    · simpa [SafeLearning.CompleteAppliedCovariance.covarianceMatrix,Matrix.one_apply,hij] using hc i j hij

theorem isotropic_direction_variance {Ω I : Type*} [MeasurableSpace Ω]
    [Fintype I] [DecidableEq I] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : I → Ω → ℝ) (hX : ∀ i,MemLp (X i) 2 μ) (sigma : ℝ)
    (hc : SafeLearning.CompleteAppliedCovariance.covarianceMatrix μ X=sigma^2 • (1:Matrix I I ℝ))
    (v : I → ℝ) : variance (fun omega => ∑ i,v i*X i omega) μ=
      sigma^2*(∑ i,(v i)^2) := by
  rw [← SafeLearning.CompleteAppliedCovariance.covariance_quadratic_is_variance μ X hX v,hc]
  simp only [Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct,Pi.smul_apply,smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end SafeLearning.CompleteAppliedCorrelation
