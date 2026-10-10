import Mathlib
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedCovariance
open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal

def covarianceMatrix {Ω I : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : I → Ω → ℝ) : Matrix I I ℝ :=
  fun i j => covariance (X i) (X j) μ

theorem covariance_matrix_entry {Ω I : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : I → Ω → ℝ) (i j : I) :
    covarianceMatrix μ X i j=
      ∫ omega,(X i omega-(∫ w,X i w ∂μ))*(X j omega-(∫ w,X j w ∂μ)) ∂μ := rfl

theorem covariance_matrix_hermitian {Ω I : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : I → Ω → ℝ) : (covarianceMatrix μ X).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [star_trivial,covarianceMatrix]
  exact covariance_comm _ _

theorem covariance_quadratic_is_variance {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : I → Ω → ℝ)
    (hX : ∀ i,MemLp (X i) 2 μ) (v : I → ℝ) :
    dotProduct v ((covarianceMatrix μ X).mulVec v)=
      variance (fun omega => ∑ i,v i*X i omega) μ := by
  rw [variance_fun_sum (fun i => (hX i).const_mul (v i))]
  simp only [Matrix.mulVec,dotProduct,covarianceMatrix]
  simp_rw [Finset.mul_sum,covariance_const_mul_left,covariance_const_mul_right]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem covariance_matrix_posSemidef {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : I → Ω → ℝ)
    (hX : ∀ i,MemLp (X i) 2 μ) : (covarianceMatrix μ X).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨covariance_matrix_hermitian μ X,?_⟩
  intro v
  simp only [star_trivial]
  rw [covariance_quadratic_is_variance μ X hX v]
  exact variance_nonneg _ _

theorem variance_zero_iff_constant {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → ℝ) (hZ : MemLp Z 2 μ) :
    variance Z μ=0 ↔ ∃ c : ℝ,Z=ᵐ[μ] fun _ => c := by
  constructor
  · intro h
    exact ⟨∫ omega,Z omega ∂μ,ae_eq_integral_of_variance_eq_zero hZ h⟩
  · rintro ⟨c,hc⟩
    rw [variance_congr hc,variance_eq_integral (by fun_prop)]
    simp

theorem covariance_posDef_iff_no_constant_combination {Ω I : Type*}
    [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : I → Ω → ℝ)
    (hX : ∀ i,MemLp (X i) 2 μ) :
    (covarianceMatrix μ X).PosDef ↔
      ∀ v : I → ℝ,v≠0 → ¬ ∃ c : ℝ,(fun omega => ∑ i,v i*X i omega)=ᵐ[μ] fun _ => c := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  simp only [star_trivial]
  constructor
  · rintro ⟨hh,hpos⟩ v hv hc
    have hZ : MemLp (fun omega => ∑ i,v i*X i omega) 2 μ := by
      simpa only [Finset.sum_fn] using
        (memLp_finsetSum' Finset.univ (fun i _ => (hX i).const_mul (v i)))
    have hz := (variance_zero_iff_constant μ _ hZ).mpr hc
    have hp := hpos hv
    rw [covariance_quadratic_is_variance μ X hX v,hz] at hp
    exact (lt_irrefl (0:ℝ)) hp
  · intro h
    refine ⟨covariance_matrix_hermitian μ X,?_⟩
    intro v hv
    rw [covariance_quadratic_is_variance μ X hX v]
    have hZ : MemLp (fun omega => ∑ i,v i*X i omega) 2 μ := by
      simpa only [Finset.sum_fn] using
        (memLp_finsetSum' Finset.univ (fun i _ => (hX i).const_mul (v i)))
    have hn : variance (fun omega => ∑ i,v i*X i omega) μ≠0 := by
      intro hz
      exact h v hv ((variance_zero_iff_constant μ _ hZ).mp hz)
    exact lt_of_le_of_ne (variance_nonneg _ _) hn.symm

theorem covariance_invertible_of_no_constant_combination {Ω I : Type*}
    [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : I → Ω → ℝ)
    (hX : ∀ i,MemLp (X i) 2 μ)
    (h : ∀ v : I → ℝ,v≠0 → ¬ ∃ c : ℝ,
      (fun omega => ∑ i,v i*X i omega)=ᵐ[μ] fun _ => c) :
    IsUnit (covarianceMatrix μ X) :=
  ((covariance_posDef_iff_no_constant_combination μ X hX).mpr h).isUnit

theorem affine_covariance_transform {Ω I J : Type*} [MeasurableSpace Ω]
    [Fintype I] [Fintype J]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : I → Ω → ℝ)
    (hX : ∀ i,MemLp (X i) 2 μ) (A : Matrix J I ℝ) (b : J → ℝ) :
    covarianceMatrix μ (fun j omega => (∑ i,A j i*X i omega)+b j)=
      A*covarianceMatrix μ X*A.transpose := by
  ext j k
  have hj : MemLp (fun omega => ∑ i,A j i*X i omega) 2 μ := by
    simpa only [Finset.sum_fn] using
      (memLp_finsetSum' Finset.univ (fun i _ => (hX i).const_mul (A j i)))
  have hk : MemLp (fun omega => ∑ i,A k i*X i omega) 2 μ := by
    simpa only [Finset.sum_fn] using
      (memLp_finsetSum' Finset.univ (fun i _ => (hX i).const_mul (A k i)))
  change covariance (fun omega => (∑ i,A j i*X i omega)+b j)
    (fun omega => (∑ i,A k i*X i omega)+b k) μ =
    (A*covarianceMatrix μ X*A.transpose) j k
  rw [covariance_add_const_left (hj.integrable (by norm_num)),
    covariance_add_const_right (hk.integrable (by norm_num)),
    covariance_fun_sum_fun_sum (fun i => (hX i).const_mul (A j i))
      (fun i => (hX i).const_mul (A k i))]
  simp only [Matrix.mul_apply,Matrix.transpose_apply,covarianceMatrix]
  simp_rw [covariance_const_mul_left,covariance_const_mul_right,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro l hl
  ring

end SafeLearning.CompleteAppliedCovariance
