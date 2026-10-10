import Mathlib

set_option autoImplicit false
noncomputable section
open Matrix Filter Asymptotics
open scoped BigOperators Topology Matrix.Norms.Operator
namespace SafeLearning.CompleteModulesMatrixGP

variable {I : Type*} [Fintype I] [DecidableEq I]

def ridgeMatrix (gram : Matrix I I ℝ) (regularizer : ℝ) : Matrix I I ℝ :=
  gram+regularizer • 1

def posteriorMean (gram : Matrix I I ℝ) (query labels : I → ℝ) (regularizer : ℝ) : ℝ :=
  query ⬝ᵥ ((ridgeMatrix gram regularizer)⁻¹ *ᵥ labels)

def posteriorVariance (gram : Matrix I I ℝ) (query : I → ℝ)
    (queryDiagonal regularizer : ℝ) : ℝ :=
  queryDiagonal-query ⬝ᵥ ((ridgeMatrix gram regularizer)⁻¹ *ᵥ query)

theorem inverse_zero_regularization_limit (gram : Matrix I I ℝ) (hdet : gram.det≠0) :
    Tendsto (fun regularizer : ℝ => (ridgeMatrix gram regularizer)⁻¹)
      (𝓝 0) (𝓝 gram⁻¹) := by
  have hr : ContinuousAt Ring.inverse gram.det := by
    simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hdet
  have hi := continuousAt_matrix_inv gram hr
  have hc : Continuous (ridgeMatrix gram) := by
    unfold ridgeMatrix
    fun_prop
  have ht : Tendsto (ridgeMatrix gram) (𝓝 0) (𝓝 gram) := by
    simpa only [ridgeMatrix,zero_smul,add_zero] using hc.tendsto 0
  exact hi.tendsto.comp ht

theorem mulVec_of_matrix_limit {index : Type*} {filter : Filter index}
    (matrix : index → Matrix I I ℝ) (limit : Matrix I I ℝ) (vector : I → ℝ)
    (hm : Tendsto matrix filter (𝓝 limit)) :
    Tendsto (fun index => matrix index *ᵥ vector) filter (𝓝 (limit *ᵥ vector)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  change Tendsto (fun index => ∑ j, matrix index i j*vector j) filter
    (𝓝 (∑ j, limit i j*vector j))
  apply tendsto_finset_sum
  intro j hj
  exact ((tendsto_pi_nhds.mp ((tendsto_pi_nhds.mp hm) i)) j).mul tendsto_const_nhds

theorem dotProduct_of_vector_limit {index : Type*} {filter : Filter index}
    (vector : index → I → ℝ) (limit query : I → ℝ)
    (hv : Tendsto vector filter (𝓝 limit)) :
    Tendsto (fun index => query ⬝ᵥ vector index) filter (𝓝 (query ⬝ᵥ limit)) := by
  unfold dotProduct
  apply tendsto_finset_sum
  intro i hi
  exact tendsto_const_nhds.mul ((tendsto_pi_nhds.mp hv) i)

theorem posterior_mean_zero_regularization_limit (gram : Matrix I I ℝ)
    (query labels : I → ℝ) (hdet : gram.det≠0) :
    Tendsto (posteriorMean gram query labels) (𝓝 0) (𝓝 (query ⬝ᵥ (gram⁻¹ *ᵥ labels))) := by
  exact dotProduct_of_vector_limit _ _ query
    (mulVec_of_matrix_limit _ _ labels (inverse_zero_regularization_limit gram hdet))

theorem posterior_variance_zero_regularization_limit (gram : Matrix I I ℝ)
    (query : I → ℝ) (queryDiagonal : ℝ) (hdet : gram.det≠0) :
    Tendsto (posteriorVariance gram query queryDiagonal) (𝓝 0)
      (𝓝 (queryDiagonal-query ⬝ᵥ (gram⁻¹ *ᵥ query))) := by
  exact tendsto_const_nhds.sub (dotProduct_of_vector_limit _ _ query
    (mulVec_of_matrix_limit _ _ query (inverse_zero_regularization_limit gram hdet)))

theorem regularized_solve_is_inverse_solution (gram : Matrix I I ℝ) (labels weight : I → ℝ)
    (regularizer : ℝ) (hdet : IsUnit (ridgeMatrix gram regularizer).det)
    (hsolve : ridgeMatrix gram regularizer *ᵥ weight=labels) :
    (ridgeMatrix gram regularizer)⁻¹ *ᵥ labels=weight := by
  let := Matrix.invertibleOfIsUnitDet (ridgeMatrix gram regularizer) hdet
  exact Matrix.inv_mulVec_eq_vec hsolve.symm

theorem normalized_inverse_small_parameter_limit (gram : Matrix I I ℝ) :
    Tendsto (fun parameter : ℝ => (1+parameter • gram)⁻¹) (𝓝 0)
      (𝓝 (1 : Matrix I I ℝ)) := by
  have hr : ContinuousAt Ring.inverse ((1 : Matrix I I ℝ).det) := by
    simpa only [Matrix.det_one,Ring.inverse_eq_inv'] using
      (continuousAt_inv₀ (by norm_num : (1:ℝ)≠0))
  have hi := continuousAt_matrix_inv (1 : Matrix I I ℝ) hr
  have hc : Continuous (fun parameter : ℝ => (1 : Matrix I I ℝ)+parameter • gram) := by fun_prop
  have ht : Tendsto (fun parameter : ℝ => (1 : Matrix I I ℝ)+parameter • gram) (𝓝 0)
      (𝓝 (1 : Matrix I I ℝ)) := by
    simpa only [zero_smul,add_zero] using hc.tendsto 0
  simpa only [Function.comp_def,inv_one] using hi.tendsto.comp ht

theorem normalized_inverse_second_order (gram : Matrix I I ℝ) :
    (fun parameter : ℝ => (1+parameter • gram)⁻¹-1+parameter • gram) =O[𝓝 0]
      (fun parameter : ℝ => parameter^2) := by
  have hc : Tendsto (fun parameter : ℝ => parameter • gram) (𝓝 0) (𝓝 0) := by
    have ht : Continuous (fun parameter : ℝ => parameter • gram) := by fun_prop
    simpa only [zero_smul] using ht.tendsto (0 : ℝ)
  have hb := (NormedRing.inverse_add_norm_diff_second_order
    (1 : (Matrix I I ℝ)ˣ)).comp_tendsto hc
  simp only [Function.comp_def,Units.val_one,inv_one,one_mul,mul_one,← Matrix.nonsing_inv_eq_ringInverse,
    norm_smul,Real.norm_eq_abs,mul_pow,sq_abs] at hb
  have hscale : (fun parameter : ℝ => parameter^2*‖gram‖^2) =O[𝓝 0]
      (fun parameter : ℝ => parameter^2) := by
    have hs := (isBigO_refl (fun parameter : ℝ => parameter^2) (𝓝 0)).const_mul_left (‖gram‖^2)
    convert hs using 1
    funext parameter
    ring
  exact hb.trans hscale

theorem normalized_inverse_large_regularization_limit (gram : Matrix I I ℝ) :
    Tendsto (fun regularizer : ℝ => (1+regularizer⁻¹ • gram)⁻¹) atTop
      (𝓝 (1 : Matrix I I ℝ)) :=
  (normalized_inverse_small_parameter_limit gram).comp tendsto_inv_atTop_zero

theorem regularized_inverse_eventual_scaling (gram : Matrix I I ℝ) :
    ∀ᶠ regularizer : ℝ in atTop,
      (ridgeMatrix gram regularizer)⁻¹=regularizer⁻¹ • (1+regularizer⁻¹ • gram)⁻¹ := by
  have hc : Continuous (fun parameter : ℝ => ((1 : Matrix I I ℝ)+parameter • gram).det) := by
    fun_prop
  have ht : Tendsto (fun regularizer : ℝ => ((1 : Matrix I I ℝ)+regularizer⁻¹ • gram).det)
      atTop (𝓝 (1:ℝ)) := by
    have hz : Tendsto (fun parameter : ℝ => ((1 : Matrix I I ℝ)+parameter • gram).det)
        (𝓝 0) (𝓝 (1:ℝ)) := by simpa only [zero_smul,add_zero,det_one] using hc.tendsto 0
    exact hz.comp tendsto_inv_atTop_zero
  have hnz : ∀ᶠ regularizer : ℝ in atTop,
      ((1 : Matrix I I ℝ)+regularizer⁻¹ • gram).det≠0 :=
    ht.eventually (eventually_ne_nhds (by norm_num : (1:ℝ)≠0))
  filter_upwards [hnz,eventually_gt_atTop (0:ℝ)] with regularizer hdet hpos
  let : Invertible regularizer := invertibleOfNonzero hpos.ne'
  have hfactor : ridgeMatrix gram regularizer=
      regularizer • ((1 : Matrix I I ℝ)+regularizer⁻¹ • gram) := by
    simp only [ridgeMatrix,smul_add,smul_smul,mul_inv_cancel₀ hpos.ne',one_smul]
    exact add_comm _ _
  rw [hfactor]
  have hi := Matrix.inv_smul (A:=((1 : Matrix I I ℝ)+regularizer⁻¹ • gram))
    regularizer (isUnit_iff_ne_zero.mpr hdet)
  simpa only [invOf_eq_inv] using hi

theorem inverse_infinite_regularization_limit (gram : Matrix I I ℝ) :
    Tendsto (fun regularizer : ℝ => (ridgeMatrix gram regularizer)⁻¹) atTop
      (𝓝 (0 : Matrix I I ℝ)) := by
  have ht := tendsto_inv_atTop_zero.smul (normalized_inverse_large_regularization_limit gram)
  have hz : Tendsto (fun regularizer : ℝ => regularizer⁻¹ • (1+regularizer⁻¹ • gram)⁻¹)
      atTop (𝓝 (0 : Matrix I I ℝ)) := by simpa only [zero_smul] using ht
  have he : (fun regularizer : ℝ => regularizer⁻¹ • (1+regularizer⁻¹ • gram)⁻¹) =ᶠ[atTop]
      (fun regularizer : ℝ => (ridgeMatrix gram regularizer)⁻¹) :=
    (regularized_inverse_eventual_scaling gram).mono (fun _ h => h.symm)
  exact hz.congr' he

theorem posterior_mean_infinite_regularization_limit (gram : Matrix I I ℝ) (query labels : I → ℝ) :
    Tendsto (posteriorMean gram query labels) atTop (𝓝 0) := by
  change Tendsto (fun regularizer : ℝ => query ⬝ᵥ ((ridgeMatrix gram regularizer)⁻¹ *ᵥ labels)) atTop (𝓝 0)
  have h := dotProduct_of_vector_limit _ _ query
    (mulVec_of_matrix_limit _ _ labels (inverse_infinite_regularization_limit gram))
  simpa only [zero_mulVec,dotProduct_zero] using h

theorem posterior_variance_infinite_regularization_limit (gram : Matrix I I ℝ)
    (query : I → ℝ) (queryDiagonal : ℝ) :
    Tendsto (posteriorVariance gram query queryDiagonal) atTop (𝓝 queryDiagonal) := by
  change Tendsto (fun regularizer : ℝ => queryDiagonal-query ⬝ᵥ ((ridgeMatrix gram regularizer)⁻¹ *ᵥ query)) atTop (𝓝 queryDiagonal)
  have hc : Tendsto (fun _ : ℝ => queryDiagonal) atTop (𝓝 queryDiagonal) := tendsto_const_nhds
  have h := hc.sub (dotProduct_of_vector_limit _ _ query
    (mulVec_of_matrix_limit _ _ query (inverse_infinite_regularization_limit gram)))
  simpa only [zero_mulVec,dotProduct_zero,sub_zero] using h

theorem inverse_infinite_regularization_second_order_remainder (gram : Matrix I I ℝ) :
    (fun regularizer : ℝ => (ridgeMatrix gram regularizer)⁻¹-
      regularizer⁻¹ • (1 : Matrix I I ℝ)+(regularizer⁻¹)^2 • gram) =O[atTop]
      (fun regularizer : ℝ => (regularizer⁻¹)^3) := by
  have hb := (normalized_inverse_second_order gram).comp_tendsto tendsto_inv_atTop_zero
  have hs := (isBigO_refl (fun regularizer : ℝ => regularizer⁻¹) atTop).smul hb
  simp only [Function.comp_def] at hs
  have hden : (fun regularizer : ℝ => regularizer⁻¹ • (regularizer⁻¹)^2)=
      (fun regularizer : ℝ => (regularizer⁻¹)^3) := by
    funext regularizer
    simp only [smul_eq_mul]
    ring
  rw [hden] at hs
  apply hs.congr' _ (Filter.EventuallyEq.refl _ _)
  filter_upwards [regularized_inverse_eventual_scaling gram] with regularizer hscale
  rw [hscale]
  simp only [smul_add,smul_sub,smul_smul]
  rw [show regularizer⁻¹*regularizer⁻¹=(regularizer⁻¹)^2 by ring]

end SafeLearning.CompleteModulesMatrixGP
