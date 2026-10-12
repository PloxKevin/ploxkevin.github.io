import SafeLearning.CompleteModulesSafeOptEightPointPosteriors

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators Matrix
namespace SafeLearning.CompleteModulesSafeOptPositiveVariance
open CompleteModulesSafeOptEightPointPosteriors

theorem actual_every_finite_psd_kernel_posterior_has_strictly_positive_variance_with_positive_regularization
    {D I : Type*} [Fintype D] [Fintype I] [DecidableEq I]
    (kernel : D → D → ℝ) (hkernel : (Matrix.of kernel).PosSemidef)
    (input : I → D) (target : D) (regularizer : ℝ)
    (hreg : 0 < regularizer) (htarget : 0 < kernel target target) :
    0 < actualGPVariance kernel input regularizer target := by
  classical
  let A := actualGPMatrix kernel input regularizer
  let c := actualGPCross kernel input target
  let w : I → ℝ := A⁻¹ *ᵥ c
  have hu : IsUnit A :=
    (actual_positive_regularization_of_a_true_psd_kernel_gives_an_invertible_gp_matrix
      kernel hkernel input regularizer hreg).2
  have hnormal : A *ᵥ w=c := by
    dsimp [w]
    rw [Matrix.mulVec_mulVec,A.mul_nonsing_inv (Matrix.isUnit_iff_isUnit_det A |>.mp hu),Matrix.one_mulVec]
  have hrow (i : I) : (∑ j, kernel (input i) (input j)*w j)+regularizer*w i=
      kernel (input i) target := by
    have h := congrFun hnormal i
    change ((Matrix.of (fun i j => kernel (input i) (input j))+regularizer • 1) *ᵥ w) i=
      kernel (input i) target at h
    simp only [Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,Pi.add_apply,
      Pi.smul_apply,smul_eq_mul] at h
    simpa [Matrix.mulVec,dotProduct] using h
  let data : Option I → D := fun j => j.elim target input
  let v : Option I → ℝ := fun j => j.elim 1 (fun i => -w i)
  let G := (Matrix.of kernel).submatrix data data
  have hG : G.PosSemidef := hkernel.submatrix data
  have hsym (i : I) : kernel target (input i)=kernel (input i) target := by
    simpa using hkernel.isHermitian.apply (input i) target
  have hnone : (G *ᵥ v) none=actualGPVariance kernel input regularizer target := by
    simp [G,data,v,Matrix.mulVec,dotProduct,Fintype.sum_option,actualGPVariance,
      actualGPCross,A,c,w,hsym,Finset.sum_neg_distrib]
    ring
  have hsome (i : I) : (G *ᵥ v) (some i)=regularizer*w i := by
    have h := hrow i
    simp [G,data,v,Matrix.mulVec,dotProduct,Fintype.sum_option,Finset.sum_neg_distrib]
    linarith
  have hquad : star v ⬝ᵥ (G *ᵥ v)=actualGPVariance kernel input regularizer target-
      regularizer*∑ i, (w i)^2 := by
    simp [dotProduct,Fintype.sum_option,v,hnone,hsome,Finset.mul_sum]
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hnonneg := hG.dotProduct_mulVec_nonneg v
  rw [hquad] at hnonneg
  have hsum : 0 ≤ ∑ i, (w i)^2 := Finset.sum_nonneg (fun i _ => sq_nonneg (w i))
  by_contra hn
  have hvariance : actualGPVariance kernel input regularizer target ≤ 0 := le_of_not_gt hn
  have hsumzero : (∑ i, (w i)^2)=0 := by nlinarith
  have hw : w=0 := by
    funext i
    have hi : (w i)^2 ≤ ∑ j, (w j)^2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (w j)) (Finset.mem_univ i)
    rw [hsumzero] at hi
    change w i=0
    nlinarith [sq_nonneg (w i)]
  have hv : actualGPVariance kernel input regularizer target=kernel target target := by
    change kernel target target-c ⬝ᵥ w=kernel target target
    rw [hw]
    simp
  rw [hv] at hvariance
  linarith

theorem actual_noiseless_source_rank_one_kernel_can_have_zero_residual_variance_at_five :
    actualGPVariance actualSourceRankOneKernel (fun _ : Fin 1 => 2) 0 5=0 := by
  have h := actual_one_observation_gp_matrix_formulas_are_the_true_scalar_mean_and_variance
    actualSourceRankOneKernel 2 5 0 2
  norm_num [actualSourceRankOneKernel,CompleteModulesSafeOptEightPointReachability.actualValue] at h
  exact h.2

end SafeLearning.CompleteModulesSafeOptPositiveVariance
