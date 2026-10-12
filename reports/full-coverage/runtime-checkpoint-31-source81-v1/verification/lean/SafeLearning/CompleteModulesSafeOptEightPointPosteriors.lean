import SafeLearning.CompleteModulesSafeOptEightPointReachability

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators Matrix
namespace SafeLearning.CompleteModulesSafeOptEightPointPosteriors
open CompleteModulesSafeOptEightPointReachability

def actualGPMatrix {D I : Type*} [Fintype I] [DecidableEq I]
    (kernel : D → D → ℝ) (input : I → D) (regularizer : ℝ) : Matrix I I ℝ :=
  Matrix.of (fun i j => kernel (input i) (input j))+regularizer • 1

def actualGPCross {D I : Type*} (kernel : D → D → ℝ) (input : I → D) (target : D) : I → ℝ :=
  fun i => kernel (input i) target

def actualGPMean {D I : Type*} [Fintype I] [DecidableEq I]
    (kernel : D → D → ℝ) (input : I → D) (regularizer : ℝ) (labels : I → ℝ) (target : D) : ℝ :=
  (actualGPCross kernel input target) ⬝ᵥ ((actualGPMatrix kernel input regularizer)⁻¹ *ᵥ labels)

def actualGPVariance {D I : Type*} [Fintype I] [DecidableEq I]
    (kernel : D → D → ℝ) (input : I → D) (regularizer : ℝ) (target : D) : ℝ :=
  kernel target target-(actualGPCross kernel input target) ⬝ᵥ
    ((actualGPMatrix kernel input regularizer)⁻¹ *ᵥ (actualGPCross kernel input target))

theorem actual_positive_regularization_of_a_true_psd_kernel_gives_an_invertible_gp_matrix
    {D I : Type*} [Fintype D] [Fintype I] [DecidableEq I]
    (kernel : D → D → ℝ) (hkernel : (Matrix.of kernel).PosSemidef)
    (input : I → D) (regularizer : ℝ) (hreg : 0 < regularizer) :
    (actualGPMatrix kernel input regularizer).PosDef ∧ IsUnit (actualGPMatrix kernel input regularizer) := by
  have hg := hkernel.submatrix input
  have hr : (regularizer • (1:Matrix I I ℝ)).PosDef := Matrix.PosDef.one.smul hreg
  have hp : (actualGPMatrix kernel input regularizer).PosDef := by simpa [actualGPMatrix,Matrix.submatrix] using Matrix.PosDef.posSemidef_add hg hr
  exact ⟨hp,hp.isUnit⟩

theorem actual_one_observation_gp_matrix_formulas_are_the_true_scalar_mean_and_variance
    {D : Type*} (kernel : D → D → ℝ) (anchor target : D) (regularizer label : ℝ) :
    actualGPMean kernel (fun _ : Fin 1 => anchor) regularizer (fun _ => label) target=
      kernel anchor target/(kernel anchor anchor+regularizer)*label ∧
      actualGPVariance kernel (fun _ : Fin 1 => anchor) regularizer target=
        kernel target target-(kernel anchor target)^2/(kernel anchor anchor+regularizer) := by
  have hm : actualGPMatrix kernel (fun _ : Fin 1 => anchor) regularizer=
      Matrix.diagonal (fun _ : Fin 1 => kernel anchor anchor+regularizer) := by
    ext i j
    fin_cases i;fin_cases j
    simp [actualGPMatrix]
  simp only [actualGPMean,actualGPVariance,hm]
  simp [Matrix.mulVec,dotProduct,Ring.inverse_eq_inv,actualGPCross]
  constructor <;> ring

def actualDiagonalKernel (i j : Fin 8) : ℝ := if i=j then 1 else 0

def actualSourceRankOneKernel (i j : Fin 8) : ℝ := actualValue i*actualValue j

theorem actual_both_source_eight_point_kernels_are_genuinely_positive_semidefinite :
    (Matrix.of actualDiagonalKernel).PosSemidef ∧
      (Matrix.of actualSourceRankOneKernel).PosSemidef := by
  constructor
  · have he : (Matrix.of actualDiagonalKernel)=1 := by
      ext i j;simp [actualDiagonalKernel,Matrix.one_apply,Matrix.of_apply]
    rw [he];exact Matrix.PosSemidef.one
  · have he : Matrix.of actualSourceRankOneKernel=Matrix.vecMulVec actualValue (star actualValue) := by
      ext i j;simp [actualSourceRankOneKernel,Matrix.vecMulVec,Matrix.of_apply]
    rw [he]
    exact Matrix.posSemidef_vecMulVec_self_star actualValue

theorem actual_every_finite_diagonal_kernel_dataset_below_five_leaves_zero_mean_and_unit_residual_variance
    {I : Type*} [Fintype I] [DecidableEq I] (input : I → Fin 8)
    (hinput : ∀ i, (input i).val ≤ 4) (regularizer : ℝ) (labels : I → ℝ) :
    actualGPMean actualDiagonalKernel input regularizer labels 5=0 ∧
      actualGPVariance actualDiagonalKernel input regularizer 5=1 := by
  have hc : actualGPCross actualDiagonalKernel input 5=0 := by
    funext i
    have he : input i≠(5:Fin 8) := by intro he;have hi:=hinput i;rw [he] at hi;norm_num at hi
    simp [actualGPCross,actualDiagonalKernel,he]
  simp [actualGPMean,actualGPVariance,hc,actualDiagonalKernel]

theorem actual_positive_beta_cannot_certify_five_with_any_below_five_diagonal_kernel_dataset
    {I : Type*} [Fintype I] [DecidableEq I] (input : I → Fin 8)
    (hinput : ∀ i, (input i).val ≤ 4) (regularizer beta : ℝ) (labels : I → ℝ) (hb : 0 < beta) :
    ¬(0:ℝ) ≤ actualGPMean actualDiagonalKernel input regularizer labels 5-
      beta*Real.sqrt (actualGPVariance actualDiagonalKernel input regularizer 5) := by
  have hp := actual_every_finite_diagonal_kernel_dataset_below_five_leaves_zero_mean_and_unit_residual_variance input hinput regularizer labels
  rw [hp.1,hp.2]
  norm_num
  linarith

theorem actual_source_rank_one_kernel_can_certify_five_from_true_data_at_two
    : actualGPMean actualSourceRankOneKernel (fun _ : Fin 1 => 2) (1/100)
        (fun _ => actualValue 2) 5=(80/401:ℝ) ∧
      actualGPVariance actualSourceRankOneKernel (fun _ : Fin 1 => 2) (1/100) 5=(1/10025:ℝ) ∧
      (0:ℝ) ≤ actualGPMean actualSourceRankOneKernel (fun _ : Fin 1 => 2) (1/100)
        (fun _ => actualValue 2) 5-Real.sqrt
          (actualGPVariance actualSourceRankOneKernel (fun _ : Fin 1 => 2) (1/100) 5) := by
  have hp := actual_one_observation_gp_matrix_formulas_are_the_true_scalar_mean_and_variance
    actualSourceRankOneKernel 2 5 (1/100) (actualValue 2)
  norm_num [actualSourceRankOneKernel,actualValue] at hp
  refine ⟨hp.1,hp.2,?_⟩
  rw [show actualValue 2=(2:ℝ) by norm_num [actualValue],hp.1,hp.2]
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤1/10025)
  have hn := Real.sqrt_nonneg (1/10025:ℝ)
  nlinarith

def actualMisspecifiedConstantKernel (_i _j : Fin 2) : ℝ := 1

def actualMisspecifiedTruth (i : Fin 2) : ℝ := ![1,-1/5] i

theorem actual_valid_constant_kernel_can_overcertify_an_unsafe_point_when_the_truth_is_misspecified :
    (Matrix.of actualMisspecifiedConstantKernel).PosSemidef ∧
      actualMisspecifiedTruth 0=1 ∧ actualMisspecifiedTruth 1<0 ∧
      (0:ℝ) ≤ actualGPMean actualMisspecifiedConstantKernel (fun _ : Fin 1 => 0) (1/100)
        (fun _ => actualMisspecifiedTruth 0) 1-Real.sqrt
          (actualGPVariance actualMisspecifiedConstantKernel (fun _ : Fin 1 => 0) (1/100) 1) := by
  refine ⟨?_,by norm_num [actualMisspecifiedTruth],by norm_num [actualMisspecifiedTruth],?_⟩
  · have he : Matrix.of actualMisspecifiedConstantKernel=
        Matrix.vecMulVec (fun _ : Fin 2 => (1:ℝ)) (star (fun _ : Fin 2 => (1:ℝ))) := by
      ext i j;simp [actualMisspecifiedConstantKernel,Matrix.vecMulVec,Matrix.of_apply]
    rw [he]
    exact Matrix.posSemidef_vecMulVec_self_star (fun _ : Fin 2 => (1:ℝ))
  · have hp := actual_one_observation_gp_matrix_formulas_are_the_true_scalar_mean_and_variance
      actualMisspecifiedConstantKernel 0 1 (1/100) (actualMisspecifiedTruth 0)
    norm_num [actualMisspecifiedConstantKernel,actualMisspecifiedTruth] at hp
    rw [show actualMisspecifiedTruth 0=(1:ℝ) by norm_num [actualMisspecifiedTruth],hp.1,hp.2]
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤1/101)
    have hn := Real.sqrt_nonneg (1/101:ℝ)
    nlinarith

end SafeLearning.CompleteModulesSafeOptEightPointPosteriors
