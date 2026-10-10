import SafeLearning.CompleteModulesKernel
import SafeLearning.CompleteModulesMatrixGP

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Matrix Filter
open scoped BigOperators Topology
namespace SafeLearning.CompleteModulesGramBridge

open CompleteModulesKernel
variable {H X I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Fintype I] [DecidableEq I]

def featureGram (feature : I → H) : Matrix I I ℝ := Matrix.gram ℝ feature

theorem feature_gram_positive_semidefinite (feature : I → H) :
    (featureGram feature).PosSemidef := Matrix.posSemidef_gram ℝ feature

theorem positive_regularization_gram_positive_definite (feature : I → H)
    (regularizer : ℝ) (hpos : 0<regularizer) :
    (CompleteModulesMatrixGP.ridgeMatrix (featureGram feature) regularizer).PosDef :=
  Matrix.PosDef.posSemidef_add (feature_gram_positive_semidefinite feature)
    ((Matrix.PosDef.one : (1 : Matrix I I ℝ).PosDef).smul hpos)

theorem positive_regularization_determinant_nonzero (feature : I → H)
    (regularizer : ℝ) (hpos : 0<regularizer) :
    (CompleteModulesMatrixGP.ridgeMatrix (featureGram feature) regularizer).det≠0 :=
  (positive_regularization_gram_positive_definite feature regularizer hpos).det_pos.ne'

theorem regularized_gram_action (feature : I → H) (regularizer : ℝ) (weight : I → ℝ) :
    CompleteModulesMatrixGP.ridgeMatrix (featureGram feature) regularizer *ᵥ weight=
      normalOperator feature regularizer weight := by
  rw [CompleteModulesMatrixGP.ridgeMatrix,Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec]
  ext i
  rfl

theorem inverse_weights_solve_normal_system (feature : I → H) (regularizer : ℝ)
    (hdet : (CompleteModulesMatrixGP.ridgeMatrix (featureGram feature) regularizer).det≠0)
    (labels : I → ℝ) :
    ∀ i, (∑ j, inner ℝ (feature i) (feature j)*
      ((CompleteModulesMatrixGP.ridgeMatrix (featureGram feature) regularizer)⁻¹ *ᵥ labels) j)+
        regularizer*((CompleteModulesMatrixGP.ridgeMatrix (featureGram feature) regularizer)⁻¹ *ᵥ labels) i=labels i := by
  letI := Matrix.invertibleOfIsUnitDet
    (CompleteModulesMatrixGP.ridgeMatrix (featureGram feature) regularizer)
    (isUnit_iff_ne_zero.mpr hdet)
  have hm : CompleteModulesMatrixGP.ridgeMatrix (featureGram feature) regularizer *ᵥ
      ((CompleteModulesMatrixGP.ridgeMatrix (featureGram feature) regularizer)⁻¹ *ᵥ labels)=labels := by
    rw [Matrix.mulVec_mulVec,Matrix.mul_inv_of_invertible,Matrix.one_mulVec]
  rw [regularized_gram_action] at hm
  exact fun i => congrFun hm i

theorem feature_gram_positive_definite_iff_independent (feature : I → H) :
    (featureGram feature).PosDef ↔ LinearIndependent ℝ feature :=
  Matrix.posDef_gram_iff_linearIndependent

section ActualRKHS
variable [CompleteSpace H] [RKHS ℝ H X ℝ]

def actualGram (input : I → X) : Matrix I I ℝ :=
  featureGram (fun i => scalarSection (H:=H) (input i))

def actualMeanFunction (input : I → X) (labels : I → ℝ) (regularizer : ℝ) : H :=
  combination (fun i => scalarSection (H:=H) (input i))
    ((CompleteModulesMatrixGP.ridgeMatrix (actualGram (H:=H) input) regularizer)⁻¹ *ᵥ labels)

theorem actual_gram_entry (input : I → X) (i j : I) :
    actualGram (H:=H) input i j=scalarKernel (H:=H) (input i) (input j) := rfl

theorem actual_mean_is_matrix_posterior (input : I → X) (labels : I → ℝ)
    (regularizer : ℝ) (x : X) :
    (actualMeanFunction (H:=H) input labels regularizer) x=
      CompleteModulesMatrixGP.posteriorMean (actualGram (H:=H) input)
        (fun i => scalarKernel (H:=H) x (input i)) labels regularizer := by
  rw [← scalar_section_reproduces]
  simp only [actualMeanFunction,combination_inner,CompleteModulesMatrixGP.posteriorMean,dotProduct]
  apply Finset.sum_congr rfl
  intro i hi
  rw [real_inner_comm]
  simp only [scalarKernel,featureKernel]
  ring

theorem actual_inverse_mean_globally_minimizes_ridge (input : I → X) (labels : I → ℝ)
    (regularizer : ℝ) (hpos : 0<regularizer) :
    ∀ competitor : H, actualRidgeObjective input labels regularizer
      (actualMeanFunction (H:=H) input labels regularizer) ≤
        actualRidgeObjective input labels regularizer competitor := by
  have hs := inverse_weights_solve_normal_system (fun i => scalarSection (H:=H) (input i))
    regularizer (positive_regularization_determinant_nonzero _ regularizer hpos) labels
  exact (actual_rkhs_ridge_solution input labels _ regularizer hpos hs).2

theorem actual_inverse_interpolant_data (input : I → X) (labels : I → ℝ)
    (hgram : (actualGram (H:=H) input).PosDef) :
    ∀ i, (actualMeanFunction (H:=H) input labels 0) (input i)=labels i := by
  have hdet : (CompleteModulesMatrixGP.ridgeMatrix (actualGram (H:=H) input) 0).det≠0 := by
    simpa [CompleteModulesMatrixGP.ridgeMatrix] using hgram.det_pos.ne'
  have hs := inverse_weights_solve_normal_system (fun i => scalarSection (H:=H) (input i)) 0 hdet labels
  intro i
  rw [← scalar_section_reproduces]
  simp only [actualMeanFunction,combination_inner]
  simpa only [actualGram,zero_mul,add_zero,mul_comm,real_inner_comm] using hs i

theorem actual_inverse_interpolant_minimum_norm (input : I → X) (labels : I → ℝ)
    (hgram : (actualGram (H:=H) input).PosDef) (competitor : H)
    (hdata : ∀ i, competitor (input i)=labels i) :
    ‖actualMeanFunction (H:=H) input labels 0‖≤‖competitor‖ := by
  have hdet : (CompleteModulesMatrixGP.ridgeMatrix (actualGram (H:=H) input) 0).det≠0 := by
    simpa [CompleteModulesMatrixGP.ridgeMatrix] using hgram.det_pos.ne'
  have hs : ∀ i, (∑ j, inner ℝ (scalarSection (H:=H) (input i))
      (scalarSection (H:=H) (input j))*
      ((CompleteModulesMatrixGP.ridgeMatrix (actualGram (H:=H) input) 0)⁻¹ *ᵥ labels) j)=labels i := by
    simpa only [actualGram,zero_mul,add_zero] using inverse_weights_solve_normal_system
      (fun i => scalarSection (H:=H) (input i)) 0 hdet labels
  exact interpolant_minimum_norm (fun i => scalarSection (H:=H) (input i)) labels _ hs
    competitor (by simpa only [scalar_section_reproduces] using hdata)

theorem actual_inverse_interpolant_unique_minimum (input : I → X) (labels : I → ℝ)
    (hgram : (actualGram (H:=H) input).PosDef) (competitor : H)
    (hdata : ∀ i, competitor (input i)=labels i)
    (hnorm : ‖competitor‖=‖actualMeanFunction (H:=H) input labels 0‖) :
    competitor=actualMeanFunction (H:=H) input labels 0 := by
  have hdet : (CompleteModulesMatrixGP.ridgeMatrix (actualGram (H:=H) input) 0).det≠0 := by
    simpa [CompleteModulesMatrixGP.ridgeMatrix] using hgram.det_pos.ne'
  have hs : ∀ i, (∑ j, inner ℝ (scalarSection (H:=H) (input i))
      (scalarSection (H:=H) (input j))*
      ((CompleteModulesMatrixGP.ridgeMatrix (actualGram (H:=H) input) 0)⁻¹ *ᵥ labels) j)=labels i := by
    simpa only [actualGram,zero_mul,add_zero] using inverse_weights_solve_normal_system
      (fun i => scalarSection (H:=H) (input i)) 0 hdet labels
  exact interpolant_minimum_unique (fun i => scalarSection (H:=H) (input i)) labels _ hs
    competitor (by simpa only [scalar_section_reproduces] using hdata) hnorm

theorem actual_inverse_interpolant_squared_norm (input : I → X) (labels : I → ℝ)
    (hgram : (actualGram (H:=H) input).PosDef) :
    ‖actualMeanFunction (H:=H) input labels 0‖^2=
      labels ⬝ᵥ ((actualGram (H:=H) input)⁻¹ *ᵥ labels) := by
  have hdata := actual_inverse_interpolant_data input labels hgram
  rw [← real_inner_self_eq_norm_sq]
  change inner ℝ (combination (fun i => scalarSection (H:=H) (input i))
    ((CompleteModulesMatrixGP.ridgeMatrix (actualGram (H:=H) input) 0)⁻¹ *ᵥ labels))
    (actualMeanFunction (H:=H) input labels 0)=_
  rw [combination_inner]
  simp only [real_inner_comm,scalar_section_reproduces,hdata,
    CompleteModulesMatrixGP.ridgeMatrix,zero_smul,add_zero,dotProduct]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem actual_mean_zero_regularization_limit_in_rkhs (input : I → X) (labels : I → ℝ)
    (hgram : (actualGram (H:=H) input).PosDef) :
    Tendsto (actualMeanFunction (H:=H) input labels) (𝓝 0)
      (𝓝 (actualMeanFunction (H:=H) input labels 0)) := by
  have hw := CompleteModulesMatrixGP.mulVec_of_matrix_limit _ _ labels
    (CompleteModulesMatrixGP.inverse_zero_regularization_limit (actualGram (H:=H) input) hgram.det_pos.ne')
  have ht : Tendsto (fun regularizer : ℝ => combination
      (fun i => scalarSection (H:=H) (input i))
      ((CompleteModulesMatrixGP.ridgeMatrix (actualGram (H:=H) input) regularizer)⁻¹ *ᵥ labels))
      (𝓝 0) (𝓝 (combination (fun i => scalarSection (H:=H) (input i))
        ((actualGram (H:=H) input)⁻¹ *ᵥ labels))) := by
    unfold combination
    apply tendsto_finset_sum
    intro i hi
    exact ((tendsto_pi_nhds.mp hw) i).smul tendsto_const_nhds
  change Tendsto (fun regularizer : ℝ => combination
    (fun i => scalarSection (H:=H) (input i))
    ((CompleteModulesMatrixGP.ridgeMatrix (actualGram (H:=H) input) regularizer)⁻¹ *ᵥ labels))
    (𝓝 0) (𝓝 (combination (fun i => scalarSection (H:=H) (input i))
      ((CompleteModulesMatrixGP.ridgeMatrix (actualGram (H:=H) input) 0)⁻¹ *ᵥ labels)))
  simpa only [CompleteModulesMatrixGP.ridgeMatrix,zero_smul,add_zero] using ht

end ActualRKHS
end SafeLearning.CompleteModulesGramBridge
