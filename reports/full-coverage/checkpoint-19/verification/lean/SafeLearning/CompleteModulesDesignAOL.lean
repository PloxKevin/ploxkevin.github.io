import SafeLearning.CompleteModulesSLLExamples
import SafeLearning.CompleteModulesLipSDPWalkthrough

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix Polynomial
open scoped BigOperators Matrix.Norms.L2Operator
namespace SafeLearning.CompleteModulesDesignAOL
open CompleteModulesSLLExamples CompleteModulesLipSDP CompleteModulesLipSDPProduct

def sourceD : Matrix (Fin 2) (Fin 2) ℝ := diagonal ![1/Real.sqrt 2,1/Real.sqrt 3]
def sourceLayer : Matrix (Fin 2) (Fin 2) ℝ := actualSourceWeights*sourceD
def sourceGram : Matrix (Fin 2) (Fin 2) ℝ := sourceD*actualSourceWeightsᵀ*actualSourceWeights*sourceD

theorem actual_source_scale_gram_and_certificate :
    actualFirstMajorizer=diagonal ![(2:ℝ),3] ∧
      sourceDᵀ=sourceD ∧ sourceLayerᵀ*sourceLayer=sourceGram ∧
      sourceGram=!![1/2,1/Real.sqrt 6;1/Real.sqrt 6,2/3] ∧
      (actualFirstMajorizer-actualSourceWeightsᵀ*actualSourceWeights).PosSemidef := by
  have hp2 : Real.sqrt (2:ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hp3 : Real.sqrt (3:ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hs2:=Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  have hs3:=Real.sq_sqrt (show (0:ℝ)≤3 by norm_num)
  have hm : Real.sqrt (6:ℝ)=Real.sqrt 2*Real.sqrt 3 := by
    convert (Real.sqrt_mul (show (0:ℝ)≤2 by norm_num) (3:ℝ)) using 1 <;>norm_num
  refine ⟨actual_first_scale_majorizer,?_,?_,?_,actual_both_source_certificates_are_positive_semidefinite.1⟩
  · simp [sourceD]
  · unfold sourceLayer sourceGram
    rw [Matrix.transpose_mul]
    have hd : sourceDᵀ=sourceD := by simp [sourceD]
    rw [hd]
    simp only [Matrix.mul_assoc]
  · unfold sourceGram
    rw [Matrix.mul_assoc sourceD actualSourceWeightsᵀ actualSourceWeights,actual_source_gram_matrix]
    unfold sourceD
    ext i j;fin_cases i <;>fin_cases j <;>
      norm_num [Matrix.mul_apply,Fin.sum_univ_two,diagonal_apply,hm]
    all_goals field_simp
    all_goals nlinarith [hs2,hs3]

theorem actual_source_trace_determinant_full_characteristic_roots (eigenvalue : ℝ) :
    sourceGram.trace=7/6 ∧ sourceGram.det=1/6 ∧
      sourceGram.charpoly=(X-C 1)*(X-C (1/6)) ∧
      (eigenvalue ∈ spectrum ℝ sourceGram ↔ eigenvalue=1 ∨ eigenvalue=1/6) := by
  have he:=actual_source_scale_gram_and_certificate.2.2.2.1
  have hs6:=Real.sq_sqrt (show (0:ℝ)≤6 by norm_num)
  have hi : (1/Real.sqrt (6:ℝ))^2=1/6 := by rw [_root_.one_div_pow,hs6]
  simp only [one_div] at hi
  have ht : sourceGram.trace=7/6 := by rw [he];norm_num [Matrix.trace,Fin.sum_univ_two]
  have hd : sourceGram.det=1/6 := by rw [he,Matrix.det_fin_two];norm_num;nlinarith [hi]
  have hc : sourceGram.charpoly=(X-C 1)*(X-C (1/6)) := by
    rw [Matrix.charpoly_fin_two,ht,hd]
    have hC : C (7/6:ℝ)=(1:ℝ[X])+C (1/6) := by
      rw [show (7/6:ℝ)=1+1/6 by norm_num,map_add,map_one]
    rw [hC]
    norm_num
    ring
  refine ⟨ht,hd,hc,?_⟩
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly,Polynomial.IsRoot,hc]
  simp [mul_eq_zero,sub_eq_zero]

theorem actual_source_layer_every_input_quadratic_energy_gap (input : Fin 2 → ℝ) :
    (∑ i,input i^2)-(∑ i,((sourceLayer *ᵥ input) i)^2)=
      (input 0/Real.sqrt 2-input 1/Real.sqrt 3)^2 := by
  have hs2:=Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  have hs3:=Real.sq_sqrt (show (0:ℝ)≤3 by norm_num)
  have hi2 : (1/Real.sqrt (2:ℝ))^2=1/2 := by rw [_root_.one_div_pow,hs2]
  have hi3 : (1/Real.sqrt (3:ℝ))^2=1/3 := by rw [_root_.one_div_pow,hs3]
  simp [sourceLayer,sourceD,actualSourceWeights,Matrix.mul_apply,Matrix.mulVec,
    Matrix.vecMul,dotProduct,Fin.sum_univ_two,diagonal_apply]
  simp only [div_eq_mul_inv] at *
  nlinarith [hi2,hi3]

theorem actual_source_layer_exact_operator_norm_one : ‖sourceLayer‖=1 := by
  have hu : ‖sourceLayer‖≤1 := by
    have h:=CompleteModulesLipSDPWalkthrough.actual_spectral_norm_le_of_quadratic_bound sourceLayer 1
      (by norm_num) (fun input => by
        have hg:=actual_source_layer_every_input_quadratic_energy_gap input
        nlinarith [sq_nonneg (input 0/Real.sqrt 2-input 1/Real.sqrt 3)])
    simpa using h
  let input : Fin 2 → ℝ := ![Real.sqrt 2,Real.sqrt 3]
  have hi : ‖WithLp.toLp 2 input‖^2=5 := by
    rw [squared_norm_of_coordinates]
    norm_num [input,Fin.sum_univ_two,Real.sq_sqrt]
  have hout : sourceLayer *ᵥ input=![(2:ℝ),1] := by
    have hp2 : Real.sqrt (2:ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    have hp3 : Real.sqrt (3:ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    have hscaled : sourceD *ᵥ input=![(1:ℝ),1] := by
      ext i;fin_cases i <;>simp [sourceD,Matrix.mulVec_diagonal,input,hp2,hp3]
    rw [sourceLayer,←Matrix.mulVec_mulVec,hscaled]
    ext i;fin_cases i <;>norm_num [actualSourceWeights,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  have ho : ‖WithLp.toLp 2 (sourceLayer *ᵥ input)‖^2=5 := by
    rw [hout,squared_norm_of_coordinates]
    norm_num [Fin.sum_univ_two]
  have hgain:=actual_spectral_matrix_gain sourceLayer input
  have hsq : ‖WithLp.toLp 2 (sourceLayer *ᵥ input)‖^2≤‖sourceLayer‖^2*‖WithLp.toLp 2 input‖^2 := by
    nlinarith [norm_nonneg (WithLp.toLp 2 (sourceLayer *ᵥ input)),norm_nonneg sourceLayer,
      norm_nonneg (WithLp.toLp 2 input),mul_nonneg (norm_nonneg sourceLayer) (norm_nonneg (WithLp.toLp 2 input))]
  rw [hi,ho] at hsq
  nlinarith [norm_nonneg sourceLayer]

end SafeLearning.CompleteModulesDesignAOL
