import SafeLearning.CompleteModulesLoSBOPracticeRKHS

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Matrix Set
open scoped BigOperators
namespace SafeLearning.CompleteModulesLoSBOExtremalConfidence
open CompleteModulesKernel CompleteModulesGramBridge

variable {H X I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [RKHS ℝ H X ℝ] [Fintype I] [DecidableEq I]

def actualDataSpan (input : I → X) : Submodule ℝ H :=
  Submodule.span ℝ (Set.range (fun i => scalarSection (H:=H) (input i)))

instance actualDataSpanFiniteDimensional (input : I → X) :
    FiniteDimensional ℝ (actualDataSpan (H:=H) input) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

def actualResidual (input : I → X) (target : X) : H :=
  scalarSection (H:=H) target-actualMeanFunction input
    (fun i => scalarKernel (H:=H) (input i) target) 0

theorem actual_inverse_interpolant_is_in_the_actual_data_span
    (input : I → X) (labels : I → ℝ) :
    actualMeanFunction (H:=H) input labels 0 ∈ actualDataSpan (H:=H) input := by
  apply Submodule.sum_mem
  intro i hi
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩)

theorem actual_residual_vanishes_on_all_data_and_is_orthogonal_to_the_actual_data_span
    (input : I → X) (target : X) (hgram : (actualGram (H:=H) input).PosDef) :
    (∀ i, (actualResidual (H:=H) input target) (input i)=0) ∧
    (∀ v ∈ actualDataSpan (H:=H) input, inner ℝ (actualResidual (H:=H) input target) v=0) := by
  have hz : ∀ i, (actualResidual (H:=H) input target) (input i)=0 := by
    intro i
    simp only [actualResidual,RKHS.coe_sub,Pi.sub_apply,
      actual_inverse_interpolant_data input _ hgram]
    rw [←scalar_section_reproduces]
    simp only [scalarKernel,featureKernel,real_inner_comm]
    rfl
  refine ⟨hz,?_⟩
  intro v hv
  obtain ⟨weight,rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hv
  rw [inner_sum]
  simp only [real_inner_smul_right,scalar_section_reproduces,hz,mul_zero,Finset.sum_const_zero]

theorem actual_inverse_kernel_interpolant_is_the_true_orthogonal_projection
    (input : I → X) (target : X) (hgram : (actualGram (H:=H) input).PosDef) :
    actualMeanFunction (H:=H) input (fun i => scalarKernel (H:=H) (input i) target) 0=
      (actualDataSpan (H:=H) input).starProjection (scalarSection (H:=H) target) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (actual_inverse_interpolant_is_in_the_actual_data_span input _)
  exact (actual_residual_vanishes_on_all_data_and_is_orthogonal_to_the_actual_data_span
    input target hgram).2

theorem actual_residual_squared_norm_is_the_literal_noise_free_matrix_power_function
    (input : I → X) (target : X) (hgram : (actualGram (H:=H) input).PosDef) :
    ‖actualResidual (H:=H) input target‖^2=
      CompleteModulesMatrixGP.posteriorVariance (actualGram (H:=H) input)
        (fun i => scalarKernel (H:=H) (input i) target) (scalarKernel (H:=H) target target) 0 := by
  let feature := fun i => scalarSection (H:=H) (input i)
  let query := fun i => scalarKernel (H:=H) (input i) target
  let weight := (CompleteModulesMatrixGP.ridgeMatrix (actualGram (H:=H) input) 0)⁻¹ *ᵥ query
  have hdet : (CompleteModulesMatrixGP.ridgeMatrix (actualGram (H:=H) input) 0).det≠0 := by
    simpa [CompleteModulesMatrixGP.ridgeMatrix] using hgram.det_pos.ne'
  have hs := inverse_weights_solve_normal_system feature 0 hdet query
  have h := posterior_residual_norm_identity feature (scalarSection (H:=H) target) weight 0 hs
  simpa [actualResidual,actualMeanFunction,CompleteModulesKernel.posteriorVariance,
    CompleteModulesMatrixGP.posteriorVariance,scalarKernel,featureKernel,
    real_inner_self_eq_norm_sq,dotProduct,feature,query,weight,mul_comm] using h

theorem actual_residual_target_value_equals_its_squared_norm
    (input : I → X) (target : X) (hgram : (actualGram (H:=H) input).PosDef) :
    (actualResidual (H:=H) input target) target=‖actualResidual (H:=H) input target‖^2 := by
  have ho := (actual_residual_vanishes_on_all_data_and_is_orthogonal_to_the_actual_data_span
    input target hgram).2 _ (actual_inverse_interpolant_is_in_the_actual_data_span input _)
  rw [←scalar_section_reproduces]
  have he : scalarSection (H:=H) target=actualResidual (H:=H) input target+
      actualMeanFunction input (fun i => scalarKernel (H:=H) (input i) target) 0 := by
    simp [actualResidual]
  rw [he,inner_add_right,ho,add_zero,real_inner_self_eq_norm_sq]

theorem actual_extremal_function_interpolates_and_attains_the_literal_lower_value_and_norm
    (input : I → X) (labels : I → ℝ) (target : X)
    (hgram : (actualGram (H:=H) input).PosDef) (bound : ℝ)
    (hbound : ‖actualMeanFunction (H:=H) input labels 0‖ ≤ bound)
    (hpower : 0 < ‖actualResidual (H:=H) input target‖) :
    ∃ f : H, (∀ i, f (input i)=labels i) ∧ ‖f‖=bound ∧
      f target=(actualMeanFunction (H:=H) input labels 0) target-
        Real.sqrt (bound^2-‖actualMeanFunction (H:=H) input labels 0‖^2)*
          ‖actualResidual (H:=H) input target‖ := by
  let s := actualMeanFunction (H:=H) input labels 0
  let g := actualResidual (H:=H) input target
  let r := Real.sqrt (bound^2-‖s‖^2)
  let c := -r/‖g‖
  let f := s+c • g
  have hg := actual_residual_vanishes_on_all_data_and_is_orthogonal_to_the_actual_data_span input target hgram
  have ho : inner ℝ s g=0 := by
    rw [real_inner_comm]
    exact hg.2 s (actual_inverse_interpolant_is_in_the_actual_data_span input labels)
  have hnon : 0 ≤ bound^2-‖s‖^2 := by
    have hb : 0 ≤ bound := (norm_nonneg _).trans hbound
    dsimp [s]
    nlinarith [norm_nonneg (actualMeanFunction (H:=H) input labels 0)]
  have hr : r^2=bound^2-‖s‖^2 := Real.sq_sqrt hnon
  have hc : c*‖g‖=-r := by dsimp [c];field_simp;ring
  have hnorm : ‖f‖^2=bound^2 := by
    dsimp [f]
    rw [norm_add_sq_real,real_inner_smul_right,ho,mul_zero,mul_zero,add_zero,
      norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
    have hs : c^2*‖g‖^2=r^2 := by nlinarith [sq_nonneg (c*‖g‖+r)]
    rw [hs,hr]
    ring
  refine ⟨f,?_,?_,?_⟩
  · intro i
    simp [f,s,g,RKHS.coe_add,RKHS.coe_smul,hg.1,
      actual_inverse_interpolant_data input labels hgram]
  · have hb : 0 ≤ bound := (norm_nonneg _).trans hbound
    nlinarith [norm_nonneg f]
  · have hx := actual_residual_target_value_equals_its_squared_norm input target hgram
    change f target=s target-r*‖g‖
    simp only [f,RKHS.coe_add,RKHS.coe_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    change s target+c*g target=s target-r*‖g‖
    rw [hx]
    nlinarith [hc]

theorem actual_smaller_multiplier_violates_the_attained_noise_free_lower_bound
    (mean trueValue trueBound estimatedBound interpolantNorm power : ℝ)
    (hpower : 0 < power)
    (hvalue : trueValue=mean-Real.sqrt (trueBound^2-interpolantNorm^2)*power)
    (hsmall : estimatedBound < Real.sqrt (trueBound^2-interpolantNorm^2)) :
    trueValue < mean-estimatedBound*power := by
  rw [hvalue]
  nlinarith

end SafeLearning.CompleteModulesLoSBOExtremalConfidence
