import SafeLearning.CompleteModulesLoSBOExtremalConfidence

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Matrix Set
open scoped BigOperators
namespace SafeLearning.CompleteModulesLoSBOExtremalConsequences
open CompleteModulesKernel CompleteModulesGramBridge CompleteModulesLoSBOExtremalConfidence

variable {H X I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [RKHS ℝ H X ℝ] [Fintype I] [DecidableEq I]

theorem actual_invertible_rkhs_gram_is_positive_definite
    (input : I → X) (hdet : (actualGram (H:=H) input).det≠0) :
    (actualGram (H:=H) input).PosDef :=
  (feature_gram_positive_semidefinite (fun i => scalarSection (H:=H) (input i))).posDef_iff_det_ne_zero.mpr hdet

theorem actual_residual_norm_is_the_literal_positive_square_root_power_function
    (input : I → X) (target : X) (hdet : (actualGram (H:=H) input).det≠0) :
    ‖actualResidual (H:=H) input target‖=
      Real.sqrt (CompleteModulesMatrixGP.posteriorVariance (actualGram (H:=H) input)
        (fun i => scalarKernel (H:=H) (input i) target) (scalarKernel (H:=H) target target) 0) := by
  rw [←actual_residual_squared_norm_is_the_literal_noise_free_matrix_power_function input target
    (actual_invertible_rkhs_gram_is_positive_definite input hdet),Real.sqrt_sq (norm_nonneg _)]

theorem actual_every_interpolating_error_is_orthogonal_and_has_the_true_squared_norm_gap
    (input : I → X) (labels : I → ℝ) (hdet : (actualGram (H:=H) input).det≠0)
    (f : H) (hdata : ∀ i, f (input i)=labels i) :
    (∀ i, (f-actualMeanFunction (H:=H) input labels 0) (input i)=0) ∧
    (∀ v∈actualDataSpan (H:=H) input,
      inner ℝ (f-actualMeanFunction (H:=H) input labels 0) v=0) ∧
    ‖f‖^2=‖actualMeanFunction (H:=H) input labels 0‖^2+
      ‖f-actualMeanFunction (H:=H) input labels 0‖^2 := by
  have hgram := actual_invertible_rkhs_gram_is_positive_definite input hdet
  have hz : ∀ i, (f-actualMeanFunction (H:=H) input labels 0) (input i)=0 := by
    intro i
    simp [RKHS.coe_sub,Pi.sub_apply,hdata,actual_inverse_interpolant_data input labels hgram]
  have ho : ∀ v∈actualDataSpan (H:=H) input,
      inner ℝ (f-actualMeanFunction (H:=H) input labels 0) v=0 := by
    intro v hv
    obtain ⟨weight,rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hv
    rw [inner_sum]
    simp [real_inner_smul_right,scalar_section_reproduces,hz]
  refine ⟨hz,ho,?_⟩
  have hs := ho _ (actual_inverse_interpolant_is_in_the_actual_data_span input labels)
  have hn := norm_add_sq_real (actualMeanFunction (H:=H) input labels 0)
    (f-actualMeanFunction (H:=H) input labels 0)
  rw [add_sub_cancel,real_inner_comm,hs,mul_zero,add_zero] at hn
  exact hn

theorem actual_every_interpolant_obeys_the_tight_noise_free_refined_norm_bound
    (input : I → X) (labels : I → ℝ) (target : X)
    (hdet : (actualGram (H:=H) input).det≠0) (bound : ℝ)
    (f : H) (hdata : ∀ i, f (input i)=labels i) (hbound : ‖f‖≤bound) :
    |f target-(actualMeanFunction (H:=H) input labels 0) target| ≤
      Real.sqrt (bound^2-‖actualMeanFunction (H:=H) input labels 0‖^2)*
        ‖actualResidual (H:=H) input target‖ := by
  let s := actualMeanFunction (H:=H) input labels 0
  let e := f-s
  have hg := actual_every_interpolating_error_is_orthogonal_and_has_the_true_squared_norm_gap
    input labels hdet f hdata
  have he : inner ℝ e (actualResidual (H:=H) input target)=f target-s target := by
    have hp := hg.2.1 _ (actual_inverse_interpolant_is_in_the_actual_data_span input
      (fun i => scalarKernel (H:=H) (input i) target))
    rw [actualResidual,inner_sub_right]
    change inner ℝ e (scalarSection (H:=H) target)-inner ℝ e
      (actualMeanFunction input (fun i => scalarKernel (H:=H) (input i) target) 0)=_
    rw [hp,sub_zero,scalar_section_reproduces]
    simp [e,RKHS.coe_sub,s]
  have hb : 0≤bound := (norm_nonneg _).trans hbound
  have hnon : 0≤bound^2-‖s‖^2 := by
    have h := hg.2.2
    change ‖f‖^2=‖s‖^2+‖e‖^2 at h
    nlinarith [norm_nonneg f,sq_nonneg ‖e‖]
  have hn : ‖e‖≤Real.sqrt (bound^2-‖s‖^2) := by
    have h := hg.2.2
    change ‖f‖^2=‖s‖^2+‖e‖^2 at h
    nlinarith [Real.sq_sqrt hnon,Real.sqrt_nonneg (bound^2-‖s‖^2),norm_nonneg e,norm_nonneg f]
  rw [←he]
  exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))

theorem actual_zero_power_function_pins_down_every_interpolating_function_at_the_target
    (input : I → X) (labels : I → ℝ) (target : X)
    (hdet : (actualGram (H:=H) input).det≠0)
    (hzero : ‖actualResidual (H:=H) input target‖=0)
    (f : H) (hdata : ∀ i, f (input i)=labels i) :
    f target=(actualMeanFunction (H:=H) input labels 0) target := by
  have h := actual_every_interpolant_obeys_the_tight_noise_free_refined_norm_bound
    input labels target hdet ‖f‖ f hdata le_rfl
  rw [hzero,mul_zero] at h
  exact sub_eq_zero.mp (abs_nonpos_iff.mp h)

theorem actual_invertible_gram_and_positive_power_give_the_literal_attaining_function
    (input : I → X) (labels : I → ℝ) (target : X)
    (hdet : (actualGram (H:=H) input).det≠0) (bound : ℝ)
    (hbound : ‖actualMeanFunction (H:=H) input labels 0‖≤bound)
    (hpower : 0<‖actualResidual (H:=H) input target‖) :
    ∃ f : H, (∀ i, f (input i)=labels i) ∧ ‖f‖=bound ∧
      f target=(actualMeanFunction (H:=H) input labels 0) target-
        Real.sqrt (bound^2-‖actualMeanFunction (H:=H) input labels 0‖^2)*
          ‖actualResidual (H:=H) input target‖ :=
  actual_extremal_function_interpolates_and_attains_the_literal_lower_value_and_norm input labels target
    (actual_invertible_rkhs_gram_is_positive_definite input hdet) bound hbound hpower

theorem actual_positive_unobserved_power_precludes_every_data_only_finite_norm_upper_bound
    (input : I → X) (labels : I → ℝ) (target : X)
    (hdet : (actualGram (H:=H) input).det≠0)
    (hpower : 0<‖actualResidual (H:=H) input target‖) :
    ∀ candidateBound : ℝ, ∃ f : H, (∀ i, f (input i)=labels i) ∧ candidateBound<‖f‖ := by
  intro candidateBound
  let bound := max ‖actualMeanFunction (H:=H) input labels 0‖ (|candidateBound|+1)
  obtain ⟨f,hdata,hnorm,hvalue⟩ := actual_invertible_gram_and_positive_power_give_the_literal_attaining_function
    input labels target hdet bound (le_max_left _ _) hpower
  refine ⟨f,hdata,?_⟩
  rw [hnorm]
  have hb : |candidateBound|+1≤bound := le_max_right _ _
  linarith [le_abs_self candidateBound]

end SafeLearning.CompleteModulesLoSBOExtremalConsequences
