import SafeLearning.CompleteModulesGramBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Matrix Set
open scoped BigOperators
namespace SafeLearning.CompleteModulesLoSBOPracticeRKHS
open SafeLearning.CompleteModulesKernel SafeLearning.CompleteModulesGramBridge

variable {H X I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [RKHS ℝ H X ℝ] [Fintype I] [DecidableEq I]

theorem actual_unobserved_orthogonal_unit_direction_vanishes_at_every_observed_input
    (input : I → X) (g : H) (horth : ∀ i, inner ℝ g (scalarSection (H:=H) (input i))=0) :
    ∀ i, g (input i)=0 := by
  intro i
  rw [←scalar_section_reproduces]
  exact horth i

theorem actual_inverse_interpolant_is_orthogonal_to_the_unobserved_direction
    (input : I → X) (labels : I → ℝ) (g : H)
    (horth : ∀ i, inner ℝ g (scalarSection (H:=H) (input i))=0) :
    inner ℝ (actualMeanFunction (H:=H) input labels 0) g=0 := by
  rw [actualMeanFunction,combination_inner]
  simp only [real_inner_comm,horth,mul_zero,Finset.sum_const_zero]

theorem actual_source_interpolant_plus_any_unobserved_direction_matches_the_same_data
    (input : I → X) (labels : I → ℝ) (hgram : (actualGram (H:=H) input).PosDef)
    (g : H) (hunit : ‖g‖=1) (horth : ∀ i, inner ℝ g (scalarSection (H:=H) (input i))=0)
    (c : ℝ) :
    (∀ i, (actualMeanFunction (H:=H) input labels 0+c • g) (input i)=labels i) ∧
      ‖actualMeanFunction (H:=H) input labels 0+c • g‖^2=
        labels ⬝ᵥ ((actualGram (H:=H) input)⁻¹ *ᵥ labels)+c^2 := by
  constructor
  · intro i
    have hz := actual_unobserved_orthogonal_unit_direction_vanishes_at_every_observed_input input g horth i
    simp only [RKHS.coe_add,RKHS.coe_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul,hz,mul_zero,add_zero]
    exact actual_inverse_interpolant_data input labels hgram i
  · have ho := actual_inverse_interpolant_is_orthogonal_to_the_unobserved_direction input labels g horth
    rw [norm_add_sq_real,real_inner_smul_right,ho,mul_zero,mul_zero,add_zero,
      actual_inverse_interpolant_squared_norm input labels hgram,norm_smul,Real.norm_eq_abs,hunit,mul_one,sq_abs]

theorem actual_exact_data_impose_the_gram_norm_lower_bound_on_every_interpolating_function
    (input : I → X) (labels : I → ℝ) (hgram : (actualGram (H:=H) input).PosDef)
    (f : H) (hdata : ∀ i, f (input i)=labels i) :
    labels ⬝ᵥ ((actualGram (H:=H) input)⁻¹ *ᵥ labels) ≤ ‖f‖^2 := by
  rw [←actual_inverse_interpolant_squared_norm input labels hgram]
  exact pow_le_pow_left₀ (norm_nonneg _) (actual_inverse_interpolant_minimum_norm input labels hgram f hdata) 2

theorem actual_source_same_exact_data_allow_norms_above_every_finite_bound
    (input : I → X) (labels : I → ℝ) (hgram : (actualGram (H:=H) input).PosDef)
    (g : H) (hunit : ‖g‖=1) (horth : ∀ i, inner ℝ g (scalarSection (H:=H) (input i))=0) :
    ∀ bound : ℝ, ∃ c : ℝ,
      (∀ i, (actualMeanFunction (H:=H) input labels 0+c • g) (input i)=labels i) ∧
      bound < ‖actualMeanFunction (H:=H) input labels 0+c • g‖ := by
  intro bound
  let c : ℝ := |bound|+1
  have h := actual_source_interpolant_plus_any_unobserved_direction_matches_the_same_data input labels hgram g hunit horth c
  refine ⟨c,h.1,?_⟩
  have he := actual_inverse_interpolant_squared_norm input labels hgram
  have hnon : 0 ≤ labels ⬝ᵥ ((actualGram (H:=H) input)⁻¹ *ᵥ labels) := by rw [←he]; positivity
  have hnorm := norm_nonneg (actualMeanFunction (H:=H) input labels 0+c • g)
  have hc : 0 < c := by dsimp [c]; positivity
  have hbound : bound < c := by dsimp [c]; linarith [le_abs_self bound]
  have hn : c ≤ ‖actualMeanFunction (H:=H) input labels 0+c • g‖ := by nlinarith [h.2]
  exact hbound.trans_le hn

end SafeLearning.CompleteModulesLoSBOPracticeRKHS
