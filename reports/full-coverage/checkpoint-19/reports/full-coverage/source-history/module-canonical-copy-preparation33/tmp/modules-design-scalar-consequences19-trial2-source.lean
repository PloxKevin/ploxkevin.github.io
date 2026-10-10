import SafeLearning.CompleteModulesDesignScalarLayers

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteModulesDesignScalarConsequences
open CompleteModulesDesignScalarLayers

theorem actual_source_every_residual_has_the_absolute_value_decomposition (T x : ℝ) :
    sourceResidual T x=(1-4/T)*x-(4/T)*|x| := by
  by_cases hx : 0≤x
  · rw [sourceResidual,max_eq_left (by linarith : (0:ℝ)≤2*x),abs_of_nonneg hx]
    ring
  · rw [sourceResidual,max_eq_right (by linarith : 2*x≤0),abs_of_nonpos (le_of_not_ge hx)]
    ring

theorem actual_source_sufficient_scalar_gram_condition_for_every_T
    (T : ℝ) (hT : 4≤T) :
    0<T ∧ (-1:ℝ)≤1-8/T ∧ 1-8/T≤1 ∧
      IsLeast (admissibleGains (sourceResidual T)) 1 := by
  have hp : 0<T := by linarith
  have hc : 0≤4/T := by positivity
  have hcle : (4:ℝ)/T≤1 := (div_le_one hp).mpr hT
  have ha : 0≤1-4/T := by linarith
  have hlower : -1≤1-8/T := by
    have h8 : (8:ℝ)/T≤2 := by
      apply (div_le_iff₀ hp).mpr
      linarith
    linarith
  have hu : 1-8/T≤1 := by
    have h8 : (0:ℝ)≤8/T := by positivity
    linarith
  refine ⟨hp,?_,hu,?_⟩
  · exact hlower
  · refine ⟨⟨by norm_num,?_⟩,?_⟩
    · intro x y
      rw [actual_source_every_residual_has_the_absolute_value_decomposition,
        actual_source_every_residual_has_the_absolute_value_decomposition]
      calc
        _ = |(1-4/T)*(x-y)-(4/T)*(|x|-|y|)| := by congr 1;ring
        _ ≤ |(1-4/T)*(x-y)|+|(4/T)*(|x|-|y|)| := abs_sub _ _
        _ = (1-4/T)*|x-y|+(4/T)*abs (abs x-abs y) := by
          rw [abs_mul,abs_mul,abs_of_nonneg ha,abs_of_nonneg hc]
        _ ≤ (1-4/T)*|x-y|+(4/T)*|x-y| := by
          exact add_le_add_left (mul_le_mul_of_nonneg_left (abs_abs_sub_abs_le_abs_sub x y) hc) _
        _ = 1*|x-y| := by ring
    · intro L hL
      have hh:=hL.2 (-1) 0
      norm_num [sourceResidual] at hh
      exact hh

end SafeLearning.CompleteModulesDesignScalarConsequences
