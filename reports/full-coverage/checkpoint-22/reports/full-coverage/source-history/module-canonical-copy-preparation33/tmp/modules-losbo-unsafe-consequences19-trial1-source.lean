import SafeLearning.CompleteModulesLoSBOUnsafeThreePoint
import SafeLearning.CompleteModulesGramBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Matrix Set
open scoped BigOperators
namespace SafeLearning.CompleteModulesLoSBOUnsafeConsequences
open CompleteModulesLoSBOUnsafeThreePoint CompleteModulesKernel CompleteModulesGramBridge
open CompleteModulesSafeOptEightPointPosteriors

def actualInitialWidth (i : Fin 3) : ENNReal := by
  classical
  exact if i∈actualSeed then ⊤ else 0

theorem actual_initial_seed_is_safe_and_zero_is_a_legitimate_infinite_width_tie :
    (∀ i∈actualSeed, (-3:ℝ)≤actualValue i) ∧ 0∈actualSeed ∧ 1∈actualSeed ∧
      actualInitialWidth 0=⊤ ∧ actualInitialWidth 1=⊤ ∧
      (∀ i∈actualSeed, actualInitialWidth i≤actualInitialWidth 0) ∧ actualValue 0=0 := by
  rw [actual_source_values_and_exact_lipschitz_constant_two.1]
  refine ⟨?_,by simp [actualSeed],by simp [actualSeed],by simp [actualInitialWidth,actualSeed],
    by simp [actualInitialWidth,actualSeed],?_,by norm_num⟩
  · intro i hi
    fin_cases i <;> norm_num [actualSeed] at hi ⊢
  · intro i hi
    simp [actualInitialWidth,actualSeed]

theorem actual_source_function_is_the_norm_two_attainer_for_the_zero_data_and_target_one :
    letI : RKHS ℝ ActualCoefficients (Fin 3) ℝ := actualRKHS
    (RKHS.coeCLM ℝ) actualCoefficient 0=0 ∧ ‖actualCoefficient‖=2 ∧
      (RKHS.coeCLM ℝ) actualCoefficient 1=actualMean 1-
        Real.sqrt ((2:ℝ)^2-(0:ℝ)^2)*Real.sqrt (actualVariance 1) := by
  letI : RKHS ℝ ActualCoefficients (Fin 3) ℝ := actualRKHS
  have he := actual_source_rkhs_kernel_values_norm_and_kernel_section_coefficient
  have hp := actual_one_observation_at_zero_has_the_literal_zero_mean_and_power_array
  rw [he.2.1 0,he.2.1 1,actual_source_values_and_exact_lipschitz_constant_two.1,hp.1,hp.2]
  exact ⟨by norm_num,he.2.2.1,by norm_num⟩

theorem actual_valid_norm_bound_at_least_two_contains_the_function_in_every_noise_free_band
    {I : Type*} [Fintype I] [DecidableEq I] (input : I → Fin 3)
    (hgram : (actualGPMatrix actualKernel input 0).PosDef) (bound : ℝ) (hbound : 2≤bound)
    (target : Fin 3) :
    |actualValue target-actualGPMean actualKernel input 0 (fun i => actualValue (input i)) target|≤
      bound*Real.sqrt (actualGPVariance actualKernel input 0 target) := by
  let feature := fun i => actualFeature (input i)
  let query := actualGPCross actualKernel input target
  let A := actualGPMatrix actualKernel input 0
  let weight := A⁻¹ *ᵥ query
  have hmatrix : CompleteModulesMatrixGP.ridgeMatrix (featureGram feature) 0=A := by
    ext i j
    simp [CompleteModulesMatrixGP.ridgeMatrix,actualGPMatrix,featureGram,Matrix.gram_apply,
      feature,A,actualKernel,real_inner_comm]
  have hs := inverse_weights_solve_normal_system feature 0
    (by rw [hmatrix];exact hgram.det_pos.ne') query
  have hnorm : ‖actualCoefficient‖≤bound := by
    rw [show ‖actualCoefficient‖=2 from actual_source_rkhs_kernel_values_norm_and_kernel_section_coefficient.2.2.1]
    exact hbound
  have h := noiseless_posterior_error feature (actualFeature target) actualCoefficient weight 0 bound
    (by norm_num) hnorm (by simpa [hmatrix,query,feature,weight,A,actualGPCross,actualKernel] using hs)
  have hmean : actualGPMean actualKernel input 0 (fun i => actualValue (input i)) target=
      ∑ i, weight i*actualValue (input i) := by
    have hi : A⁻¹.IsSymm := hgram.isHermitian.isSymm.inv
    have hh := Matrix.dotProduct_transpose_mulVec A⁻¹ (fun i => actualValue (input i)) query
    rw [hi] at hh
    change query ⬝ᵥ (A⁻¹ *ᵥ (fun i => actualValue (input i)))=∑ i, weight i*actualValue (input i)
    rw [←hh]
    simp [dotProduct,weight,mul_comm]
  have hvariance : posteriorVariance feature (actualFeature target) weight=
      actualGPVariance actualKernel input 0 target := by
    simp [posteriorVariance,actualGPVariance,actualKernel,real_inner_self_eq_norm_sq,
      dotProduct,actualGPCross,query,weight,A,feature,mul_comm]
  rw [hmean,←hvariance]
  exact h

theorem actual_any_valid_lower_cone_algorithm_keeps_the_unsafe_point_out_for_all_time
    (safeSets : ℕ → Set (Fin 3)) (lower : ℕ → Fin 3 → ℝ)
    (hseed : safeSets 0=actualSeed) (hvalid : ∀ n i, lower n i≤actualValue i)
    (hstep : ∀ n i, i∈safeSets (n+1) → i∈safeSets n ∨
      ∃ a∈safeSets n, (-3:ℝ)≤lower (n+1) a-2*actualDistance a i) :
    (∀ n i, i∈safeSets n → (-3:ℝ)≤actualValue i) ∧ (∀ n, (2:Fin 3)∉safeSets n) := by
  have hsafe : ∀ n i, i∈safeSets n → (-3:ℝ)≤actualValue i := by
    intro n
    induction n with
    | zero => intro i hi;rw [hseed] at hi
              exact actual_initial_seed_is_safe_and_zero_is_a_legitimate_infinite_width_tie.1 i hi
    | succ n ih =>
      intro i hi
      rcases hstep n i hi with old | ⟨a,ha,hcertificate⟩
      · exact ih i old
      · have hl := hvalid (n+1) a
        have hf := actual_source_values_and_exact_lipschitz_constant_two.2.1 a i
        have habs := (abs_le.mp hf).1
        linarith
  refine ⟨hsafe,?_⟩
  intro n hi
  have h := hsafe n 2 hi
  rw [actual_source_values_and_exact_lipschitz_constant_two.1] at h
  norm_num at h

theorem actual_any_admissible_query_of_a_valid_lower_cone_algorithm_is_safe_forever
    (safeSets : ℕ → Set (Fin 3)) (lower : ℕ → Fin 3 → ℝ) (query : ℕ → Fin 3)
    (hseed : safeSets 0=actualSeed) (hvalid : ∀ n i, lower n i≤actualValue i)
    (hstep : ∀ n i, i∈safeSets (n+1) → i∈safeSets n ∨
      ∃ a∈safeSets n, (-3:ℝ)≤lower (n+1) a-2*actualDistance a i)
    (hquery : ∀ n, query n∈safeSets n) : ∀ n, query n≠2 := by
  have h := actual_any_valid_lower_cone_algorithm_keeps_the_unsafe_point_out_for_all_time
    safeSets lower hseed hvalid hstep
  intro n he
  have hh := hquery n
  rw [he] at hh
  exact h.2 n hh

end SafeLearning.CompleteModulesLoSBOUnsafeConsequences
