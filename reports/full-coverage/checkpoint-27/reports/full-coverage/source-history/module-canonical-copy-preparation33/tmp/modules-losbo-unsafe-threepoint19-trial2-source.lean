import SafeLearning.CompleteModulesSafeOptEightPointPosteriors
import SafeLearning.CompleteModulesKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Matrix Set
open scoped BigOperators
namespace SafeLearning.CompleteModulesLoSBOUnsafeThreePoint
open CompleteModulesSafeOptEightPointPosteriors

abbrev ActualCoefficients := EuclideanSpace ℝ (Fin 3)
def actualFeature (i : Fin 3) : ActualCoefficients :=
  WithLp.toLp 2 ((![![1,0,0],![0,1,0],![0,2,1]] : Fin 3 → Fin 3 → ℝ) i)
def actualKernel (i j : Fin 3) : ℝ := inner ℝ (actualFeature i) (actualFeature j)
def actualCoefficient : ActualCoefficients := WithLp.toLp 2 (![0,-2,0] : Fin 3 → ℝ)
def actualValue (i : Fin 3) : ℝ := inner ℝ actualCoefficient (actualFeature i)
def actualDistance (i j : Fin 3) : ℝ := |(i.val:ℝ)-(j.val:ℝ)|
def actualGram : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1,0,0;0,1,2;0,2,5]

theorem actual_source_kernel_entries_equal_the_printed_three_by_three_gram :
    Matrix.of actualKernel=actualGram := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [actualKernel,actualFeature,actualGram,PiLp.inner_apply,
      Fin.sum_univ_succ]

theorem actual_source_gram_is_positive_definite_with_the_three_printed_leading_minors :
    actualGram.PosDef ∧ actualGram 0 0=1 ∧
      (actualGram.submatrix (Fin.castLE (by decide : 2≤3)) (Fin.castLE (by decide : 2≤3))).det=1 ∧
      actualGram.det=1 := by
  refine ⟨?_,by norm_num [actualGram],by norm_num [actualGram,Matrix.det_fin_two],
    by norm_num [actualGram,Matrix.det_fin_three]⟩
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [actualGram,Matrix.conjTranspose_apply]
  · intro x hx
    have hquad : star x ⬝ᵥ (actualGram *ᵥ x)=
        (x 0)^2+(x 1+2*x 2)^2+(x 2)^2 := by
      simp [actualGram,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
      ring
    rw [hquad]
    have hs : 0 ≤ (x 0)^2+(x 1+2*x 2)^2+(x 2)^2 := by positivity
    by_contra hn
    have hz0 : x 0=0 := by nlinarith [sq_nonneg (x 1+2*x 2),sq_nonneg (x 2)]
    have hz2 : x 2=0 := by nlinarith [sq_nonneg (x 0),sq_nonneg (x 1+2*x 2)]
    have hz1 : x 1=0 := by rw [hz0,hz2] at hn;simp at hn; nlinarith
    apply hx
    ext i
    fin_cases i
    · exact hz0
    · exact hz1
    · exact hz2

theorem actual_source_values_and_exact_lipschitz_constant_two :
    actualValue=(![0,-2,-4] : Fin 3 → ℝ) ∧
      (∀ i j, |actualValue i-actualValue j| ≤ 2*actualDistance i j) ∧
      (∀ bound : ℝ, (∀ i j, |actualValue i-actualValue j| ≤ bound*actualDistance i j) → 2≤bound) := by
  have hv : actualValue=(![0,-2,-4] : Fin 3 → ℝ) := by
    ext i
    fin_cases i <;> norm_num [actualValue,actualCoefficient,actualFeature,PiLp.inner_apply,Fin.sum_univ_succ]
  refine ⟨hv,?_,?_⟩
  · intro i j
    rw [hv]
    fin_cases i <;> fin_cases j <;> norm_num [actualDistance]
  · intro bound h
    have hh := h 0 1
    rw [hv] at hh
    norm_num [actualDistance] at hh
    exact hh

@[instance_reducible]
def actualRKHS : RKHS ℝ ActualCoefficients (Fin 3) ℝ where
  coeCLM := ContinuousLinearMap.pi (fun i => innerSL ℝ (actualFeature i))
  coeCLM_injective := by
    intro a b he
    have h (i : Fin 3) : inner ℝ (actualFeature i) a=inner ℝ (actualFeature i) b := congrFun he i
    have h0 := h 0;have h1 := h 1;have h2 := h 2
    simp [actualFeature,PiLp.inner_apply,Fin.sum_univ_succ] at h0 h1 h2
    ext i
    fin_cases i
    · exact h0
    · exact h1
    · linarith

theorem actual_source_rkhs_kernel_values_norm_and_kernel_section_coefficient :
    letI : RKHS ℝ ActualCoefficients (Fin 3) ℝ := actualRKHS
    (∀ i j, (RKHS.kernel ActualCoefficients i j) 1=actualKernel i j) ∧
      (∀ i, (RKHS.coeCLM ℝ) actualCoefficient i=actualValue i) ∧
      ‖actualCoefficient‖=2 ∧ actualCoefficient=(-2:ℝ) • (RKHS.kerFun ActualCoefficients 1 1) := by
  letI : RKHS ℝ ActualCoefficients (Fin 3) ℝ := actualRKHS
  have hker (i : Fin 3) : RKHS.kerFun ActualCoefficients i 1=actualFeature i := by
    apply ext_inner_right ℝ
    intro a
    rw [real_inner_comm (RKHS.kerFun ActualCoefficients i 1) a]
    rw [RKHS.inner_kerFun]
    change inner ℝ a (actualFeature i)=inner ℝ (actualFeature i) a
    exact real_inner_comm _ _
  refine ⟨?_,?_,?_,?_⟩
  · intro i j
    have h := RKHS.kernel_inner (H:=ActualCoefficients) i j (1:ℝ) (1:ℝ)
    rw [hker i,hker j] at h
    simpa [actualKernel,real_inner_comm] using h
  · intro i
    change inner ℝ (actualFeature i) actualCoefficient=inner ℝ actualCoefficient (actualFeature i)
    exact real_inner_comm _ _
  · norm_num [actualCoefficient,EuclideanSpace.norm_eq,Fin.sum_univ_succ]
  · rw [hker]
    ext i
    fin_cases i <;> norm_num [actualCoefficient,actualFeature]

def actualMean (i : Fin 3) : ℝ := actualGPMean actualKernel (fun _ : Fin 1 => 0) 0 (fun _ => 0) i
def actualVariance (i : Fin 3) : ℝ := actualGPVariance actualKernel (fun _ : Fin 1 => 0) 0 i
def actualSeed : Set (Fin 3) := {0,1}
def actualLower (bound : ℝ) (i : Fin 3) : ℝ := by
  classical
  exact if i∈actualSeed then max (-3) (actualMean i-bound*Real.sqrt (actualVariance i))
    else actualMean i-bound*Real.sqrt (actualVariance i)
def actualUpper (bound : ℝ) (i : Fin 3) : ℝ :=
  actualMean i+bound*Real.sqrt (actualVariance i)
def actualSafeAfterOne (bound : ℝ) : Set (Fin 3) := actualSeed∪
  {i | ∃ a∈actualSeed, -3≤actualLower bound a-2*actualDistance a i}
def actualMaximizersAfterOne (bound : ℝ) : Set (Fin 3) :=
  {i | i∈actualSafeAfterOne bound ∧ ∀ a∈actualSafeAfterOne bound, actualLower bound a≤actualUpper bound i}
def actualExpandersAfterOne (bound : ℝ) : Set (Fin 3) :=
  {i | i∈actualSafeAfterOne bound ∧ ∃ a, a∉actualSafeAfterOne bound ∧
    -3≤actualUpper bound i-2*actualDistance i a}
def actualWidth (bound : ℝ) (i : Fin 3) : ℝ := actualUpper bound i-actualLower bound i

theorem actual_one_observation_at_zero_has_the_literal_zero_mean_and_power_array :
    actualMean=0 ∧ actualVariance=(![0,1,5] : Fin 3 → ℝ) := by
  have hentries (i j : Fin 3) : actualKernel i j=actualGram i j :=
    congrFun (congrFun actual_source_kernel_entries_equal_the_printed_three_by_three_gram i) j
  constructor
  · ext i
    have h := (actual_one_observation_gp_matrix_formulas_are_the_true_scalar_mean_and_variance actualKernel 0 i 0 0).1
    simpa [actualMean,hentries,actualGram] using h
  · ext i
    have h := (actual_one_observation_gp_matrix_formulas_are_the_true_scalar_mean_and_variance actualKernel 0 i 0 0).2
    fin_cases i <;> simpa [actualVariance,hentries,actualGram] using h

theorem actual_half_bound_has_the_literal_lower_upper_arrays_and_unsafe_certificate :
    actualLower (1/2)=(![0,-1/2,-Real.sqrt 5/2] : Fin 3 → ℝ) ∧
    actualUpper (1/2)=(![0,1/2,Real.sqrt 5/2] : Fin 3 → ℝ) ∧
    actualSafeAfterOne (1/2)=univ ∧ actualValue 2<(-3:ℝ) ∧
    actualLower (1/2) 1-2*actualDistance 1 2=(-5/2:ℝ) := by
  have hp := actual_one_observation_at_zero_has_the_literal_zero_mean_and_power_array
  have hlo : actualLower (1/2)=(![0,-1/2,-Real.sqrt 5/2] : Fin 3 → ℝ) := by
    ext i
    fin_cases i <;> norm_num [actualLower,actualSeed,hp.1,hp.2] <;> ring
  have hup : actualUpper (1/2)=(![0,1/2,Real.sqrt 5/2] : Fin 3 → ℝ) := by
    ext i
    fin_cases i <;> norm_num [actualUpper,hp.1,hp.2] <;> ring
  refine ⟨hlo,hup,?_,?_,?_⟩
  · ext i
    simp only [mem_univ,iff_true]
    fin_cases i
    · exact Or.inl (by simp [actualSeed])
    · exact Or.inl (by simp [actualSeed])
    · exact Or.inr ⟨1,by simp [actualSeed],by norm_num [hlo,actualDistance]⟩
  · rw [actual_source_values_and_exact_lipschitz_constant_two.1];norm_num
  · rw [hlo];norm_num [actualDistance]

theorem actual_half_bound_maximizer_acquisition_queries_the_unsafe_point_two :
    actualExpandersAfterOne (1/2)=∅ ∧ actualMaximizersAfterOne (1/2)=univ ∧
    actualWidth (1/2)=(![0,1,Real.sqrt 5] : Fin 3 → ℝ) ∧
    (∀ i, i≠2 → actualWidth (1/2) i<actualWidth (1/2) 2) := by
  have h := actual_half_bound_has_the_literal_lower_upper_arrays_and_unsafe_certificate
  have hs : 1<Real.sqrt (5:ℝ) := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤5),Real.sqrt_nonneg (5:ℝ)]
  have hw : actualWidth (1/2)=(![0,1,Real.sqrt 5] : Fin 3 → ℝ) := by
    ext i
    unfold actualWidth
    rw [h.1,h.2.1]
    fin_cases i <;> simp <;> ring
  refine ⟨?_,?_,hw,?_⟩
  · ext i
    unfold actualExpandersAfterOne
    rw [h.2.2.1]
    simp
  · ext i
    simp only [actualMaximizersAfterOne,h.2.2.1,mem_setOf_eq,mem_univ,true_and,iff_true]
    intro a ha
    rw [h.1,h.2.1]
    fin_cases i <;> fin_cases a <;> norm_num <;> nlinarith
  · intro i hi
    rw [hw]
    fin_cases i <;> norm_num at hi ⊢ <;> try nlinarith

theorem actual_every_estimated_bound_above_one_fails_the_first_seed_to_two_certificate
    (bound : ℝ) (hbound : 1<bound) :
    actualLower bound 1-2*actualDistance 1 2<(-3:ℝ) := by
  have hp := actual_one_observation_at_zero_has_the_literal_zero_mean_and_power_array
  norm_num [actualLower,actualSeed,actualDistance,hp.1,hp.2]
  rcases le_total (-3:ℝ) (-bound) with h | h
  · rw [max_eq_right h];linarith
  · rw [max_eq_left h];norm_num

theorem actual_invalid_bound_between_one_and_two_empties_the_seed_intersection_after_observing_one
    (bound : ℝ) (hlower : 1<bound) (hupper : bound<2) :
    Icc (actualLower bound 1) (actualUpper bound 1)∩Icc (-2:ℝ) (-2)=∅ := by
  have hp := actual_one_observation_at_zero_has_the_literal_zero_mean_and_power_array
  ext x
  simp only [mem_inter_iff,mem_Icc,mem_empty_iff_false,iff_false]
  rintro ⟨⟨hlo,hhi⟩,⟨hx1,hx2⟩⟩
  have hx : x=-2 := le_antisymm hx2 hx1
  rw [hx] at hlo
  have hb : (-3:ℝ)≤-bound := by linarith
  norm_num [actualLower,actualSeed,hp.1,hp.2,max_eq_right hb] at hlo
  linarith

end SafeLearning.CompleteModulesLoSBOUnsafeThreePoint
