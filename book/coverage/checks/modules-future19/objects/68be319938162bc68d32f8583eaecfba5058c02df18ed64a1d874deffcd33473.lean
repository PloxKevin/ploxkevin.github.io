import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Matrix
open scoped BigOperators ComplexConjugate
namespace SafeLearning.CompleteModulesRealHarmonicOrthogonality

variable {n : ℕ} [NeZero n]

def characterValue (k t : ZMod n) : ℂ := ZMod.stdAddChar (k*t)

theorem actual_complete_cyclic_character_sum (k : ZMod n) :
    (∑ t : ZMod n,characterValue k t)=if k=0 then (n:ℂ) else 0 := by
  simpa only [characterValue,mul_comm,ZMod.card] using
    AddChar.sum_mulShift k (ZMod.isPrimitive_stdAddChar n)

theorem actual_character_real_imaginary_components_have_unit_energy (k t : ZMod n) :
    (characterValue k t).re^2+(characterValue k t).im^2=1 := by
  have hn : ‖characterValue k t‖=1 := (ZMod.stdAddChar (N:=n)).norm_apply (k*t)
  have hs := Complex.normSq_eq_norm_sq (characterValue k t)
  simpa only [Complex.normSq_apply,hn,one_pow,pow_two] using hs

theorem actual_character_product_uses_the_sum_frequency (k l t : ZMod n) :
    characterValue k t*characterValue l t=characterValue (k+l) t := by
  simp only [characterValue,add_mul,AddChar.map_add_eq_mul]

theorem actual_character_conjugate_product_uses_the_difference_frequency (k l t : ZMod n) :
    characterValue k t*conj (characterValue l t)=characterValue (k-l) t := by
  simp only [characterValue,sub_eq_add_neg,add_mul,neg_mul,
    AddChar.map_add_eq_mul,AddChar.map_neg_eq_conj]

theorem actual_nonzero_character_real_and_imaginary_sums_vanish (k : ZMod n) (hk : k≠0) :
    (∑ t : ZMod n,(characterValue k t).re)=0 ∧
      (∑ t : ZMod n,(characterValue k t).im)=0 := by
  have h := actual_complete_cyclic_character_sum k
  rw [if_neg hk] at h
  constructor
  · have hr := congrArg Complex.reCLM h
    simpa only [map_sum,Complex.reCLM_apply,Complex.zero_re] using hr
  · have hi := congrArg Complex.imCLM h
    simpa only [map_sum,Complex.imCLM_apply,Complex.zero_im] using hi

theorem actual_real_imaginary_character_pairs_are_orthogonal_with_the_true_half_cardinality
    (k l : ZMod n) (hplus : k+l≠0) :
    (∑ t : ZMod n,(characterValue k t).re*(characterValue l t).re)=
        if k=l then (n:ℝ)/2 else 0 ∧
    (∑ t : ZMod n,(characterValue k t).im*(characterValue l t).im)=
        if k=l then (n:ℝ)/2 else 0 ∧
    (∑ t : ZMod n,(characterValue k t).re*(characterValue l t).im)=0 ∧
    (∑ t : ZMod n,(characterValue k t).im*(characterValue l t).re)=0 := by
  have hp : (∑ t : ZMod n,characterValue k t*characterValue l t)=0 := by
    simp_rw [actual_character_product_uses_the_sum_frequency]
    rw [actual_complete_cyclic_character_sum,if_neg hplus]
  have hm : (∑ t : ZMod n,characterValue k t*conj (characterValue l t))=
      if k=l then (n:ℂ) else 0 := by
    simp_rw [actual_character_conjugate_product_uses_the_difference_frequency]
    rw [actual_complete_cyclic_character_sum,sub_eq_zero]
  have hpr := congrArg Complex.reCLM hp
  have hpi := congrArg Complex.imCLM hp
  have hmr := congrArg Complex.reCLM hm
  have hmi := congrArg Complex.imCLM hm
  simp only [map_sum,Complex.reCLM_apply,Complex.imCLM_apply,
    Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im,
    Complex.zero_re,Complex.zero_im,Finset.sum_sub_distrib,Finset.sum_add_distrib,
    mul_neg,Finset.sum_neg_distrib] at hpr hpi hmr hmi
  by_cases hkl : k=l
  · simp only [if_pos hkl,Complex.natCast_re,Complex.natCast_im] at hmr hmi
    simp only [if_pos hkl]
    exact ⟨by linarith,by linarith,by linarith,by linarith⟩
  · simp only [if_neg hkl,Complex.zero_re,Complex.zero_im] at hmr hmi
    simp only [if_neg hkl]
    exact ⟨by linarith,by linarith,by linarith,by linarith⟩

end SafeLearning.CompleteModulesRealHarmonicOrthogonality
