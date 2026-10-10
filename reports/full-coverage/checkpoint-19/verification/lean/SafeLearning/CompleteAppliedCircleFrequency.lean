import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace SafeLearning.CompleteAppliedCircleFrequency

def unitPoint (omega : ℝ) : ℂ := (Real.cos omega : ℂ)+(Real.sin omega : ℂ)*Complex.I
def sourceTransfer (z : ℂ) : ℂ := (3/5)/(z-4/5)
def realPartFromCosine (c : ℝ) : ℝ := (3/5)*(c-4/5)/(41/25-8/5*c)

theorem actual_unit_circle_point_has_norm_one (omega : ℝ) : ‖unitPoint omega‖=1 := by
  rw [Complex.norm_def]
  have hs : Complex.normSq (unitPoint omega)=1 := by
    simp only [unitPoint,Complex.normSq_apply,Complex.add_re,Complex.add_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.mul_re,Complex.mul_im,
      Complex.I_re,Complex.I_im,mul_zero,mul_one,sub_zero,zero_add,add_zero]
    simpa only [pow_two] using Real.cos_sq_add_sin_sq omega
  rw [hs,Real.sqrt_one]

theorem actual_unit_circle_denominator_has_the_source_square (omega : ℝ) :
    Complex.normSq (unitPoint omega-4/5)=41/25-8/5*Real.cos omega := by
  have hs := Real.cos_sq_add_sin_sq omega
  simp only [unitPoint,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.add_re,Complex.add_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
    Complex.div_re,Complex.div_im,
    mul_zero,mul_one,sub_zero,zero_add,add_zero]
  norm_num
  nlinarith

theorem actual_source_real_part_on_the_unit_circle (omega : ℝ) :
    (sourceTransfer (unitPoint omega)).re=realPartFromCosine (Real.cos omega) := by
  have hnum : ((3/5:ℂ)).re=(3/5:ℝ) := by norm_num
  have hnumi : ((3/5:ℂ)).im=0 := by norm_num
  have hden : (unitPoint omega-4/5).re=Real.cos omega-4/5 := by
    rw [Complex.sub_re]
    have hconst : ((4/5:ℂ)).re=(4/5:ℝ) := by norm_num
    rw [hconst]
    simp only [unitPoint,Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,mul_zero,mul_one,sub_zero,add_zero]
  rw [sourceTransfer,Complex.div_re,hnum,hnumi,hden,
    actual_unit_circle_denominator_has_the_source_square,zero_mul,zero_div,add_zero]
  rfl

theorem actual_denominator_is_strictly_positive_for_every_cosine (c : ℝ) (hc : c≤1) :
    0<41/25-8/5*c := by linarith

theorem actual_source_derivative_in_cosine (c : ℝ) (hc : c≤1) :
    HasDerivAt realPartFromCosine ((3/5)*(9/25)/(41/25-8/5*c)^2) c ∧
      0<(3/5)*(9/25)/(41/25-8/5*c)^2 := by
  have hd := actual_denominator_is_strictly_positive_for_every_cosine c hc
  constructor
  · convert (((hasDerivAt_id c).sub_const (4/5)).const_mul (3/5)).div
      ((hasDerivAt_const c (41/25)).sub ((hasDerivAt_id c).const_mul (8/5))) hd.ne' using 1
    · rfl
    · dsimp only [Pi.sub_apply,id_eq]
      field_simp [hd.ne'];ring
  · positivity

theorem actual_source_real_part_is_strictly_increasing_in_cosine :
    StrictMonoOn realPartFromCosine (Icc (-1) 1) := by
  intro x hx y hy hxy
  have hxpos := actual_denominator_is_strictly_positive_for_every_cosine x hx.2
  have hypos := actual_denominator_is_strictly_positive_for_every_cosine y hy.2
  change (3/5)*(x-4/5)/(41/25-8/5*x)<(3/5)*(y-4/5)/(41/25-8/5*y)
  rw [div_lt_div_iff₀ hxpos hypos]
  nlinarith

theorem actual_source_real_part_minimum_is_attained_at_pi :
    IsLeast (Set.range (fun omega : ℝ=>(sourceTransfer (unitPoint omega)).re)) (-1/3:ℝ) ∧
      (sourceTransfer (unitPoint Real.pi)).re= -1/3 := by
  have hpi : (sourceTransfer (unitPoint Real.pi)).re= -1/3 := by
    rw [actual_source_real_part_on_the_unit_circle]
    norm_num [realPartFromCosine]
  refine ⟨⟨⟨Real.pi,hpi⟩,?_⟩,hpi⟩
  rintro value ⟨omega,rfl⟩
  dsimp only
  rw [actual_source_real_part_on_the_unit_circle]
  have hc := Real.neg_one_le_cos omega
  have hd := actual_denominator_is_strictly_positive_for_every_cosine (Real.cos omega)
    (Real.cos_le_one omega)
  change (-1/3:ℝ)≤(3/5)*(Real.cos omega-4/5)/(41/25-8/5*Real.cos omega)
  rw [le_div_iff₀ hd]
  linarith

theorem actual_source_frequency_gain_is_attained_three :
    IsGreatest (Set.range (fun omega : ℝ=>‖sourceTransfer (unitPoint omega)‖)) (3:ℝ) ∧
      sSup (Set.range (fun omega : ℝ=>‖sourceTransfer (unitPoint omega)‖))=3 := by
  have h0 : ‖sourceTransfer (unitPoint 0)‖=(3:ℝ) := by
    norm_num [unitPoint,sourceTransfer]
  have hg : IsGreatest (Set.range (fun omega : ℝ=>‖sourceTransfer (unitPoint omega)‖)) (3:ℝ) := by
    refine ⟨⟨0,h0⟩,?_⟩
    rintro value ⟨omega,rfl⟩
    have hb : (1/5:ℝ)≤‖unitPoint omega-4/5‖ := by
      have h := norm_sub_norm_le (unitPoint omega) (4/5:ℂ)
      rw [actual_unit_circle_point_has_norm_one] at h
      norm_num at h
      linarith
    dsimp only
    rw [sourceTransfer,norm_div]
    norm_num
    rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/5) hb)]
    linarith
  exact ⟨hg,hg.csSup_eq⟩

theorem actual_all_frequency_strict_circle_condition_iff (kappa : ℝ) (hk : 0≤kappa) :
    (∃epsilon : ℝ,0<epsilon ∧ ∀omega : ℝ,
      epsilon≤1+kappa*(sourceTransfer (unitPoint omega)).re) ↔ kappa<3 := by
  constructor
  · rintro ⟨epsilon,he,hall⟩
    have hp := hall Real.pi
    rw [actual_source_real_part_minimum_is_attained_at_pi.2] at hp
    linarith
  · intro hk3
    refine ⟨1-kappa/3,by linarith,?_⟩
    intro omega
    have h := actual_source_real_part_minimum_is_attained_at_pi.1.2 ⟨omega,rfl⟩
    have hm := mul_le_mul_of_nonneg_left h hk
    linarith

end SafeLearning.CompleteAppliedCircleFrequency
