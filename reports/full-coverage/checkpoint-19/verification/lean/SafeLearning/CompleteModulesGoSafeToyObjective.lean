import SafeLearning.CompleteModulesGoSafeToyIslands

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Set
namespace SafeLearning.CompleteModulesGoSafeToyObjective
open SafeLearning.CompleteModulesGoSafeToyAffine SafeLearning.CompleteModulesGoSafeToyFeasibility
open SafeLearning.CompleteModulesGoSafeToyIslands

def actualObjective (p : ℝ × ℝ) : ℝ :=
  Real.exp (-((p.1-3/4)^2+(p.2-3/5)^2)/(2*(13/100)^2))+
    (3/5)*Real.exp (-((p.1-1/4)^2+(p.2-2/5)^2)/(2*(13/100)^2))+(1/10)*p.2

def actualParameterBox : Set (ℝ × ℝ) := Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1

theorem actual_gaussian_exponential_has_the_true_reciprocal_envelope
    (dx dy cutoff : ℝ) (hc : 0 ≤ cutoff)
    (hd : cutoff ≤ (dx^2+dy^2)/(2*(13/100)^2)) :
    Real.exp (-(dx^2+dy^2)/(2*(13/100)^2)) ≤ 1/(1+cutoff) := by
  let z : ℝ := (dx^2+dy^2)/(2*(13/100)^2)
  have hz : cutoff ≤ z := hd
  have he := Real.add_one_le_exp z
  have hp := Real.exp_pos (-z)
  have hid : Real.exp z*Real.exp (-z)=1 := by rw [← Real.exp_add];simp
  have hm := mul_le_mul_of_nonneg_right he hp.le
  have hbound : (1+cutoff)*Real.exp (-z) ≤ 1 := by nlinarith
  have hden : 0 < 1+cutoff := by linarith
  rw [neg_div]
  change Real.exp (-z) ≤ 1/(1+cutoff)
  apply (le_div_iff₀ hden).mpr
  nlinarith

theorem actual_gaussian_blobs_are_positive_and_at_most_one (x y : ℝ) :
    0 < Real.exp (-(x^2+y^2)/(2*(13/100)^2)) ∧
      Real.exp (-(x^2+y^2)/(2*(13/100)^2)) ≤ 1 := by
  constructor
  · exact Real.exp_pos _
  · apply Real.exp_le_one_iff.mpr
    have hs : 0 ≤ x^2+y^2 := by positivity
    norm_num
    nlinarith

theorem actual_source_second_island_center_objective_is_at_least_one_point_zero_six :
    (53/50:ℝ) ≤ actualObjective (3/4,3/5) := by
  unfold actualObjective
  norm_num only [Prod.fst,Prod.snd,sub_self,pow_two,zero_mul,zero_add,neg_zero,zero_div,Real.exp_zero]
  have he := (Real.exp_pos (-(((3/4:ℝ)-1/4)^2+((3/5:ℝ)-2/5)^2)/(2*(13/100)^2))).le
  nlinarith

theorem actual_source_every_objective_at_least_the_second_center_lies_strictly_in_the_second_island_core
    (p : ℝ × ℝ) (hp : p ∈ actualParameterBox) (hscore : (53/50:ℝ) ≤ actualObjective p) :
    (5/8:ℝ) < p.1 ∧ p.1 < (7/8:ℝ) := by
  have hp1 : p.1 ∈ Icc (0:ℝ) 1 := hp.1
  have hp2 : p.2 ∈ Icc (0:ℝ) 1 := hp.2
  have hfirst := actual_gaussian_blobs_are_positive_and_at_most_one (p.1-3/4) (p.2-3/5)
  have hsecond := actual_gaussian_blobs_are_positive_and_at_most_one (p.1-1/4) (p.2-2/5)
  have hx : (1/2:ℝ) < p.1 := by
    by_contra h
    have hx : p.1 ≤ (1/2:ℝ) := by linarith
    have hsq : (1/16:ℝ) ≤ (p.1-3/4)^2 := by nlinarith [sq_nonneg (p.1-1/2)]
    have hb := actual_gaussian_exponential_has_the_true_reciprocal_envelope
      (p.1-3/4) (p.2-3/5) (625/338) (by norm_num) (by norm_num; nlinarith [sq_nonneg (p.2-3/5)])
    have hb' : Real.exp (-((p.1-3/4)^2+(p.2-3/5)^2)/(2*(13/100)^2)) ≤ (338/963:ℝ) := by
      convert hb using 1 <;> norm_num
    unfold actualObjective at hscore
    nlinarith [hp2.2,hsecond.2]
  have hsecondBound : Real.exp (-((p.1-1/4)^2+(p.2-2/5)^2)/(2*(13/100)^2)) ≤ (338/963:ℝ) := by
    have hsq : (1/16:ℝ) ≤ (p.1-1/4)^2 := by nlinarith [sq_nonneg (p.1-1/2)]
    have hb := actual_gaussian_exponential_has_the_true_reciprocal_envelope
      (p.1-1/4) (p.2-2/5) (625/338) (by norm_num) (by norm_num; nlinarith [sq_nonneg (p.2-2/5)])
    convert hb using 1 <;> norm_num
  have hnear : |p.1-3/4| < (1/8:ℝ) := by
    by_contra h
    have hsq : (1/64:ℝ) ≤ (p.1-3/4)^2 := by
      have hab : (1/8:ℝ) ≤ |p.1-3/4| := by linarith
      have hm := mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 1/8) hab
      simp only [← pow_two,sq_abs] at hm
      norm_num at hm
      exact hm
    have hb := actual_gaussian_exponential_has_the_true_reciprocal_envelope
      (p.1-3/4) (p.2-3/5) (625/1352) (by norm_num) (by norm_num; nlinarith [sq_nonneg (p.2-3/5)])
    have hb' : Real.exp (-((p.1-3/4)^2+(p.2-3/5)^2)/(2*(13/100)^2)) ≤ (1352/1977:ℝ) := by
      convert hb using 1 <;> norm_num
    unfold actualObjective at hscore
    nlinarith [hp2.2]
  rw [abs_lt] at hnear
  constructor <;> linarith

theorem actual_source_objective_is_continuous : Continuous actualObjective := by
  unfold actualObjective
  fun_prop

theorem actual_source_every_high_objective_box_point_belongs_to_the_actual_second_safe_island
    (p : ℝ × ℝ) (hp : p ∈ actualParameterBox) (hscore : (53/50:ℝ) ≤ actualObjective p) :
    p.1 ∈ Ioo (1/2+actualBoundary (actualGain p.2)) (1-actualBoundary (actualGain p.2)) ∧
      0 ≤ actualSourceSafety (actualGain p.2) p.1 := by
  have hg : actualGain p.2 ∈ Icc (3:ℝ) 8 := by
    have hy := hp.2
    constructor <;> unfold actualGain <;> linarith [hy.1,hy.2]
  have hb := actual_boundary_lies_strictly_between_one_twelfth_and_one_eighth _ hg
  have hx := actual_source_every_objective_at_least_the_second_center_lies_strictly_in_the_second_island_core p hp hscore
  have hi : p.1 ∈ Ioo (1/2+actualBoundary (actualGain p.2)) (1-actualBoundary (actualGain p.2)) := by
    constructor <;> linarith [hb.2,hx.1,hx.2]
  refine ⟨hi,?_⟩
  apply (actual_source_safe_set_is_exactly_two_disjoint_closed_islands _ _ hg hp.1).mpr
  right
  exact ⟨hi.1.le,hi.2.le⟩

theorem actual_source_objective_has_a_genuine_global_box_maximum_and_every_maximizer_is_in_the_second_island_core :
    (∃ p ∈ actualParameterBox, IsGreatest (actualObjective '' actualParameterBox) (actualObjective p)) ∧
    ∀ p ∈ actualParameterBox, IsGreatest (actualObjective '' actualParameterBox) (actualObjective p) →
      (5/8:ℝ)<p.1 ∧ p.1<(7/8:ℝ) := by
  constructor
  · have hc : IsCompact actualParameterBox := isCompact_Icc.prod isCompact_Icc
    have hn : actualParameterBox.Nonempty := ⟨(3/4,3/5),by norm_num [actualParameterBox]⟩
    obtain ⟨p,hp,hm⟩ := hc.exists_isMaxOn hn actual_source_objective_is_continuous.continuousOn
    refine ⟨p,hp,⟨⟨p,hp,rfl⟩,?_⟩⟩
    rintro value ⟨q,hq,rfl⟩
    exact hm hq
  · intro p hp hm
    have hs : actualObjective (3/4,3/5) ≤ actualObjective p :=
      hm.2 ⟨(3/4,3/5),by norm_num [actualParameterBox],rfl⟩
    exact actual_source_every_objective_at_least_the_second_center_lies_strictly_in_the_second_island_core
      p hp (actual_source_second_island_center_objective_is_at_least_one_point_zero_six.trans hs)

end SafeLearning.CompleteModulesGoSafeToyObjective
