import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped BigOperators Topology

namespace SafeLearning.CompleteFoundationsExtrema

theorem fraction_image : (fun x : ℝ => x/(1+x)) '' Ici (0 : ℝ)=Ico 0 1 := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    change 0≤x at hx
    refine ⟨div_nonneg hx (by linarith),?_⟩
    rw [div_lt_iff₀ (by linarith)]
    linarith
  · intro hy
    refine ⟨y/(1-y),div_nonneg hy.1 (by linarith [hy.2]),?_⟩
    have hden : 1-y≠0 := by linarith [hy.2]
    have hden₂ : 1+y/(1-y)≠0 := by
      have hp : 0≤y/(1-y) := div_nonneg hy.1 (by linarith [hy.2])
      linarith
    field_simp
    ring

theorem fraction_strictly_increases : StrictMonoOn (fun x : ℝ => x/(1+x)) (Ici 0) := by
  intro x hx y hy hxy
  change 0≤x at hx
  change 0≤y at hy
  rw [div_lt_div_iff₀ (by linarith : 0<1+x) (by linarith : 0<1+y)]
  nlinarith

theorem fraction_extrema :
    IsGLB ((fun x : ℝ => x/(1+x)) '' Ici (0 : ℝ)) 0 ∧
      IsLUB ((fun x : ℝ => x/(1+x)) '' Ici (0 : ℝ)) 1 ∧
      (0 : ℝ) ∈ ((fun x : ℝ => x/(1+x)) '' Ici (0 : ℝ)) ∧
      (1 : ℝ) ∉ ((fun x : ℝ => x/(1+x)) '' Ici (0 : ℝ)) := by
  rw [fraction_image]
  exact ⟨isGLB_Ico (by norm_num),isLUB_Ico (by norm_num),by norm_num,by norm_num⟩

theorem fraction_limit_at_infinity :
    Tendsto (fun x : ℝ => x/(1+x)) atTop (𝓝 1) := by
  have hi : Tendsto (fun x : ℝ => (x+1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id)
  have ht : Tendsto (fun x : ℝ => 1-(x+1)⁻¹) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hi
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hn : x+1≠0 := by linarith
  field_simp
  ring

theorem multiplicative_initial_values :
    (-1 : ℝ)^0*(1+1/(0+1))=2 ∧
    (-1 : ℝ)^1*(1+1/(1+1))= -3/2 ∧
    (-1 : ℝ)^2*(1+1/(2+1))=4/3 ∧
    (-1 : ℝ)^3*(1+1/(3+1))= -5/4 := by norm_num

theorem even_odd_monotonicity :
    Antitone (fun n : ℕ => 1+1/((2*n : ℝ)+1)) ∧
      Monotone (fun n : ℕ => -1-1/((2*n : ℝ)+2)) := by
  constructor
  · intro n m hnm
    have hcast : (n : ℝ) ≤ m := by exact_mod_cast hnm
    have h := one_div_le_one_div_of_le
      (by positivity : (0 : ℝ)<2*n+1) (by linarith : (2*n : ℝ)+1≤2*m+1)
    linarith
  · intro n m hnm
    have hcast : (n : ℝ) ≤ m := by exact_mod_cast hnm
    have h := one_div_le_one_div_of_le
      (by positivity : (0 : ℝ)<2*n+2) (by linarith : (2*n : ℝ)+2≤2*m+2)
    linarith

theorem sine_cosine_upper (x : ℝ) : Real.sin x+Real.cos x≤Real.sqrt 2 := by
  have hsq := Real.sin_sq_add_cos_sq x
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)
  nlinarith [sq_nonneg (Real.sin x-Real.cos x),Real.sqrt_nonneg 2]

theorem sine_cosine_shift (x : ℝ) :
    Real.sin x+Real.cos x=Real.sqrt 2*Real.sin (x+Real.pi/4) := by
  rw [Real.sin_add,Real.sin_pi_div_four,Real.cos_pi_div_four]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)
  linear_combination -(Real.sin x+Real.cos x)/2 * hs

theorem sine_cosine_attains :
    Real.sin (Real.pi/4)+Real.cos (Real.pi/4)=Real.sqrt 2 := by
  rw [Real.sin_pi_div_four,Real.cos_pi_div_four]; ring

theorem sine_cosine_supremum :
    IsLUB (range (fun x : ℝ => Real.sin x+Real.cos x)) (Real.sqrt 2) := by
  refine ⟨?_,?_⟩
  · rintro y ⟨x,rfl⟩; exact sine_cosine_upper x
  · intro b hb
    have h := hb (mem_range_self (Real.pi/4))
    rw [sine_cosine_attains] at h
    exact h

theorem individual_trig_suprema : IsLUB (range Real.sin) 1 ∧ IsLUB (range Real.cos) 1 := by
  constructor
  · refine ⟨?_,?_⟩
    · rintro y ⟨x,rfl⟩; exact Real.sin_le_one x
    · intro b hb; simpa using hb (mem_range_self (Real.pi/2))
  · refine ⟨?_,?_⟩
    · rintro y ⟨x,rfl⟩; exact Real.cos_le_one x
    · intro b hb; simpa using hb (mem_range_self 0)

theorem trig_decimal_and_strict_gap :
    |Real.sqrt 2-(1414/1000 : ℝ)|<1/2000 ∧ Real.sqrt 2<2 ∧
      ¬ ∃ x : ℝ, Real.sin x=1 ∧ Real.cos x=1 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)
  have hp := Real.sqrt_nonneg 2
  refine ⟨?_,?_,?_⟩
  · rw [abs_lt]; constructor <;> nlinarith
  · nlinarith
  · rintro ⟨x,h₁,h₂⟩; have h := Real.sin_sq_add_cos_sq x; rw [h₁,h₂] at h; norm_num at h

theorem bilinear_inner_supremum (x : ℝ) :
    IsLUB ((fun y : ℝ => x*y) '' Icc (-1 : ℝ) 1) |x| := by
  have hbound : ∀ y ∈ Icc (-1 : ℝ) 1, x*y≤|x| := by
    intro y hy
    have hyabs : |y|≤1 := abs_le.mpr hy
    have hprod := mul_le_mul_of_nonneg_left hyabs (abs_nonneg x)
    exact (le_abs_self (x*y)).trans (by rw [abs_mul]; simpa using hprod)
  refine ⟨?_,?_⟩
  · rintro y ⟨z,hz,rfl⟩; exact hbound z hz
  · intro b hb
    by_cases hx : 0≤x
    · have h := hb (show x*1 ∈ ((fun y : ℝ => x*y) '' Icc (-1 : ℝ) 1) from ⟨1,by norm_num,rfl⟩)
      simpa [abs_of_nonneg hx] using h
    · have h := hb (show x*(-1) ∈ ((fun y : ℝ => x*y) '' Icc (-1 : ℝ) 1) from ⟨-1,by norm_num,rfl⟩)
      simpa [abs_of_nonpos (le_of_not_ge hx)] using h

theorem bilinear_inner_infimum (y : ℝ) :
    IsGLB ((fun x : ℝ => x*y) '' Icc (-1 : ℝ) 1) (-|y|) := by
  have hbound : ∀ x ∈ Icc (-1 : ℝ) 1, -|y|≤x*y := by
    intro x hx
    have hxabs : |x|≤1 := abs_le.mpr hx
    have hprod := mul_le_mul_of_nonneg_right hxabs (abs_nonneg y)
    have hneg := neg_abs_le (x*y)
    rw [abs_mul] at hneg
    nlinarith
  refine ⟨?_,?_⟩
  · rintro x ⟨z,hz,rfl⟩; exact hbound z hz
  · intro b hb
    by_cases hy : 0≤y
    · have h := hb (show (-1)*y ∈ ((fun x : ℝ => x*y) '' Icc (-1 : ℝ) 1) from ⟨-1,by norm_num,rfl⟩)
      simpa [abs_of_nonneg hy] using h
    · have h := hb (show 1*y ∈ ((fun x : ℝ => x*y) '' Icc (-1 : ℝ) 1) from ⟨1,by norm_num,rfl⟩)
      simpa [abs_of_nonpos (le_of_not_ge hy)] using h

theorem bilinear_outer_values :
    IsGLB ((fun x : ℝ => |x|) '' Icc (-1 : ℝ) 1) 0 ∧
      IsLUB ((fun y : ℝ => -|y|) '' Icc (-1 : ℝ) 1) 0 ∧
      ∀ x y : ℝ, (0 : ℝ)*y≤0*0 ∧ 0*0≤x*0 := by
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,?_⟩
  · rintro v ⟨x,hx,rfl⟩; exact abs_nonneg x
  · intro b hb; simpa using hb (show |(0 : ℝ)| ∈ ((fun x : ℝ => |x|) '' Icc (-1 : ℝ) 1) from ⟨0,by norm_num,rfl⟩)
  · rintro v ⟨y,hy,rfl⟩; exact neg_nonpos.mpr (abs_nonneg y)
  · intro b hb; simpa using hb (show -|(0 : ℝ)| ∈ ((fun y : ℝ => -|y|) '' Icc (-1 : ℝ) 1) from ⟨0,by norm_num,rfl⟩)
  · intro x y; simp

theorem actual_bilinear_minimax_values :
    sInf ((fun x : ℝ => sSup ((fun y : ℝ => x*y) '' Icc (-1 : ℝ) 1)) '' Icc (-1 : ℝ) 1)=0 ∧
      sSup ((fun y : ℝ => sInf ((fun x : ℝ => x*y) '' Icc (-1 : ℝ) 1)) '' Icc (-1 : ℝ) 1)=0 := by
  have hne : (Icc (-1 : ℝ) 1).Nonempty := ⟨0,by norm_num⟩
  have hs (x : ℝ) : sSup ((fun y : ℝ => x*y) '' Icc (-1 : ℝ) 1)=|x| :=
    (bilinear_inner_supremum x).csSup_eq (hne.image _)
  have hi (y : ℝ) : sInf ((fun x : ℝ => x*y) '' Icc (-1 : ℝ) 1)= -|y| :=
    (bilinear_inner_infimum y).csInf_eq (hne.image _)
  simp_rw [hs,hi]
  exact ⟨bilinear_outer_values.1.csInf_eq (hne.image _),
    bilinear_outer_values.2.1.csSup_eq (hne.image _)⟩

end SafeLearning.CompleteFoundationsExtrema
