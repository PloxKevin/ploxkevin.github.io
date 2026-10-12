import SafeLearning.CompleteDualPILinearModel

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open SafeLearning.CompleteDualPILinearModel
namespace SafeLearning.CompleteDualPIJury

theorem real_pair_jury_criterion (x y : ℝ) :
    |x|<1 ∧ |y|<1 ↔ |x*y|<1 ∧ |x+y|<1+x*y := by
  simp only [abs_lt]
  constructor
  · rintro ⟨⟨hx1,hx2⟩,hy1,hy2⟩
    have hp := mul_pos (by linarith : 0<1-x) (by linarith : 0<1-y)
    have hm := mul_pos (by linarith : 0<1+x) (by linarith : 0<1+y)
    have hpp := mul_pos (by linarith : 0<1-x) (by linarith : 0<1+y)
    have hmp := mul_pos (by linarith : 0<1+x) (by linarith : 0<1-y)
    refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩ <;> nlinarith
  · rintro ⟨⟨hd1,hd2⟩,ht1,ht2⟩
    have hp : 0<(1-x)*(1-y) := by nlinarith
    have hm : 0<(1+x)*(1+y) := by nlinarith
    have upper : ∀ u v : ℝ, u*v<1 → 0<(1-u)*(1-v) → u<1 := by
      intro u v huv hprod
      by_contra hu
      have hu1 : 1≤u := le_of_not_gt hu
      have hv : 1<v := by
        by_contra hv
        have hv1 : v≤1 := le_of_not_gt hv
        have hn := mul_nonpos_of_nonpos_of_nonneg (by linarith : 1-u≤0)
          (by linarith : 0≤1-v)
        linarith
      have hmul := mul_le_mul hu1 hv.le (by norm_num : (0:ℝ)≤1) (by linarith : 0≤u)
      nlinarith
    have hx2 := upper x y hd2 hp
    have hy2 := upper y x (by simpa [mul_comm] using hd2) (by simpa [mul_comm] using hp)
    have hx1 := upper (-x) (-y) (by nlinarith) (by simpa using hm)
    have hy1 := upper (-y) (-x) (by nlinarith) (by simpa [mul_comm] using hm)
    refine ⟨⟨?_,hx2⟩,⟨?_,hy2⟩⟩ <;> linarith

theorem norm_lt_one_iff_normSq_lt_one (z : ℂ) : ‖z‖<1 ↔ Complex.normSq z<1 := by
  have hsq := Complex.sq_norm z
  have hn := norm_nonneg z
  constructor <;> intro h <;> nlinarith

theorem actual_characteristic_has_root (trace determinant : ℝ) :
    ∃ z : ℂ, characteristic trace determinant z=0 := by
  obtain ⟨w,hw⟩ := IsAlgClosed.exists_pow_nat_eq
    ((trace:ℂ)^2-4*(determinant:ℂ)) (by norm_num : 0<(2:ℕ))
  refine ⟨((trace:ℂ)+w)/2,?_⟩
  unfold characteristic
  linear_combination hw/4

theorem actual_real_characteristic_other_root (trace determinant x : ℝ)
    (hroot : characteristic trace determinant (x:ℂ)=0) :
    x*(trace-x)=determinant ∧
      characteristic trace determinant ((trace-x:ℝ):ℂ)=0 := by
  have hr := congrArg Complex.re hroot
  simp [characteristic,pow_two] at hr
  constructor
  · nlinarith
  · apply Complex.ext <;> simp [characteristic,Complex.mul_re,Complex.mul_im,pow_two]
    nlinarith

/-- Genuine necessity and sufficiency for every complex root of the actual quadratic. -/
theorem all_roots_strictly_inside_unit_disk_iff_jury (trace determinant : ℝ) :
    (∀ z : ℂ, characteristic trace determinant z=0 → ‖z‖<1) ↔
      |determinant|<1 ∧ |trace|<1+determinant := by
  constructor
  · intro hall
    obtain ⟨z,hz⟩ := actual_characteristic_has_root trace determinant
    by_cases him : z.im=0
    · have he : z=(z.re:ℂ) := by apply Complex.ext <;> simp [him]
      have hroot : characteristic trace determinant (z.re:ℂ)=0 := by rwa [← he]
      obtain ⟨hprod,hother⟩ := actual_real_characteristic_other_root trace determinant z.re hroot
      have hx : |z.re|<1 := by
        have hx := hall z hz
        rw [he,Complex.norm_real,Real.norm_eq_abs] at hx
        exact hx
      have hy : |trace-z.re|<1 := by
        have hy := hall _ hother
        rw [Complex.norm_real,Real.norm_eq_abs] at hy
        exact hy
      have hp := (real_pair_jury_criterion z.re (trace-z.re)).mp ⟨hx,hy⟩
      simpa [hprod] using hp
    · obtain ⟨ht,hn,_⟩ := actual_any_nonreal_root_has_source_modulus trace determinant z hz him
      have hd : determinant<1 := by rw [← hn];exact (norm_lt_one_iff_normSq_lt_one z).mp (hall z hz)
      have hd0 : 0≤determinant := by rw [← hn];exact Complex.normSq_nonneg z
      have hi : 0<z.im^2 := sq_pos_of_ne_zero him
      have hnorm : z.re^2+z.im^2=determinant := by simpa [Complex.normSq_apply,pow_two] using hn
      simp only [abs_lt]
      refine ⟨⟨by linarith,hd⟩,⟨?_,?_⟩⟩ <;>
        nlinarith [sq_nonneg (z.re-1),sq_nonneg (z.re+1)]
  · rintro ⟨hd,ht⟩ z hz
    by_cases him : z.im=0
    · have he : z=(z.re:ℂ) := by apply Complex.ext <;> simp [him]
      have hroot : characteristic trace determinant (z.re:ℂ)=0 := by rwa [← he]
      obtain ⟨hprod,_⟩ := actual_real_characteristic_other_root trace determinant z.re hroot
      have hp : |z.re*(trace-z.re)|<1 ∧ |z.re+(trace-z.re)|<1+z.re*(trace-z.re) := by
        simpa [hprod] using And.intro hd ht
      have hx := ((real_pair_jury_criterion z.re (trace-z.re)).mpr hp).1
      rw [he,Complex.norm_real,Real.norm_eq_abs]
      exact hx
    · obtain ⟨_,hn,_⟩ := actual_any_nonreal_root_has_source_modulus trace determinant z hz him
      apply (norm_lt_one_iff_normSq_lt_one z).mpr
      rw [hn]
      exact (abs_lt.mp hd).2

theorem actual_uncurved_spectral_stability_region (c kp ki : ℝ) :
    (∀ z : ℂ,characteristic (2-c*(kp+ki)) (1-c*kp) z=0 → ‖z‖<1) ↔
      0<c*kp ∧ c*kp<2 ∧ 0<c*ki ∧ c*(2*kp+ki)<4 := by
  rw [all_roots_strictly_inside_unit_disk_iff_jury,actual_uncurved_jury_gain_region]

theorem actual_curved_spectral_stability_region (a c kp ki : ℝ) :
    (∀ z : ℂ,characteristic (1+a-c*(kp+ki)) (a-c*kp) z=0 → ‖z‖<1) ↔
      a-1<c*kp ∧ c*kp<a+1 ∧ 0<c*ki ∧ c*(2*kp+ki)<2*(1+a) := by
  rw [all_roots_strictly_inside_unit_disk_iff_jury,actual_curved_jury_gain_region]

theorem pure_integral_never_strictly_spectrally_stable (c ki : ℝ) :
    ¬(∀ z : ℂ,characteristic (2-c*ki) 1 z=0 → ‖z‖<1) := by
  rw [all_roots_strictly_inside_unit_disk_iff_jury]
  norm_num

end SafeLearning.CompleteDualPIJury
