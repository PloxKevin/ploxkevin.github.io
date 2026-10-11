import SafeLearning.CompleteModulesScalarSDP

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesTwoByTwoNSD
open CompleteModulesScalarSDP

theorem actual_symmetric_two_by_two_negative_quadratic_criterion (a b c : ℝ) :
    (∀ x y : ℝ,a*x^2+2*b*x*y+c*y^2 ≤ 0) ↔
      a ≤ 0 ∧ c ≤ 0 ∧ 0 ≤ a*c-b^2 := by
  constructor
  · intro h
    have ha := h 1 0
    have hc := h 0 1
    norm_num at ha hc
    refine ⟨ha,hc,?_⟩
    by_cases hneg : a < 0
    · have hschur := (negative_scalar_schur_iff c b a hneg).mp
        (by intro x y;convert h y x using 1 <;> ring)
      have hi : c-b^2/a=(a*c-b^2)/a := by field_simp [hneg.ne] <;> ring
      rw [hi] at hschur
      exact (div_nonpos_iff.mp hschur).resolve_right (by intro hh;linarith [hh.2]) |>.1
    · have hazero : a=0 := by linarith
      have hbzero : b=0 := by
        by_contra hn
        have hbad := h ((1-c)/(2*b)) 1
        have hi : 2*b*((1-c)/(2*b))=1-c := by field_simp [hn]
        rw [hazero] at hbad
        norm_num at hbad
        rw [hi] at hbad
        linarith
      simp [hazero,hbzero]
  · rintro ⟨ha,hc,hdet⟩
    by_cases hneg : a < 0
    · have hschur : c-b^2/a ≤ 0 := by
        have hi : c-b^2/a=(a*c-b^2)/a := by field_simp [hneg.ne] <;> ring
        rw [hi]
        exact div_nonpos_of_nonneg_of_nonpos hdet hneg.le
      have h := (negative_scalar_schur_iff c b a hneg).mpr hschur
      intro x y
      convert h y x using 1 <;> ring
    · have hazero : a=0 := by linarith
      have hbzero : b=0 := by rw [hazero] at hdet; nlinarith [sq_nonneg b]
      intro x y
      rw [hazero,hbzero]
      nlinarith [sq_nonneg y]

theorem actual_symmetric_two_by_two_negative_matrix_criterion (a b c : ℝ) :
    (-(!![a,b;b,c] : Matrix (Fin 2) (Fin 2) ℝ)).PosSemidef ↔
      a ≤ 0 ∧ c ≤ 0 ∧ 0 ≤ a*c-b^2 := by
  rw [← actual_symmetric_two_by_two_negative_quadratic_criterion]
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  have hh : (-(!![a,b;b,c] : Matrix (Fin 2) (Fin 2) ℝ)).IsHermitian := by
    ext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.conjTranspose_apply]
  constructor
  · intro h x y
    have hv := h.2 (![x,y] : Fin 2 → ℝ)
    simp [Matrix.mulVec,dotProduct,Fin.sum_univ_two] at hv
    nlinarith
  · intro h
    refine ⟨hh,?_⟩
    intro vector
    have hv := h (vector 0) (vector 1)
    simp [Matrix.mulVec,dotProduct,Fin.sum_univ_two]
    nlinarith

end SafeLearning.CompleteModulesTwoByTwoNSD
