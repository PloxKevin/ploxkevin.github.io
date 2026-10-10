import SafeLearning.CompletePolicyQuadraticDualConvex

set_option autoImplicit false
noncomputable section
open Set Matrix
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator
namespace SafeLearning.CompletePolicyQuadraticPerspective
open SafeLearning.CompletePolicyQuadraticDual
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def whiten (H : Matrix ι ι ℝ) (v : ι → ℝ) : ι → ℝ := CFC.sqrt H⁻¹ *ᵥ v

theorem actual_whitening_norm_identity (H : Matrix ι ι ℝ) (hH : H.PosDef)
    (v : ι → ℝ) :
    ‖WithLp.toLp 2 (whiten H v)‖ ^ 2 = v ⬝ᵥ (H⁻¹ *ᵥ v) := by
  have hn : 0 ≤ H⁻¹ := hH.inv.posSemidef.nonneg
  have hs : CFC.sqrt H⁻¹ * CFC.sqrt H⁻¹ = H⁻¹ := by
    simpa only [pow_two] using CFC.sq_sqrt H⁻¹
  have hh : (CFC.sqrt H⁻¹).IsHermitian := (CFC.sqrt_nonneg H⁻¹).posSemidef.isHermitian
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [WithLp.ofLp_toLp,pow_two]
  change (whiten H v) ⬝ᵥ (whiten H v) = _
  unfold whiten
  have he := hh.star_dotProduct_mulVec_comm v (CFC.sqrt H⁻¹ *ᵥ v)
  simp only [star_trivial] at he
  rw [dotProduct_comm (CFC.sqrt H⁻¹ *ᵥ v) (CFC.sqrt H⁻¹ *ᵥ v),←he,
    mulVec_mulVec,hs]

theorem actual_whitening_is_affine_in_nu (H : Matrix ι ι ℝ) (g b : ι → ℝ)
    (u v a z : ℝ) (haz : a+z=1) :
    whiten H (g-(a*u+z*v) • b) = a • whiten H (g-u • b)+z • whiten H (g-v • b) := by
  unfold whiten
  simp only [mulVec_sub,mulVec_smul,smul_sub]
  have hz : z=1-a := by linarith
  rw [hz]
  module

def perspectiveDomain : Set ((ι → ℝ) × ℝ) := {p | 0 < p.2}

theorem actual_perspective_domain_is_convex : Convex ℝ (perspectiveDomain (ι := ι)) := by
  intro p hp t ht a z ha hz haz
  change 0 < a*p.2+z*t.2
  change 0 < p.2 at hp
  change 0 < t.2 at ht
  by_cases hp' : 0 < a
  · exact lt_of_lt_of_le (mul_pos hp' hp) (le_add_of_nonneg_right (mul_nonneg hz ht.le))
  · have ha0 : a=0 := le_antisymm (le_of_not_gt hp') ha
    have hz1 : z=1 := by linarith
    simpa [ha0,hz1] using ht

theorem actual_quadratic_perspective_is_jointly_convex (H : Matrix ι ι ℝ) (hH : H.PosDef) :
    ConvexOn ℝ perspectiveDomain (fun p : (ι → ℝ) × ℝ =>
      (p.1 ⬝ᵥ (H⁻¹ *ᵥ p.1))/(2*p.2)) := by
  have he (p : (ι → ℝ) × ℝ) (hp : 0 < p.2) :
      actualDual H p.1 0 0 0 (p.2,0)=(p.1 ⬝ᵥ (H⁻¹ *ᵥ p.1))/(2*p.2) := by
    rw [actual_true_supremum_equals_closed_dual H hH p.1 0 0 0 p.2 0 hp]
    simp [closedDual]
  refine ⟨actual_perspective_domain_is_convex,?_⟩
  intro p hp t ht a z ha hz haz
  have hnew := actual_perspective_domain_is_convex hp ht ha hz haz
  dsimp only at ⊢
  rw [←he _ hnew,←he p hp,←he t ht]
  simp only [smul_eq_mul]
  unfold actualDual at ⊢
  apply csSup_le (range_nonempty _)
  rintro y ⟨x,rfl⟩
  have hm (q : (ι → ℝ) × ℝ) (hq : 0 < q.2) :
      lagrangian H q.1 0 0 0 q.2 0 x ≤ actualDual H q.1 0 0 0 (q.2,0) :=
    CompletePolicyQuadraticDualConvex.actual_lagrangian_is_bounded_by_its_true_supremum H hH q.1 0 0 0 (q.2,0) hq x
  have hf : lagrangian H (a • p.1+z • t.1) 0 0 0 (a*p.2+z*t.2) 0 x =
      a*lagrangian H p.1 0 0 0 p.2 0 x+z*lagrangian H t.1 0 0 0 t.2 0 x := by
    simp [lagrangian,add_dotProduct,smul_dotProduct]
    ring
  change lagrangian H (a • p.1+z • t.1) 0 0 0 (a*p.2+z*t.2) 0 x ≤ _
  rw [hf]
  exact add_le_add (mul_le_mul_of_nonneg_left (hm p hp) ha)
    (mul_le_mul_of_nonneg_left (hm t ht) hz)

theorem actual_euclidean_norm_square_perspective_is_jointly_convex :
    ConvexOn ℝ (perspectiveDomain (ι := ι))
      (fun p : (ι → ℝ) × ℝ => ‖WithLp.toLp 2 p.1‖^2/(2*p.2)) := by
  have h := actual_quadratic_perspective_is_jointly_convex (1 : Matrix ι ι ℝ) Matrix.PosDef.one
  apply h.congr
  intro p _
  rw [inv_one,Matrix.one_mulVec,EuclideanSpace.real_norm_sq_eq]
  simp only [dotProduct,WithLp.ofLp_toLp,pow_two]

theorem actual_closed_dual_has_the_literal_norm_perspective_form
    (H : Matrix ι ι ℝ) (hH : H.PosDef) (g b : ι → ℝ) (c δ lam nu : ℝ) :
    closedDual H g b c δ lam nu =
      ‖WithLp.toLp 2 (whiten H (g-nu • b))‖^2/(2*lam)-nu*c+lam*δ := by
  rw [actual_whitening_norm_identity H hH]
  rfl

end SafeLearning.CompletePolicyQuadraticPerspective
