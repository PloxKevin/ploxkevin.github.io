import SafeLearning.CompleteFoundationsGeometry
import SafeLearning.CompleteFoundationsNormDuality
import Mathlib.Analysis.Matrix.PosDef

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators Matrix RealInnerProductSpace

namespace SafeLearning.CompleteFoundationsLiteralInnerProduct28

section Generic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem actual_inner_product_has_every_source_axiom_and_induced_length (x y z : E) (a : ℝ) :
    ⟪x,y⟫=⟪y,x⟫ ∧ ⟪x+y,z⟫=⟪x,z⟫+⟪y,z⟫ ∧
    ⟪x,y+z⟫=⟪x,y⟫+⟪x,z⟫ ∧ ⟪a • x,y⟫=a*⟪x,y⟫ ∧
    ⟪x,a • y⟫=a*⟪x,y⟫ ∧ (x≠0 → 0<⟪x,x⟫) ∧ ‖x‖=Real.sqrt ⟪x,x⟫ := by
  exact ⟨real_inner_comm _ _,inner_add_left _ _ _,inner_add_right _ _ _,
    real_inner_smul_left _ _ _,real_inner_smul_right _ _ _,
    fun hx => real_inner_self_pos.mpr hx,norm_eq_sqrt_real_inner _⟩

theorem actual_nonzero_y_parabola_has_the_printed_completed_square (x y : E) (hy : y≠0) (t : ℝ) :
    ‖x-t • y‖^2=‖x‖^2-⟪x,y⟫^2/‖y‖^2+
      ‖y‖^2*(t-⟪x,y⟫/‖y‖^2)^2 := by
  rw [CompleteFoundationsGeometry.inner_product_quadratic_expansion]
  have hn : ‖y‖≠0 := norm_ne_zero_iff.mpr hy
  field_simp [hn]
  ring

theorem actual_nonzero_y_parabola_attains_the_printed_global_minimum (x y : E) (hy : y≠0) :
    ‖x-(⟪x,y⟫/‖y‖^2) • y‖^2=‖x‖^2-⟪x,y⟫^2/‖y‖^2 ∧
    0≤‖x‖^2-⟪x,y⟫^2/‖y‖^2 ∧
    ∀ t : ℝ, ‖x‖^2-⟪x,y⟫^2/‖y‖^2≤‖x-t • y‖^2 := by
  have he : ‖x-(⟪x,y⟫/‖y‖^2) • y‖^2=‖x‖^2-⟪x,y⟫^2/‖y‖^2 := by
    simpa using actual_nonzero_y_parabola_has_the_printed_completed_square x y hy (⟪x,y⟫/‖y‖^2)
  refine ⟨he,by rw [←he]; positivity,?_⟩
  intro t
  rw [actual_nonzero_y_parabola_has_the_printed_completed_square x y hy t]
  exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) (sq_nonneg _))

theorem actual_source_minimum_nonnegativity_derives_cauchy_schwarz (x y : E) :
    |⟪x,y⟫|≤‖x‖*‖y‖ := by
  by_cases hy : y=0
  · subst y; simp
  · have hn : 0<‖y‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hy)
    have hm := (actual_nonzero_y_parabola_attains_the_printed_global_minimum x y hy).2.1
    have hb : ⟪x,y⟫^2≤‖x‖^2*‖y‖^2 := by
      have hd : ⟪x,y⟫^2/‖y‖^2≤‖x‖^2 := by linarith
      exact (div_le_iff₀ hn).mp hd
    apply abs_le_of_sq_le_sq _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    simpa only [mul_pow] using hb

theorem actual_cauchy_schwarz_equality_forces_the_printed_scalar (x y : E) (hy : y≠0)
    (he : |⟪x,y⟫|=‖x‖*‖y‖) : x=(⟪x,y⟫/‖y‖^2) • y := by
  have hn : ‖y‖^2≠0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hy)
  have hs : ⟪x,y⟫^2=‖x‖^2*‖y‖^2 := by
    simpa only [sq_abs,mul_pow] using congrArg (fun a : ℝ => a^2) he
  have hz : ‖x‖^2-⟪x,y⟫^2/‖y‖^2=0 := by rw [hs,mul_div_cancel_right₀ _ hn]; ring
  have hm := (actual_nonzero_y_parabola_attains_the_printed_global_minimum x y hy).1
  rw [hz] at hm
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hm))

theorem actual_zero_y_cauchy_schwarz_both_sides_are_zero (x : E) :
    |⟪x,(0:E)⟫|=0 ∧ ‖x‖*‖(0:E)‖=0 := by simp
end Generic

section Finite
variable {I : Type*} [Fintype I] [DecidableEq I]

def weightedInner (M : Matrix I I ℝ) (x y : I → ℝ) : ℝ := x ⬝ᵥ (M *ᵥ y)
def weightedLength (M : Matrix I I ℝ) (x : I → ℝ) : ℝ := Real.sqrt (weightedInner M x x)

theorem actual_standard_euclidean_inner_and_induced_length (x y : I → ℝ) :
    ⟪CompleteFoundationsNormDuality.euclidean x,CompleteFoundationsNormDuality.euclidean y⟫=
      ∑ i,x i*y i ∧
    CompleteFoundationsNormDuality.l2Norm x=Real.sqrt (∑ i,x i*x i) := by
  constructor
  · simpa only [dotProduct] using CompleteFoundationsNormDuality.actual_euclidean_pairing_is_dot x y
  · simpa [CompleteFoundationsNormDuality.l2Norm,
      CompleteFoundationsNormDuality.actual_euclidean_pairing_is_dot,dotProduct] using
      norm_eq_sqrt_real_inner (CompleteFoundationsNormDuality.euclidean x)

theorem actual_weighted_inner_is_symmetric_and_linear_in_both_arguments
    (M : Matrix I I ℝ) (hM : M.PosDef) (x y z : I → ℝ) (a : ℝ) :
    weightedInner M x y=weightedInner M y x ∧
    weightedInner M (x+y) z=weightedInner M x z+weightedInner M y z ∧
    weightedInner M x (y+z)=weightedInner M x y+weightedInner M x z ∧
    weightedInner M (a • x) y=a*weightedInner M x y ∧
    weightedInner M x (a • y)=a*weightedInner M x y := by
  have ht : M.transpose=M := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hM.isHermitian.eq
  refine ⟨?_,?_,?_,?_,?_⟩
  · dsimp [weightedInner]
    rw [Matrix.dotProduct_mulVec,←Matrix.mulVec_transpose,ht,dotProduct_comm]
  · simp [weightedInner,add_dotProduct]
  · simp [weightedInner,Matrix.mulVec_add,dotProduct_add]
  · simp [weightedInner,smul_dotProduct]
  · simp [weightedInner,Matrix.mulVec_smul,dotProduct_smul]

theorem actual_positive_definite_weighted_inner_and_length_positive (M : Matrix I I ℝ)
    (hM : M.PosDef) (x : I → ℝ) (hx : x≠0) :
    0<weightedInner M x x ∧ 0<weightedLength M x := by
  have hp : 0<weightedInner M x x := by simpa only [star_trivial,weightedInner] using hM.dotProduct_mulVec_pos hx
  exact ⟨hp,Real.sqrt_pos.mpr hp⟩

theorem actual_weighted_length_vanishes_exactly_at_zero (M : Matrix I I ℝ)
    (hM : M.PosDef) (x : I → ℝ) : weightedLength M x=0 ↔ x=0 := by
  constructor
  · intro h
    by_contra hx
    exact (actual_positive_definite_weighted_inner_and_length_positive M hM x hx).2.ne' h
  · rintro rfl
    simp [weightedLength,weightedInner]

theorem actual_positive_diagonal_weights_supply_the_printed_inner_product (m : I → ℝ)
    (hm : ∀ i,0<m i) (x y : I → ℝ) :
    (Matrix.diagonal m).PosDef ∧
    weightedInner (Matrix.diagonal m) x y=∑ i,m i*x i*y i := by
  constructor
  · exact Matrix.PosDef.diagonal hm
  · simp [weightedInner,dotProduct,Matrix.diagonal_mulVec]
    apply Finset.sum_congr rfl
    intro i hi
    ring
end Finite

section OnlySourceAxioms
variable {F : Type*} [AddCommGroup F] [Module ℝ F]

private def sourceCore (b : F → F → ℝ)
    (hsym : ∀ x y, b x y=b y x)
    (hadd : ∀ x y z, b (x+y) z=b x z+b y z)
    (hsmul : ∀ a x y, b (a • x) y=a*b x y)
    (hpos : ∀ x, x≠0 → 0<b x x) : InnerProductSpace.Core ℝ F where
  inner := b
  conj_inner_symm x y := by simpa using hsym y x
  re_inner_nonneg x := by
    by_cases hx : x=0
    · subst x
      have hzero : b 0 0=0 := by simpa using hsmul 0 (0:F) (0:F)
      simpa [hzero]
    · simpa using le_of_lt (hpos x hx)
  add_left := hadd
  smul_left x y a := by simpa using hsmul a x y
  definite x hx := by
    by_contra hn
    exact (hpos x hn).ne' hx

theorem actual_only_three_source_axioms_derive_cauchy_schwarz (b : F → F → ℝ)
    (hsym : ∀ x y, b x y=b y x)
    (hadd : ∀ x y z, b (x+y) z=b x z+b y z)
    (hsmul : ∀ a x y, b (a • x) y=a*b x y)
    (hpos : ∀ x, x≠0 → 0<b x x) (x y : F) :
    |b x y|≤Real.sqrt (b x x)*Real.sqrt (b y y) := by
  letI core : InnerProductSpace.Core ℝ F := sourceCore b hsym hadd hsmul hpos
  letI : NormedAddCommGroup F := InnerProductSpace.Core.toNormedAddCommGroup
  letI : InnerProductSpace ℝ F := InnerProductSpace.ofCore inferInstance
  have hn (v : F) : ‖v‖=Real.sqrt (b v v) := rfl
  simpa only [hn] using actual_source_minimum_nonnegativity_derives_cauchy_schwarz x y

theorem actual_only_three_source_axioms_give_the_printed_parabola_minimum (b : F → F → ℝ)
    (hsym : ∀ x y, b x y=b y x)
    (hadd : ∀ x y z, b (x+y) z=b x z+b y z)
    (hsmul : ∀ a x y, b (a • x) y=a*b x y)
    (hpos : ∀ x, x≠0 → 0<b x x) (x y : F) (hy : y≠0) :
    let length := fun v => Real.sqrt (b v v)
    length (x-(b x y/length y^2) • y)^2=length x^2-b x y^2/length y^2 ∧
    0≤length x^2-b x y^2/length y^2 ∧
    ∀ t : ℝ, length x^2-b x y^2/length y^2≤length (x-t • y)^2 := by
  letI core : InnerProductSpace.Core ℝ F := sourceCore b hsym hadd hsmul hpos
  letI : NormedAddCommGroup F := InnerProductSpace.Core.toNormedAddCommGroup
  letI : InnerProductSpace ℝ F := InnerProductSpace.ofCore inferInstance
  have hn (v : F) : ‖v‖=Real.sqrt (b v v) := rfl
  simpa only [hn] using actual_nonzero_y_parabola_attains_the_printed_global_minimum x y hy

theorem actual_only_three_source_axioms_force_the_printed_equality_case (b : F → F → ℝ)
    (hsym : ∀ x y, b x y=b y x)
    (hadd : ∀ x y z, b (x+y) z=b x z+b y z)
    (hsmul : ∀ a x y, b (a • x) y=a*b x y)
    (hpos : ∀ x, x≠0 → 0<b x x) (x y : F) (hy : y≠0)
    (he : |b x y|=Real.sqrt (b x x)*Real.sqrt (b y y)) :
    x=(b x y/(Real.sqrt (b y y))^2) • y := by
  letI core : InnerProductSpace.Core ℝ F := sourceCore b hsym hadd hsmul hpos
  letI : NormedAddCommGroup F := InnerProductSpace.Core.toNormedAddCommGroup
  letI : InnerProductSpace ℝ F := InnerProductSpace.ofCore inferInstance
  have hn (v : F) : ‖v‖=Real.sqrt (b v v) := rfl
  have hh : |⟪x,y⟫|=‖x‖*‖y‖ := by simpa only [hn] using he
  simpa only [hn] using actual_cauchy_schwarz_equality_forces_the_printed_scalar x y hy hh
end OnlySourceAxioms

end SafeLearning.CompleteFoundationsLiteralInnerProduct28
