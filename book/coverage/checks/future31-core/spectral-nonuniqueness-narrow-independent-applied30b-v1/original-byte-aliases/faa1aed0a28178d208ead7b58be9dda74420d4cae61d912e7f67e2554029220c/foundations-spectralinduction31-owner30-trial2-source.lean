import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators Matrix

namespace SafeLearning.CompleteFoundationsSpectralInductionSketch31

section FiniteReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

/-- Only the symmetric operator and nontrivial finite-dimensional space are assumed.
The initial eigenvector comes from the attained Rayleigh quotient, not a basis premise. -/
theorem actual_real_unit_eigenvector_exists
    [Nontrivial E] (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) :
    ∃ a : ℝ, ∃ q : E, ‖q‖ = 1 ∧ T q = a • q := by
  let a : ℝ := ⨆ x : {x : E // x ≠ 0},
    RCLike.re (inner ℝ (T x) x) / ‖(x : E)‖ ^ 2
  have ha : Module.End.HasEigenvalue T a := hT.hasEigenvalue_iSup_of_finiteDimensional
  obtain ⟨v, hv, hv0⟩ := ha.exists_hasEigenvector
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
  have he : T v = a • v := Module.End.mem_eigenspace_iff.mp hv
  refine ⟨a, ‖v‖⁻¹ • v, ?_, ?_⟩
  · simp [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v),
      inv_mul_cancel₀ hn]
  · simp only [map_smul, he, smul_smul]
    congr 1
    ring

/-- The source's q-perp is the actual orthogonal complement of the span of q. -/
theorem actual_unit_eigenvector_orthogonal_complement_is_invariant
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) (q : E) (a : ℝ)
    (hq : T q = a • q) :
    ∀ x ∈ (ℝ ∙ q)ᗮ, T x ∈ (ℝ ∙ q)ᗮ := by
  intro x hx
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hx ⊢
  rw [← hT q x, hq]
  simp [inner_smul_left, hx]

theorem actual_restriction_to_the_orthogonal_complement_is_symmetric
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) (q : E) (a : ℝ)
    (hq : T q = a • q) :
    (T.restrict
      (actual_unit_eigenvector_orthogonal_complement_is_invariant T hT q a hq)).IsSymmetric :=
  hT.restrict_invariant
    (actual_unit_eigenvector_orthogonal_complement_is_invariant T hT q a hq)

theorem actual_unit_vector_complement_has_one_lower_dimension
    (m : ℕ) (hE : Module.finrank ℝ E = m + 1) (q : E) (hq : ‖q‖ = 1) :
    Module.finrank ℝ (ℝ ∙ q)ᗮ = m := by
  letI : Fact (Module.finrank ℝ E = m + 1) := ⟨hE⟩
  have hq0 : q ≠ 0 := by
    intro h
    simpa [h] using hq
  exact Submodule.finrank_orthogonal_span_singleton hq0

/-- An arbitrary basis inside one eigenspace consists of eigenvectors, including
repeated eigenvalues. No pairwise distinct eigenvalue premise is used. -/
theorem actual_every_orthonormal_eigenspace_basis_is_an_eigenvector_family
    {ι : Type*} [Fintype ι] (T : E →ₗ[ℝ] E) (a : ℝ)
    (b : OrthonormalBasis ι ℝ (Module.End.eigenspace T a)) :
    ∀ i, T (b i : E) = a • (b i : E) := by
  intro i
  exact Module.End.mem_eigenspace_iff.mp (b i).property

end FiniteReal

/-- Actual dimension induction, with the empty-space base and a one-smaller
symmetric restriction at each successor. The returned complete basis is constructed
from the first unit eigenvector and the recursively obtained complement basis. -/
theorem actual_finite_dimensional_dimension_induction
    (m : ℕ) : ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E], ∀ (T : E →ₗ[ℝ] E), T.IsSymmetric →
      Module.finrank ℝ E = m →
      ∃ b : OrthonormalBasis (Fin m) ℝ E, ∃ a : Fin m → ℝ,
        ∀ i, T (b i) = a i • b i := by
  induction m with
  | zero =>
      intro E _ _ _ T hT hE
      let b : OrthonormalBasis (Fin 0) ℝ E :=
        (stdOrthonormalBasis ℝ E).reindex (finCongr hE)
      refine ⟨b, fun i => Fin.elim0 i, ?_⟩
      intro i
      exact Fin.elim0 i
  | succ m ih =>
      intro E _ _ _ T hT hE
      letI : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hE
      obtain ⟨a, q, hqnorm, hqeig⟩ := actual_real_unit_eigenvector_exists T hT
      let P : Submodule ℝ E := (ℝ ∙ q)ᗮ
      have hi : ∀ x ∈ P, T x ∈ P :=
        actual_unit_eigenvector_orthogonal_complement_is_invariant T hT q a hqeig
      have hs : (T.restrict hi).IsSymmetric := hT.restrict_invariant hi
      have hp : Module.finrank ℝ P = m :=
        actual_unit_vector_complement_has_one_lower_dimension m hE q hqnorm
      obtain ⟨b, c, heig⟩ := ih P (T.restrict hi) hs hp
      let v : Fin (m + 1) → E := Matrix.vecCons q (fun i => (b i : E))
      have ho : Orthonormal ℝ v := by
        apply orthonormal_vecCons_iff.mpr
        refine ⟨hqnorm, ?_, ?_⟩
        · intro i
          exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (b i).property
        · constructor
          · intro i
            exact b.orthonormal.norm_eq_one i
          · intro i j hij
            exact b.orthonormal.inner_eq_zero hij
      have hcard : Fintype.card (Fin (m + 1)) = Module.finrank ℝ E := by
        simpa using hE.symm
      have hspan := ho.linearIndependent.span_eq_top_of_card_eq_finrank' hcard
      let B : OrthonormalBasis (Fin (m + 1)) ℝ E := OrthonormalBasis.mk ho hspan.ge
      refine ⟨B, Matrix.vecCons a c, ?_⟩
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [B, v] using hqeig
      · have hh := congrArg (fun x : P => (x : E)) (heig j)
        simpa [B, v, LinearMap.restrict_apply] using hh

section Matrices
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Changing every eigenvector's sign preserves the orthogonal spectral data. -/
theorem actual_global_sign_change_preserves_orthogonal_diagonalization
    (A Q : Matrix n n ℝ) (d : n → ℝ)
    (hQ : Q.transpose * Q = 1)
    (hA : A = Q * Matrix.diagonal d * Q.transpose) :
    (-Q).transpose * (-Q) = 1 ∧
      A = (-Q) * Matrix.diagonal d * (-Q).transpose := by
  constructor
  · simpa using hQ
  · simpa using hA

/-- Nonempty dimension gives genuinely distinct spectral eigenvector matrices. -/
theorem actual_nonempty_orthogonal_matrix_differs_from_its_negative
    [Nonempty n] (Q : Matrix n n ℝ) (hQ : Q.transpose * Q = 1) : Q ≠ -Q := by
  intro he
  have hz : Q = 0 := by
    ext i j
    have hh := congrArg (fun M : Matrix n n ℝ => M i j) he
    change Q i j = -(Q i j) at hh
    change Q i j = 0
    linarith
  let i : n := Classical.arbitrary n
  have hh := congrArg (fun M : Matrix n n ℝ => M i i) hQ
  norm_num [hz] at hh

/-- The dimension-zero base has exactly one matrix; no nonuniqueness is inferred there. -/
theorem actual_empty_dimensional_matrix_is_unique
    (A B : Matrix (Fin 0) (Fin 0) ℝ) : A = B := Subsingleton.elim _ _

end Matrices
end SafeLearning.CompleteFoundationsSpectralInductionSketch31

namespace SafeLearning.CompleteFoundationsSpectralInductionSketch31

/-- The recursively constructed abstract basis is bound to the actual real matrix
acting in Euclidean coordinates, rather than the coordinate supremum norm. -/
theorem actual_real_symmetric_matrix_basis_from_dimension_induction
    (m : ℕ) (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.IsHermitian) :
    ∃ b : OrthonormalBasis (Fin m) ℝ (EuclideanSpace ℝ (Fin m)),
      ∃ a : Fin m → ℝ, ∀ i,
        A *ᵥ (b i : Fin m → ℝ) = a i • (b i : Fin m → ℝ) := by
  obtain ⟨b, a, hb⟩ := actual_finite_dimensional_dimension_induction m
    (EuclideanSpace ℝ (Fin m)) A.toEuclideanLin
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA) (by simp)
  refine ⟨b, a, ?_⟩
  intro i
  simpa only [Matrix.toLpLin_apply, WithLp.ofLp_smul] using
    congrArg (fun x : EuclideanSpace ℝ (Fin m) => (x : Fin m → ℝ)) (hb i)

end SafeLearning.CompleteFoundationsSpectralInductionSketch31
