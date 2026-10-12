import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Set
open scoped BigOperators NNReal ENNReal Matrix RealInnerProductSpace

namespace SafeLearning.CompleteFoundationsInducedNormProductCertificates30

section GeneralInducedNorm
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem actual_induced_norm_bounds_every_input (A : E →L[ℝ] F) (x : E) :
    ‖A x‖ ≤ ‖A‖ * ‖x‖ := A.le_opNorm x

theorem actual_induced_norm_is_a_lipschitz_constant (A : E →L[ℝ] F) :
    LipschitzWith ‖A‖₊ A := A.lipschitzWith

theorem actual_nonnegative_bound_constant_iff_opnorm_le (A : E →L[ℝ] F)
    (C : ℝ) (hC : 0 ≤ C) : (∀ x : E, ‖A x‖ ≤ C * ‖x‖) ↔ ‖A‖ ≤ C := by
  exact (A.opNorm_le_iff hC).symm

variable [FiniteDimensional ℝ E] [Nontrivial E]

theorem actual_induced_norm_has_a_unit_sphere_maximizer (A : E →L[ℝ] F) :
    ∃ x : E, ‖x‖ = 1 ∧ ‖A x‖ = ‖A‖ := by
  have hne : (Metric.sphere (0 : E) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  obtain ⟨x, hx, hmax⟩ := (isCompact_sphere (0 : E) 1).exists_isMaxOn hne
    A.continuous.norm.continuousOn
  have hg : IsGreatest ((fun y : E => ‖A y‖) '' Metric.sphere 0 1) ‖A x‖ := by
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hmax hy
  have heq : ‖A x‖ = ‖A‖ := hg.csSup_eq.symm.trans A.sSup_sphere_eq_norm
  exact ⟨x, mem_sphere_zero_iff_norm.mp hx, heq⟩

theorem actual_induced_norm_is_greatest_unit_sphere_value (A : E →L[ℝ] F) :
    IsGreatest ((fun x : E => ‖A x‖) '' {x | ‖x‖ = 1}) ‖A‖ := by
  obtain ⟨x, hx, heq⟩ := actual_induced_norm_has_a_unit_sphere_maximizer A
  refine ⟨⟨x, hx, heq⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  change ‖y‖ = 1 at hy
  simpa only [hy, mul_one] using A.le_opNorm y

theorem actual_induced_norm_is_greatest_nonzero_ratio (A : E →L[ℝ] F) :
    IsGreatest ((fun x : E => ‖A x‖ / ‖x‖) '' {x | x ≠ 0}) ‖A‖ := by
  obtain ⟨x, hx, heq⟩ := actual_induced_norm_has_a_unit_sphere_maximizer A
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  refine ⟨⟨x, hx0, by change ‖A x‖ / ‖x‖ = ‖A‖; rw [hx, heq, div_one]⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact (div_le_iff₀ (norm_pos_iff.mpr hy)).mpr (A.le_opNorm y)

theorem actual_induced_norm_is_the_least_real_bound_constant (A : E →L[ℝ] F) :
    IsLeast {C : ℝ | ∀ x : E, ‖A x‖ ≤ C * ‖x‖} ‖A‖ := by
  refine ⟨A.le_opNorm, ?_⟩
  intro C hC
  obtain ⟨x, hx, heq⟩ := actual_induced_norm_has_a_unit_sphere_maximizer A
  simpa only [hx, heq, mul_one] using hC x

end GeneralInducedNorm

section MatrixBridge
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  {a b : ℝ≥0∞} [Fact (1 ≤ a)] [Fact (1 ≤ b)]

def sourceMatrixMap (a b : ℝ≥0∞) [Fact (1 ≤ a)] [Fact (1 ≤ b)]
    (A : Matrix m n ℝ) : PiLp a (fun _ : n => ℝ) →L[ℝ] PiLp b (fun _ : m => ℝ) :=
  (Matrix.toLpLin a b A).toContinuousLinearMap

theorem actual_matrix_map_is_the_literal_matrix_vector_product (A : Matrix m n ℝ)
    (x : n → ℝ) :
    sourceMatrixMap a b A (WithLp.toLp a x) = WithLp.toLp b (A *ᵥ x) := rfl

theorem actual_matrix_induced_norm_maxima_and_least_constant [Nonempty n]
    (A : Matrix m n ℝ) :
    IsGreatest ((fun x : PiLp a (fun _ : n => ℝ) =>
      ‖sourceMatrixMap a b A x‖ / ‖x‖) '' {x | x ≠ 0}) ‖sourceMatrixMap a b A‖ ∧
    IsGreatest ((fun x : PiLp a (fun _ : n => ℝ) =>
      ‖sourceMatrixMap a b A x‖) '' {x | ‖x‖ = 1}) ‖sourceMatrixMap a b A‖ ∧
    IsLeast {C : ℝ | ∀ x : PiLp a (fun _ : n => ℝ),
      ‖sourceMatrixMap a b A x‖ ≤ C * ‖x‖} ‖sourceMatrixMap a b A‖ :=
  ⟨actual_induced_norm_is_greatest_nonzero_ratio _,
   actual_induced_norm_is_greatest_unit_sphere_value _,
   actual_induced_norm_is_the_least_real_bound_constant _⟩
end MatrixBridge

section ProductsAndCompatibility
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem actual_compatible_induced_norms_are_submultiplicative
    (A : F →L[ℝ] G) (B : E →L[ℝ] F) : ‖A.comp B‖ ≤ ‖A‖ * ‖B‖ :=
  ContinuousLinearMap.opNorm_comp_le A B

theorem actual_induced_norm_power_bound (A : E →L[ℝ] E) (k : ℕ) :
    ‖A ^ k‖ ≤ ‖A‖ ^ k := by
  cases subsingleton_or_nontrivial E with
  | inl h =>
    letI : Subsingleton E := h
    have hz : A ^ k = 0 := Subsingleton.elim _ _
    rw [hz, norm_zero]
    exact pow_nonneg (norm_nonneg A) k
  | inr h =>
    letI : Nontrivial E := h
    exact norm_pow_le A k

theorem actual_dual_norm_compatible_bilinear_bound
    (ℓ : F →L[ℝ] ℝ) (A : E →L[ℝ] F) (y : E) :
    |ℓ (A y)| ≤ ‖ℓ‖ * ‖A‖ * ‖y‖ := by
  calc
    |ℓ (A y)| = ‖ℓ (A y)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖ℓ‖ * ‖A y‖ := ℓ.le_opNorm _
    _ ≤ ‖ℓ‖ * (‖A‖ * ‖y‖) := mul_le_mul_of_nonneg_left (A.le_opNorm _) (norm_nonneg _)
    _ = ‖ℓ‖ * ‖A‖ * ‖y‖ := by ring

end ProductsAndCompatibility

section EuclideanCompatibility
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
theorem actual_euclidean_pairing_uses_the_spectral_operator_norm
    (x : F) (A : E →L[ℝ] F) (y : E) :
    |⟪x, A y⟫| ≤ ‖x‖ * ‖A‖ * ‖y‖ := by
  simpa only [innerSL_apply_apply, innerSL_apply_norm] using
    actual_dual_norm_compatible_bilinear_bound (innerSL ℝ x) A y
end EuclideanCompatibility

section RectangularFrobenius
variable {m n l : Type*} [Fintype m] [Fintype n] [Fintype l]
open scoped Matrix.Norms.Frobenius

theorem actual_rectangular_frobenius_submultiplicativity
    (A : Matrix l m ℝ) (B : Matrix m n ℝ) : ‖A * B‖ ≤ ‖A‖ * ‖B‖ :=
  Matrix.frobenius_norm_mul A B

theorem actual_frobenius_positive_integer_power_bound [DecidableEq n]
    (A : Matrix n n ℝ) (k : ℕ) : ‖A ^ (k + 1)‖ ≤ ‖A‖ ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      ‖A ^ (k + 1 + 1)‖ = ‖A ^ (k + 1) * A‖ := by rw [pow_succ]
      _ ≤ ‖A ^ (k + 1)‖ * ‖A‖ := Matrix.frobenius_norm_mul _ _
      _ ≤ ‖A‖ ^ (k + 1) * ‖A‖ := mul_le_mul_of_nonneg_right ih (norm_nonneg _)
      _ = ‖A‖ ^ (k + 1 + 1) := (pow_succ _ _).symm

theorem actual_frobenius_zero_power_cannot_use_the_induced_norm_bound :
    1 < ‖(0 : Matrix (Fin 2) (Fin 2) ℝ) ^ 0‖ := by
  have hn : ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ = Real.sqrt 2 := by
    rw [Matrix.frobenius_norm_def]
    norm_num [Fin.sum_univ_succ, Real.sqrt_eq_rpow]
  rw [pow_zero, hn]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
end RectangularFrobenius

section GenuineLayeredNetworks
variable (E : ℕ → Type*) [∀ k, NormedAddCommGroup (E k)] [∀ k, NormedSpace ℝ (E k)]

def sourceNetwork (W : ∀ k, E k →L[ℝ] E (k + 1)) (φ : ∀ k, E k → E k) :
    (k : ℕ) → E 0 → E k
  | 0 => id
  | k + 1 => fun x => φ (k + 1) (W k (sourceNetwork W φ k x))

theorem actual_layered_network_lipschitz_product
    (W : ∀ k, E k →L[ℝ] E (k + 1)) (φ : ∀ k, E k → E k)
    (hφ : ∀ k, LipschitzWith 1 (φ k)) :
    ∀ k, LipschitzWith (∏ i ∈ Finset.range k, ‖W i‖₊) (sourceNetwork E W φ k) := by
  intro k
  induction k with
  | zero => simpa only [sourceNetwork, Finset.prod_range_zero] using LipschitzWith.id
  | succ k ih =>
    have h := (hφ (k + 1)).comp ((W k).lipschitzWith.comp ih)
    simpa only [sourceNetwork, Finset.prod_range_succ, one_mul, mul_comm, Function.comp_def] using h
end GenuineLayeredNetworks

end SafeLearning.CompleteFoundationsInducedNormProductCertificates30

namespace SafeLearning.CompleteFoundationsInducedNormProductCertificates30
section ArbitraryFiniteDimensionalInputAndOutputNorms
variable {E F m n : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E]
  [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def sourceArbitraryNormMatrixMap (bE : Module.Basis n ℝ E) (bF : Module.Basis m ℝ F)
    (A : Matrix m n ℝ) : E →L[ℝ] F :=
  (Matrix.toLin bE bF A).toContinuousLinearMap

theorem actual_arbitrary_norm_matrix_map_has_exact_literal_coordinates
    (bE : Module.Basis n ℝ E) (bF : Module.Basis m ℝ F) (A : Matrix m n ℝ) (x : E) :
    bF.equivFun (sourceArbitraryNormMatrixMap bE bF A x) = A *ᵥ bE.equivFun x := by
  simpa only [sourceArbitraryNormMatrixMap, LinearMap.coe_toContinuousLinearMap', Module.Basis.equivFun_apply] using
    Matrix.repr_toLin bE bF A x

theorem actual_arbitrary_norm_matrix_maxima_and_smallest_constant [Nontrivial E]
    (bE : Module.Basis n ℝ E) (bF : Module.Basis m ℝ F) (A : Matrix m n ℝ) :
    IsGreatest ((fun x : E => ‖sourceArbitraryNormMatrixMap bE bF A x‖ / ‖x‖) ''
      {x | x ≠ 0}) ‖sourceArbitraryNormMatrixMap bE bF A‖ ∧
    IsGreatest ((fun x : E => ‖sourceArbitraryNormMatrixMap bE bF A x‖) ''
      {x | ‖x‖ = 1}) ‖sourceArbitraryNormMatrixMap bE bF A‖ ∧
    IsLeast {C : ℝ | ∀ x : E, ‖sourceArbitraryNormMatrixMap bE bF A x‖ ≤ C * ‖x‖}
      ‖sourceArbitraryNormMatrixMap bE bF A‖ :=
  ⟨actual_induced_norm_is_greatest_nonzero_ratio _,
   actual_induced_norm_is_greatest_unit_sphere_value _,
   actual_induced_norm_is_the_least_real_bound_constant _⟩
end ArbitraryFiniteDimensionalInputAndOutputNorms
end SafeLearning.CompleteFoundationsInducedNormProductCertificates30
