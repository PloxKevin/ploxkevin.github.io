import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric
open scoped Topology BigOperators RealInnerProductSpace Matrix

namespace SafeLearning.CompleteFoundationsCompactnessWholeUnits30

section ActualCompactness
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem actual_bounded_definition_by_a_ball (A : Set E) :
    Bornology.IsBounded A ↔ ∃ R : ℝ, A ⊆ Metric.ball 0 R :=
  isBounded_iff_subset_ball 0

theorem actual_sequential_definition_of_compactness (A : Set E) :
    IsCompact A ↔ ∀ x : ℕ → E, (∀ n, x n ∈ A) →
      ∃ a ∈ A, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) :=
  isCompact_iff_isSeqCompact

theorem actual_heine_borel_closed_and_bounded (A : Set E) :
    IsCompact A ↔ IsClosed A ∧ Bornology.IsBounded A :=
  isCompact_iff_isClosed_bounded

theorem actual_every_bounded_sequence_has_a_convergent_subsequence
    (x : ℕ → E) (R : ℝ) (hx : ∀ n, ‖x n‖ ≤ R) :
    ∃ a : E, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) := by
  obtain ⟨a, _, φ, hφ, hlim⟩ :=
    tendsto_subseq_of_bounded (x:=x) (s:=Metric.closedBall (0 : E) R) isBounded_closedBall
      (fun n => by simpa [Metric.mem_closedBall, dist_zero_right] using hx n)
  exact ⟨a, φ, hφ, hlim⟩

theorem actual_compact_set_has_a_finite_cover_by_any_positive_radius
    (A : Set E) (hA : IsCompact A) (τ : ℝ) (hτ : 0 < τ) :
    ∃ centers ⊆ A, centers.Finite ∧ A ⊆ ⋃ z ∈ centers, Metric.ball z τ :=
  hA.finite_cover_balls hτ

theorem actual_closedness_keeps_a_subsequence_limit_in_the_set
    (A : Set E) (hA : IsClosed A) (x : ℕ → E) (a : E)
    (hx : ∀ n, x n ∈ A) (hlim : Tendsto x atTop (𝓝 a)) : a ∈ A :=
  hA.mem_of_tendsto hlim (Eventually.of_forall hx)

theorem actual_infinite_terms_in_a_union_force_one_infinite_half
    (x : ℕ → E) (A B : Set E) (h : ∃ᶠ n in atTop, x n ∈ A ∪ B) :
    (∃ᶠ n in atTop, x n ∈ A) ∨ (∃ᶠ n in atTop, x n ∈ B) := by
  exact Filter.frequently_or_distrib.mp (by simpa only [Set.mem_union] using h)

theorem actual_closed_balls_are_compact (x : E) (R : ℝ) :
    IsCompact (Metric.closedBall x R) := isCompact_closedBall x R

theorem actual_positive_dimensional_real_space_is_not_compact [Nontrivial E] :
    ¬IsCompact (univ : Set E) :=
  fun h => NormedSpace.unbounded_univ ℝ E h.isBounded

end ActualCompactness

theorem actual_euclidean_unit_cube_is_compact {I : Type*} [Fintype I] :
    IsCompact {x : EuclideanSpace ℝ I | ∀ i, 0 ≤ x i ∧ x i ≤ 1} := by
  have h : IsCompact ((PiLp.homeomorph 2 (fun _ : I => ℝ)) ⁻¹'
      Icc (0 : I → ℝ) 1) :=
    (PiLp.homeomorph 2 (fun _ : I => ℝ)).isCompact_preimage.mpr isCompact_Icc
  change IsCompact {x : EuclideanSpace ℝ I | (∀ i, 0 ≤ x i) ∧ (∀ i, x i ≤ 1)} at h
  convert h using 1
  ext x
  simp only [Set.mem_ofPred_eq, forall_and]


theorem actual_half_open_interval_is_not_compact : ¬IsCompact (Ioc (0 : ℝ) 1) := by
  intro h
  have hn := isClosed_Ioc_iff.mp h.isClosed
  norm_num at hn

section PrimitivePositiveHomogeneousQuadratic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem actual_positive_continuous_quadratic_derives_a_uniform_coercivity_bound
    [Nontrivial E] (Q : E → ℝ) (hQ : Continuous Q)
    (hscale : ∀ (t : ℝ) (x : E), Q (t • x) = t^2 * Q x)
    (hpositive : ∀ x : E, x ≠ 0 → 0 < Q x) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : E, c*‖x‖^2 ≤ Q x := by
  have hne : (Metric.sphere (0 : E) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  obtain ⟨y, hy, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn hne hQ.continuousOn
  have hynorm : ‖y‖=1 := mem_sphere_zero_iff_norm.mp hy
  have hyzero : y ≠ 0 := by intro he; simp [he] at hynorm
  refine ⟨Q y, hpositive y hyzero, ?_⟩
  intro x
  by_cases hx : x=0
  · subst x
    have hzero := hscale 0 (0 : E)
    simpa using le_of_eq hzero.symm
  · have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hunit : ‖(‖x‖⁻¹ : ℝ) • x‖=1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hnorm.le)]
      exact inv_mul_cancel₀ (ne_of_gt hnorm)
    have hm := hmin (mem_sphere_zero_iff_norm.mpr hunit)
    change Q y ≤ Q ((‖x‖⁻¹ : ℝ) • x) at hm
    rw [hscale] at hm
    have hh := mul_le_mul_of_nonneg_right hm (sq_nonneg ‖x‖)
    convert hh using 1 <;> field_simp [ne_of_gt hnorm]

theorem actual_positive_continuous_quadratic_sublevels_are_compact
    (Q : E → ℝ) (hQ : Continuous Q)
    (hscale : ∀ (t : ℝ) (x : E), Q (t • x) = t^2 * Q x)
    (hpositive : ∀ x : E, x ≠ 0 → 0 < Q x) (r : ℝ) :
    IsCompact {x : E | Q x ≤ r} := by
  cases subsingleton_or_nontrivial E with
  | inl hs =>
    letI : Subsingleton E := hs
    exact (Set.toFinite _).isCompact
  | inr hn =>
    letI : Nontrivial E := hn
    obtain ⟨c, hc, hbound⟩ :=
      actual_positive_continuous_quadratic_derives_a_uniform_coercivity_bound Q hQ hscale hpositive
    apply isCompact_of_isClosed_isBounded (isClosed_le hQ continuous_const)
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨|r|/c+1, ?_⟩
    intro x hx
    have hsq : ‖x‖^2 ≤ |r|/c := by
      apply (le_div_iff₀ hc).mpr
      have hxr : Q x ≤ r := hx
      nlinarith [hbound x, le_abs_self r]
    have hnonnegative : 0 ≤ |r|/c := div_nonneg (abs_nonneg _) hc.le
    nlinarith [norm_nonneg x, sq_nonneg (‖x‖-(|r|/c+1))]
end PrimitivePositiveHomogeneousQuadratic

section ActualMatrixEllipsoids
variable {I : Type*} [Fintype I] [DecidableEq I]

def sourceMatrixAction (P : Matrix I I ℝ) : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I :=
  (Matrix.toLpLin 2 2 P).toContinuousLinearMap

def sourceEllipsoidQuadratic (P : Matrix I I ℝ) (x : EuclideanSpace ℝ I) : ℝ :=
  ⟪x, sourceMatrixAction P x⟫

theorem actual_matrix_quadratic_is_the_literal_coordinate_formula
    (P : Matrix I I ℝ) (x : EuclideanSpace ℝ I) :
    sourceEllipsoidQuadratic P x = dotProduct (fun i => x i) (P *ᵥ (fun i => x i)) := by
  simp only [sourceEllipsoidQuadratic, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  change (P *ᵥ (fun i => x i)) ⬝ᵥ (fun i => x i) =
    (fun i => x i) ⬝ᵥ (P *ᵥ (fun i => x i))
  exact dotProduct_comm _ _

theorem actual_positive_definite_matrix_ellipsoids_are_compact
    (P : Matrix I I ℝ) (hP : P.PosDef) (r : ℝ) :
    IsCompact {x : EuclideanSpace ℝ I | sourceEllipsoidQuadratic P x ≤ r} := by
  apply actual_positive_continuous_quadratic_sublevels_are_compact
  · exact continuous_id.inner (sourceMatrixAction P).continuous
  · intro t x
    simp only [sourceEllipsoidQuadratic, map_smul, real_inner_smul_left, real_inner_smul_right]
    ring
  · intro x hx
    have hvec : (fun i => x i) ≠ 0 := by
      intro h
      apply hx
      ext i
      exact congrFun h i
    rw [actual_matrix_quadratic_is_the_literal_coordinate_formula]
    simpa only [star_trivial] using hP.dotProduct_mulVec_pos hvec
end ActualMatrixEllipsoids

def sourceHyperbolicSublevel : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | (x 0)^2-(x 1)^2 ≤ 1}

theorem actual_hyperbolic_sublevel_is_closed : IsClosed sourceHyperbolicSublevel := by
  exact isClosed_le (((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).pow 2).sub
    ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).pow 2)) continuous_const

theorem actual_hyperbolic_sublevel_is_unbounded :
    ¬Bornology.IsBounded sourceHyperbolicSublevel := by
  intro h
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp h
  let x : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![|R|+1, |R|+1]
  have hx : x ∈ sourceHyperbolicSublevel := by norm_num [x, sourceHyperbolicSublevel]
  have hcoord := PiLp.norm_apply_le x 0
  have hr := hR x hx
  have he : ‖x 0‖=|R|+1 := by simp [x, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < |R|+1)]
  rw [he] at hcoord
  linarith [le_abs_self R]

theorem actual_hyperbolic_sublevel_is_not_compact : ¬IsCompact sourceHyperbolicSublevel :=
  fun h => actual_hyperbolic_sublevel_is_unbounded h.isBounded

def sourceSaturatingValue (x : ℝ) : ℝ := x^2/(1+x^2)

theorem actual_saturating_value_is_positive_away_from_zero (x : ℝ) (hx : x ≠ 0) :
    0 < sourceSaturatingValue x :=
  div_pos (sq_pos_of_ne_zero hx) (by nlinarith [sq_nonneg x])

theorem actual_saturating_value_is_strictly_below_one (x : ℝ) :
    sourceSaturatingValue x < 1 := by
  apply (div_lt_one (show 0<1+x^2 by nlinarith [sq_nonneg x])).mpr
  linarith

theorem actual_saturating_half_sublevel_is_the_closed_unit_interval :
    {x : ℝ | sourceSaturatingValue x ≤ (1/2:ℝ)} = Icc (-1 : ℝ) 1 := by
  ext x
  have hd : 0<1+x^2 := by nlinarith [sq_nonneg x]
  change x^2/(1+x^2) ≤ (1/2:ℝ) ↔ -1≤x ∧ x≤1
  rw [div_le_iff₀ hd]
  constructor
  · intro h
    constructor <;> nlinarith [sq_nonneg (x-1),sq_nonneg (x+1)]
  · rintro ⟨ha,hb⟩
    nlinarith [mul_nonneg (by linarith : 0≤x+1) (by linarith : 0≤1-x)]

theorem actual_saturating_half_sublevel_is_compact :
    IsCompact {x : ℝ | sourceSaturatingValue x ≤ (1/2:ℝ)} := by
  rw [actual_saturating_half_sublevel_is_the_closed_unit_interval]
  exact isCompact_Icc

theorem actual_saturating_sublevel_at_or_above_one_is_all_real (c : ℝ) (hc : 1≤c) :
    {x : ℝ | sourceSaturatingValue x ≤ c}=univ := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
  exact (actual_saturating_value_is_strictly_below_one x).le.trans hc

theorem actual_saturating_sublevel_at_or_above_one_is_not_compact (c : ℝ) (hc : 1≤c) :
    ¬IsCompact {x : ℝ | sourceSaturatingValue x ≤ c} := by
  rw [actual_saturating_sublevel_at_or_above_one_is_all_real c hc]
  exact actual_positive_dimensional_real_space_is_not_compact

end SafeLearning.CompleteFoundationsCompactnessWholeUnits30

namespace SafeLearning.CompleteFoundationsCompactnessWholeUnits30

section ActualSmallestEigenvalue
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

theorem actual_positive_definite_matrix_smallest_eigenvalue_bound
    (P : Matrix I I ℝ) (hP : P.PosDef) :
    ∃ muMin : ℝ, 0 < muMin ∧
      Module.End.HasEigenvalue (sourceMatrixAction P).toLinearMap muMin ∧
      (∀ μ : ℝ, Module.End.HasEigenvalue (sourceMatrixAction P).toLinearMap μ → muMin ≤ μ) ∧
      ∀ x : EuclideanSpace ℝ I, muMin * ‖x‖^2 ≤ sourceEllipsoidQuadratic P x := by
  let T := sourceMatrixAction P
  let Q := sourceEllipsoidQuadratic P
  have hsym : T.toLinearMap.IsSymmetric := by
    change P.toEuclideanLin.IsSymmetric
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr hP.isHermitian
  have hQ : Continuous Q := continuous_id.inner T.continuous
  have hscale : ∀ (t : ℝ) (x : EuclideanSpace ℝ I), Q (t • x) = t^2 * Q x := by
    intro t x
    simp only [Q, sourceEllipsoidQuadratic, map_smul, real_inner_smul_left, real_inner_smul_right]
    ring
  have hpositive : ∀ x : EuclideanSpace ℝ I, x ≠ 0 → 0 < Q x := by
    intro x hx
    have hvec : (fun i => x i) ≠ 0 := by
      intro h
      apply hx
      ext i
      exact congrFun h i
    change 0 < sourceEllipsoidQuadratic P x
    rw [actual_matrix_quadratic_is_the_literal_coordinate_formula]
    simpa only [star_trivial] using hP.dotProduct_mulVec_pos hvec
  have hne : (Metric.sphere (0 : EuclideanSpace ℝ I) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  obtain ⟨y, hy, hmin⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ I) 1).exists_isMinOn hne hQ.continuousOn
  have hynorm : ‖y‖ = 1 := mem_sphere_zero_iff_norm.mp hy
  have hyzero : y ≠ 0 := by intro he; simp [he] at hynorm
  have heq : T.reApplyInnerSelf = Q := by
    funext x
    simp only [ContinuousLinearMap.reApplyInnerSelf_apply, RCLike.re_to_real, Q,
      sourceEllipsoidQuadratic, T, real_inner_comm]
  have hmin' : IsMinOn T.reApplyInnerSelf (Metric.sphere 0 ‖y‖) y := by
    simpa only [heq, hynorm] using hmin
  have heig := hsym.isSelfAdjoint.hasEigenvector_of_isLocalExtrOn hyzero (Or.inl hmin'.isLocalMinOn)
  have hquot : T.rayleighQuotient y = Q y := by
    simp only [ContinuousLinearMap.rayleighQuotient, heq, hynorm, one_pow, div_one]
  rw [hquot] at heig
  have hbound : ∀ x : EuclideanSpace ℝ I, Q y * ‖x‖^2 ≤ Q x := by
    intro x
    by_cases hx : x = 0
    · subst x
      have hzero := hscale 0 (0 : EuclideanSpace ℝ I)
      simpa using le_of_eq hzero.symm
    · have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hunit : ‖(‖x‖⁻¹ : ℝ) • x‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hnorm.le)]
        exact inv_mul_cancel₀ (ne_of_gt hnorm)
      have hm := hmin (mem_sphere_zero_iff_norm.mpr hunit)
      change Q y ≤ Q ((‖x‖⁻¹ : ℝ) • x) at hm
      rw [hscale] at hm
      have hh := mul_le_mul_of_nonneg_right hm (sq_nonneg ‖x‖)
      convert hh using 1 <;> field_simp [ne_of_gt hnorm]
  refine ⟨Q y, hpositive y hyzero, Module.End.hasEigenvalue_of_hasEigenvector heig, ?_, hbound⟩
  intro μ hμ
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hvnorm : 0 < ‖v‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hv.2)
  have hvQ : Q v = μ * ‖v‖^2 := by
    change ⟪v, T v⟫ = _
    have hvT : T v = μ • v := hv.apply_eq_smul
    rw [hvT, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hb := hbound v
  rw [hvQ] at hb
  exact (mul_le_mul_iff_right₀ hvnorm).mp (by simpa only [mul_comm] using hb)
end ActualSmallestEigenvalue

end SafeLearning.CompleteFoundationsCompactnessWholeUnits30


namespace SafeLearning.CompleteFoundationsCompactnessWholeUnits30
section ActualHalvedBoxes
variable {I : Type*} [Fintype I]

theorem actual_midpoint_subdivision_retains_an_infinitely_visited_half_box
    (x : ℕ → I → ℝ) (a b : I → ℝ) (hab : a ≤ b)
    (hfreq : ∃ᶠ n in atTop, x n ∈ Icc a b) :
    ∃ p : (I → ℝ) × (I → ℝ), p.1 ≤ p.2 ∧
      (∃ᶠ n in atTop, x n ∈ Icc p.1 p.2) ∧ Icc p.1 p.2 ⊆ Icc a b ∧
      ∀ i, p.2 i - p.1 i = (b i - a i)/2 := by
  classical
  let m : I → ℝ := fun i => (a i + b i)/2
  let lo : (I → Bool) → I → ℝ := fun c i => if c i then m i else a i
  let hi : (I → Bool) → I → ℝ := fun c i => if c i then b i else m i
  have hcover : ∀ z ∈ Icc a b, ∃ c : I → Bool, z ∈ Icc (lo c) (hi c) := by
    intro z hz
    let c : I → Bool := fun i => decide (m i < z i)
    refine ⟨c, ?_, ?_⟩
    · intro i
      by_cases h : m i < z i
      · simp [lo, c, h]; linarith
      · simpa [lo, c, h] using hz.1 i
    · intro i
      by_cases h : m i < z i
      · simpa [hi, c, h] using hz.2 i
      · simp [hi, c, h]; exact le_of_not_gt h
  obtain ⟨c, hc⟩ := Filter.frequently_exists.mp (hfreq.mono fun n hn => hcover (x n) hn)
  refine ⟨(lo c, hi c), ?_, hc, ?_, ?_⟩
  · intro i
    cases h : c i <;> simp [lo, hi, h, m] <;> linarith [hab i]
  · intro z hz
    constructor
    · intro i
      have hzi := hz.1 i
      cases h : c i <;> simp [lo, h, m] at hzi <;> linarith [hab i]
    · intro i
      have hzi := hz.2 i
      cases h : c i <;> simp [hi, h, m] at hzi <;> linarith [hab i]
  · intro i
    cases h : c i <;> simp [lo, hi, h, m] <;> ring

theorem actual_repeated_midpoint_boxes_are_constructed_from_infinite_terms
    (x : ℕ → I → ℝ) (a b : I → ℝ) (hab : a ≤ b)
    (hfreq : ∃ᶠ n in atTop, x n ∈ Icc a b) :
    ∃ aa bb : ℕ → I → ℝ, aa 0 = a ∧ bb 0 = b ∧
      (∀ n, aa n ≤ bb n) ∧ (∀ n, ∃ᶠ k in atTop, x k ∈ Icc (aa n) (bb n)) ∧
      (∀ n, Icc (aa (n+1)) (bb (n+1)) ⊆ Icc (aa n) (bb n)) ∧
      ∀ n i, bb n i - aa n i = (b i - a i) * (1/2:ℝ)^n := by
  classical
  let S := {p : (I → ℝ) × (I → ℝ) // p.1 ≤ p.2 ∧ ∃ᶠ n in atTop, x n ∈ Icc p.1 p.2}
  have hex : ∀ s : S, ∃ p : (I → ℝ) × (I → ℝ), p.1 ≤ p.2 ∧
      (∃ᶠ n in atTop, x n ∈ Icc p.1 p.2) ∧ Icc p.1 p.2 ⊆ Icc s.val.1 s.val.2 ∧
      ∀ i, p.2 i - p.1 i = (s.val.2 i - s.val.1 i)/2 := by
    intro s
    exact actual_midpoint_subdivision_retains_an_infinitely_visited_half_box x
      s.val.1 s.val.2 s.property.1 s.property.2
  choose next hn using hex
  let nextS (s : S) : S := ⟨next s, (hn s).1, (hn s).2.1⟩
  let boxes : ℕ → S := fun n => Nat.rec (⟨(a,b), hab, hfreq⟩ : S) (fun _ s => nextS s) n
  let aa : ℕ → I → ℝ := fun n => (boxes n).val.1
  let bb : ℕ → I → ℝ := fun n => (boxes n).val.2
  refine ⟨aa, bb, rfl, rfl, (fun n => (boxes n).property.1),
    (fun n => (boxes n).property.2), ?_, ?_⟩
  · intro n
    exact (hn (boxes n)).2.2.1
  · intro n i
    induction n with
    | zero => simp [aa, bb, boxes]
    | succ n ih =>
      have hw := (hn (boxes n)).2.2.2 i
      change bb (n+1) i - aa (n+1) i = (bb n i - aa n i)/2 at hw
      rw [hw, ih, pow_succ]
      ring

theorem actual_nested_shrinking_boxes_give_a_subsequence_limit
    (x : ℕ → I → ℝ) (a b : ℕ → I → ℝ)
    (hnested : ∀ n, Icc (a (n+1)) (b (n+1)) ⊆ Icc (a n) (b n))
    (hfreq : ∀ n, ∃ᶠ k in atTop, x k ∈ Icc (a n) (b n))
    (hwidth : ∀ i, Tendsto (fun n => b n i - a n i) atTop (𝓝 0)) :
    ∃ z : I → ℝ, (∀ n, z ∈ Icc (a n) (b n)) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ n, x (φ n) ∈ Icc (a n) (b n)) ∧
        Tendsto (x ∘ φ) atTop (𝓝 z) := by
  classical
  have hnonempty : ∀ n, (Icc (a n) (b n)).Nonempty := by
    intro n
    obtain ⟨k, hk⟩ := (hfreq n).exists
    exact ⟨x k, hk⟩
  obtain ⟨z, hz⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n => Icc (a n) (b n)) hnested hnonempty isCompact_Icc (fun _ => isClosed_Icc)
  have hzall : ∀ n, z ∈ Icc (a n) (b n) := by simpa only [mem_iInter] using hz
  have hex : ∀ n M : ℕ, ∃ k, M ≤ k ∧ x k ∈ Icc (a n) (b n) := by
    intro n M
    exact frequently_atTop.mp (hfreq n) M
  choose index hge hmem using hex
  let φ : ℕ → ℕ := fun n => Nat.rec (index 0 0) (fun n prev => index (n+1) (prev+1)) n
  have hφ : StrictMono φ := strictMono_nat_of_lt_succ fun n => by
    change φ n < index (n+1) (φ n+1)
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (hge (n+1) (φ n+1))
  have hφmem : ∀ n, x (φ n) ∈ Icc (a n) (b n) := by
    intro n
    cases n with
    | zero => exact hmem 0 0
    | succ n => exact hmem (n+1) (φ n+1)
  refine ⟨z, hzall, φ, hφ, hφmem, ?_⟩
  apply tendsto_pi_nhds.mpr
  intro i
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.mp (hwidth i)).2 ε hε)
  refine ⟨N, ?_⟩
  intro n hn
  have hxi := hφmem n
  have hzi := hzall n
  have habs : |x (φ n) i - z i| ≤ b n i - a n i := by
    apply abs_le.mpr
    constructor <;> linarith [hxi.1 i, hxi.2 i, hzi.1 i, hzi.2 i]
  simpa only [Function.comp_apply, Real.dist_eq] using habs.trans_lt (hN n hn)

theorem actual_halved_box_proof_of_a_convergent_subsequence
    (x : ℕ → I → ℝ) (a b : I → ℝ) (hab : a ≤ b) (hx : ∀ n, x n ∈ Icc a b) :
    ∃ z : I → ℝ, z ∈ Icc a b ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (x ∘ φ) atTop (𝓝 z) := by
  obtain ⟨aa, bb, ha, hb, _, hfreq, hnested, hwidth⟩ :=
    actual_repeated_midpoint_boxes_are_constructed_from_infinite_terms x a b hab
      (Eventually.of_forall hx).frequently
  have hlim : ∀ i, Tendsto (fun n => bb n i - aa n i) atTop (𝓝 0) := by
    intro i
    simp_rw [hwidth]
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num : (1/2:ℝ) < 1)).const_mul (b i - a i)
  obtain ⟨z, hz, φ, hφ, _, ht⟩ :=
    actual_nested_shrinking_boxes_give_a_subsequence_limit x aa bb hnested hfreq hlim
  refine ⟨z, ?_, φ, hφ, ht⟩
  simpa only [ha, hb] using hz 0
end ActualHalvedBoxes
end SafeLearning.CompleteFoundationsCompactnessWholeUnits30


namespace SafeLearning.CompleteFoundationsCompactnessWholeUnits30

theorem actual_euclidean_bounded_sequence_halved_box_subsequence
    {I : Type*} [Fintype I] (x : ℕ → EuclideanSpace ℝ I) (R : ℝ)
    (hx : ∀ n, ‖x n‖ ≤ R) :
    ∃ z : EuclideanSpace ℝ I, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (x ∘ φ) atTop (𝓝 z) := by
  let e := PiLp.homeomorph 2 (fun _ : I => ℝ)
  let a : I → ℝ := fun _ => -|R|
  let b : I → ℝ := fun _ => |R|
  have hab : a ≤ b := fun i => by dsimp [a, b]; linarith [abs_nonneg R]
  have hbox : ∀ n, e (x n) ∈ Icc a b := by
    intro n
    have hcoord : ∀ i, |x n i| ≤ |R| := fun i => by
      have hh := PiLp.norm_apply_le (x n) i
      rw [Real.norm_eq_abs] at hh
      exact hh.trans ((hx n).trans (le_abs_self R))
    constructor
    · intro i
      exact (abs_le.mp (hcoord i)).1
    · intro i
      exact (abs_le.mp (hcoord i)).2
  obtain ⟨z, _, φ, hφ, ht⟩ :=
    actual_halved_box_proof_of_a_convergent_subsequence (fun n => e (x n)) a b hab hbox
  have hh := e.symm.continuous.tendsto z |>.comp ht
  refine ⟨e.symm z, φ, hφ, ?_⟩
  convert hh using 1
  funext n
  exact (e.symm_apply_apply (x (φ n))).symm
end SafeLearning.CompleteFoundationsCompactnessWholeUnits30
