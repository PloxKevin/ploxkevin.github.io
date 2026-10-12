import SafeLearning.CompleteFoundationsNormDuality
import Mathlib.Analysis.MeanInequalities
import Mathlib.Basic.Real.ConjExponents

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open scoped BigOperators RealInnerProductSpace ENNReal NNReal

namespace SafeLearning.CompleteFoundationsHolderDualNormWholeUnits30

open Set CompleteFoundationsNormDuality
variable {I : Type*} [Fintype I] [DecidableEq I]

-- TMP-only, uncompiled draft. The finite-p object is the genuine Mathlib PiLp norm.
-- Conjugacy below is the literal reciprocal identity, including both infinite endpoints.
def sourcePNorm (p : ℝ≥0∞) (x : I → ℝ) : ℝ :=
  ‖(WithLp.toLp p x : PiLp p (fun _ : I => ℝ))‖

theorem actual_finite_norm_formula {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ∞) (x : I → ℝ) :
    sourcePNorm p x = (∑ i, |x i| ^ p.toReal) ^ (1 / p.toReal) := by
  simp only [sourcePNorm, PiLp.norm_eq_sum (p.toReal_pos_iff_ne_top.mpr hp),
    PiLp.toLp_apply, Real.norm_eq_abs]

theorem actual_infinity_norm_formula (x : I → ℝ) : sourcePNorm ∞ x = ‖x‖ := by
  simp [sourcePNorm]

theorem actual_one_norm_formula (x : I → ℝ) : sourcePNorm 1 x = ∑ i, |x i| := by
  simp [sourcePNorm, PiLp.norm_eq_of_L1, Real.norm_eq_abs]

theorem actual_two_norm_formula (x : I → ℝ) : sourcePNorm 2 x = l2Norm x := rfl

theorem actual_pnorm_homogeneity {p : ℝ≥0∞} [Fact (1 ≤ p)] (c : ℝ) (x : I → ℝ) :
    sourcePNorm p (c • x) = |c| * sourcePNorm p x := by
  simp [sourcePNorm, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]

theorem actual_pnorm_neg {p : ℝ≥0∞} [Fact (1 ≤ p)] (x : I → ℝ) :
    sourcePNorm p (-x) = sourcePNorm p x := by
  simp [sourcePNorm, WithLp.toLp_neg]

theorem actual_pnorm_nonnegative {p : ℝ≥0∞} [Fact (1 ≤ p)] (x : I → ℝ) :
    0 ≤ sourcePNorm p x := norm_nonneg _

theorem actual_all_conjugate_holder (p q : ℝ≥0∞) [ENNReal.HolderConjugate p q]
    (u v : I → ℝ) : |u ⬝ᵥ v| ≤ sourcePNorm p u * sourcePNorm q v := by
  letI : Fact (1 ≤ p) := ⟨ENNReal.HolderConjugate.one_le p q⟩
  letI : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  by_cases hp : p = ∞
  · have hq : q = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one p q).mp hp
    subst p; subst q
    have h := actual_infinity_ball_holder v u ‖u‖ (norm_nonneg u) le_rfl
    rw [dotProduct_comm] at h
    simpa [sourcePNorm, l1Norm] using h
  by_cases hq : q = ∞
  · have hp1 : p = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one q p).mp hq
    subst p; subst q
    have h := actual_infinity_ball_holder u v ‖v‖ (norm_nonneg v) le_rfl
    simpa [sourcePNorm, l1Norm, mul_comm] using h
  have hc := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
  calc
    |u ⬝ᵥ v| ≤ ∑ i, |u i| * |v i| := by
      simpa [dotProduct, abs_mul] using
        (Finset.abs_sum_le_sum_abs (fun i : I => u i * v i) Finset.univ)
    _ ≤ (∑ i, |u i| ^ p.toReal) ^ (1 / p.toReal) *
        (∑ i, |v i| ^ q.toReal) ^ (1 / q.toReal) := by
      simpa only [abs_abs] using
        Real.inner_le_Lp_mul_Lq Finset.univ (fun i => |u i|) (fun i => |v i|) hc
    _ = sourcePNorm p u * sourcePNorm q v := by
      rw [actual_finite_norm_formula hp, actual_finite_norm_formula hq]

theorem actual_finite_conjugate_unit_attainer (p q : ℝ≥0∞)
    [ENNReal.HolderConjugate p q] (hp : p ≠ ∞) (hq : q ≠ ∞) (w : I → ℝ) :
    ∃ x : I → ℝ, sourcePNorm p x ≤ 1 ∧ w ⬝ᵥ x = sourcePNorm q w := by
  letI : Fact (1 ≤ p) := ⟨ENNReal.HolderConjugate.one_le p q⟩
  letI : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  have hc := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
  let f : I → ℝ≥0 := fun i => ⟨|w i|, abs_nonneg _⟩
  obtain ⟨g, hg, he⟩ := (NNReal.isGreatest_Lp Finset.univ f hc.symm).1
  let x : I → ℝ := fun i => Real.sign (w i) * (g i : ℝ)
  have hgReal : ∑ i, (g i : ℝ) ^ p.toReal ≤ 1 := by
    have h := NNReal.coe_le_coe.mpr hg
    simpa using h
  have hsum : ∑ i, |x i| ^ p.toReal ≤ 1 := by
    apply le_trans (Finset.sum_le_sum fun i _ => ?_) hgReal
    apply Real.rpow_le_rpow (abs_nonneg _) ?_ hc.nonneg
    dsimp [x]
    rw [abs_mul, abs_of_nonneg (g i).coe_nonneg]
    simpa using mul_le_mul_of_nonneg_right
      (actual_sign_absolute_bound_and_dot (w i)).1 (g i).coe_nonneg
  refine ⟨x, ?_, ?_⟩
  · rw [actual_finite_norm_formula hp]
    exact Real.rpow_le_one
      (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _)
      hsum (le_of_lt hc.one_div_pos)
  · have hval : ∑ i, |w i| * (g i : ℝ) = sourcePNorm q w := by
      have h := congrArg ((↑) : ℝ≥0 → ℝ) he
      simp only [NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_rpow] at h
      change (∑ i, |w i| * (g i : ℝ)) =
        (∑ i, |w i| ^ q.toReal) ^ (1 / q.toReal) at h
      simpa only [actual_finite_norm_formula hq] using h
    rw [dotProduct]
    calc
      ∑ i, w i * x i = ∑ i, |w i| * (g i : ℝ) := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp [x]
        rw [← mul_assoc, (actual_sign_absolute_bound_and_dot (w i)).2]
      _ = sourcePNorm q w := hval

theorem actual_all_conjugate_unit_attainer (p q : ℝ≥0∞)
    [ENNReal.HolderConjugate p q] (w : I → ℝ) :
    ∃ x : I → ℝ, sourcePNorm p x ≤ 1 ∧ w ⬝ᵥ x = sourcePNorm q w := by
  letI : Fact (1 ≤ p) := ⟨ENNReal.HolderConjugate.one_le p q⟩
  letI : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  by_cases hp : p = ∞
  · have hq : q = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one p q).mp hp
    subst p; subst q
    refine ⟨fun i => Real.sign (w i), ?_, ?_⟩
    · simpa [sourcePNorm] using (actual_sign_vector_attains_infinity_ball w 1 zero_le_one).1
    · simpa [sourcePNorm, l1Norm] using (actual_sign_vector_attains_infinity_ball w 1 zero_le_one).2
  by_cases hq : q = ∞
  · have hp1 : p = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one q p).mp hq
    subst p; subst q
    cases isEmpty_or_nonempty I with
    | inl hempty =>
      letI : IsEmpty I := hempty
      have hw0 : w = 0 := Subsingleton.elim _ _
      rw [hw0]
      refine ⟨0, ?_, ?_⟩ <;> simp [sourcePNorm, dotProduct]
    | inr hnonempty =>
      letI : Nonempty I := hnonempty
      obtain ⟨j, hj⟩ := actual_largest_absolute_coordinate_exists w
      refine ⟨Pi.single j (Real.sign (w j)), ?_, ?_⟩
      · simpa [sourcePNorm, l1Norm] using (actual_largest_coordinate_attains_one_ball w j hj 1 zero_le_one).1
      · simpa [sourcePNorm, l1Norm] using (actual_largest_coordinate_attains_one_ball w j hj 1 zero_le_one).2
  exact actual_finite_conjugate_unit_attainer p q hp hq w

theorem actual_all_conjugate_ball_maximum_and_minimum (p q : ℝ≥0∞)
    [ENNReal.HolderConjugate p q] (w : I → ℝ) (ε : ℝ) (hε : 0 ≤ ε) :
    IsGreatest ((fun x : I → ℝ => w ⬝ᵥ x) '' {x | sourcePNorm p x ≤ ε})
      (ε * sourcePNorm q w) ∧
    IsLeast ((fun x : I → ℝ => w ⬝ᵥ x) '' {x | sourcePNorm p x ≤ ε})
      (-ε * sourcePNorm q w) := by
  letI : Fact (1 ≤ p) := ⟨ENNReal.HolderConjugate.one_le p q⟩
  letI : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  obtain ⟨x, hx, he⟩ := actual_all_conjugate_unit_attainer p q w
  have scaledNorm : sourcePNorm p (ε • x) ≤ ε := by
    rw [actual_pnorm_homogeneity, abs_of_nonneg hε]
    simpa using mul_le_mul_of_nonneg_left hx hε
  have scaledDot : w ⬝ᵥ (ε • x) = ε * sourcePNorm q w := by
    rw [dotProduct_smul, he]; ring
  have bound : ∀ z : I → ℝ, sourcePNorm p z ≤ ε →
      |w ⬝ᵥ z| ≤ ε * sourcePNorm q w := by
    intro z hz
    have h := actual_all_conjugate_holder p q z w
    rw [dotProduct_comm] at h
    exact h.trans (mul_le_mul_of_nonneg_right hz (actual_pnorm_nonnegative w))
  constructor
  · refine ⟨⟨ε • x, scaledNorm, scaledDot⟩, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact (le_abs_self _).trans (bound z hz)
  · refine ⟨⟨-(ε • x), ?_, ?_⟩, ?_⟩
    · change sourcePNorm p (-(ε • x)) ≤ ε
      simpa only [actual_pnorm_neg] using scaledNorm
    · change w ⬝ᵥ (-(ε • x)) = -ε * sourcePNorm q w
      rw [dotProduct_neg, scaledDot]; ring
    · rintro _ ⟨z, hz, rfl⟩
      simpa only [neg_mul] using (abs_le.mp (bound z hz)).1

theorem actual_all_conjugate_dual_norm (p q : ℝ≥0∞)
    [ENNReal.HolderConjugate p q] (w : I → ℝ) :
    IsGreatest ((fun x : I → ℝ => w ⬝ᵥ x) '' {x | sourcePNorm p x ≤ 1})
      (sourcePNorm q w) := by
  simpa using (actual_all_conjugate_ball_maximum_and_minimum p q w 1 zero_le_one).1

theorem actual_holder_equality_is_attainable (p q : ℝ≥0∞)
    [ENNReal.HolderConjugate p q] (w : I → ℝ) :
    ∃ x : I → ℝ, |w ⬝ᵥ x| = sourcePNorm q w * sourcePNorm p x := by
  letI : Fact (1 ≤ p) := ⟨ENNReal.HolderConjugate.one_le p q⟩
  letI : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  obtain ⟨x, hx, he⟩ := actual_all_conjugate_unit_attainer p q w
  refine ⟨x, le_antisymm (actual_all_conjugate_holder q p w x) ?_⟩
  rw [he, abs_of_nonneg (actual_pnorm_nonnegative w)]
  simpa using mul_le_mul_of_nonneg_left hx (actual_pnorm_nonnegative w)

theorem actual_young_nonnegative_real_exponents {a b p q : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hpq : p.HolderConjugate q) :
    a * b ≤ a ^ p / p + b ^ q / q :=
  Real.young_inequality_of_nonneg ha hb hpq

theorem actual_named_euclidean_attaining_point (w : I → ℝ) (hw : w ≠ 0)
    (ε : ℝ) (hε : 0 ≤ ε) :
    sourcePNorm 2 ((ε / l2Norm w) • w) = ε ∧
    w ⬝ᵥ ((ε / l2Norm w) • w) = ε * l2Norm w := by
  have hn : 0 < l2Norm w := by
    apply norm_pos_iff.mpr
    intro h
    apply hw
    exact WithLp.toLp_injective 2 h
  constructor
  · rw [actual_pnorm_homogeneity, actual_two_norm_formula,
      abs_of_nonneg (div_nonneg hε hn.le), div_mul_cancel₀ _ hn.ne']
  · have hs : w ⬝ᵥ w = l2Norm w ^ 2 := by
      rw [← actual_euclidean_pairing_is_dot, real_inner_self_eq_norm_sq]
      rfl
    rw [dotProduct_smul, hs]
    change (ε / l2Norm w) * l2Norm w ^ 2 = ε * l2Norm w
    field_simp [hn.ne']

theorem actual_zero_weight_every_feasible_point_maximizes (p : ℝ≥0∞)
    (x : I → ℝ) : (0 : I → ℝ) ⬝ᵥ x = 0 := by simp

theorem actual_pnorm_zero {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    sourcePNorm p (0 : I → ℝ) = 0 := by simp [sourcePNorm]

theorem actual_all_conjugate_linear_image_is_the_full_closed_interval
    (p q : ℝ≥0∞) [ENNReal.HolderConjugate p q] (w : I → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε) :
    ((fun x : I → ℝ => w ⬝ᵥ x) '' {x | sourcePNorm p x ≤ ε}) =
      Icc (-ε * sourcePNorm q w) (ε * sourcePNorm q w) := by
  letI : Fact (1 ≤ p) := ⟨ENNReal.HolderConjugate.one_le p q⟩
  letI : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  obtain ⟨x, hx, he⟩ := actual_all_conjugate_unit_attainer p q w
  ext b
  constructor
  · rintro ⟨z, hz, rfl⟩
    have h := actual_all_conjugate_holder p q z w
    rw [dotProduct_comm] at h
    have hb := h.trans (mul_le_mul_of_nonneg_right hz (actual_pnorm_nonnegative w))
    simpa only [mem_Icc, neg_mul] using abs_le.mp hb
  · intro hb
    have hab : |b| ≤ ε * sourcePNorm q w := by
      apply abs_le.mpr
      simpa only [mem_Icc, neg_mul] using hb
    by_cases hz : sourcePNorm q w = 0
    · have hb0 : b = 0 := by rw [hz, mul_zero] at hab; exact abs_nonpos_iff.mp hab
      subst b
      refine ⟨0, ?_, by simp⟩
      change sourcePNorm p (0 : I → ℝ) ≤ ε
      simpa only [actual_pnorm_zero] using hε
    · have hpos : 0 < sourcePNorm q w := lt_of_le_of_ne
        (actual_pnorm_nonnegative w) (Ne.symm hz)
      refine ⟨(b / sourcePNorm q w) • x, ?_, ?_⟩
      · change sourcePNorm p ((b / sourcePNorm q w) • x) ≤ ε
        rw [actual_pnorm_homogeneity, abs_div, abs_of_pos hpos]
        have hs : |b| / sourcePNorm q w ≤ ε := (div_le_iff₀ hpos).mpr hab
        have hn : 0 ≤ |b| / sourcePNorm q w := div_nonneg (abs_nonneg b) hpos.le
        exact (mul_le_mul_of_nonneg_left hx hn).trans (by simpa using hs)
      · change w ⬝ᵥ ((b / sourcePNorm q w) • x) = b
        rw [dotProduct_smul, he]
        exact div_mul_cancel₀ _ hz

theorem actual_box_hyperplane_intersection_iff (w : I → ℝ) (b : ℝ) :
    (∃ x : I → ℝ, (∀ i, -1 ≤ x i ∧ x i ≤ 1) ∧ w ⬝ᵥ x = b) ↔
      |b| ≤ l1Norm w := by
  have himage := actual_all_conjugate_linear_image_is_the_full_closed_interval ∞ 1 w 1 zero_le_one
  have hnorm : ∀ x : I → ℝ, (∀ i, -1 ≤ x i ∧ x i ≤ 1) ↔ sourcePNorm ∞ x ≤ 1 := by
    intro x
    rw [actual_infinity_norm_formula, pi_norm_le_iff_of_nonneg zero_le_one]
    simp only [Real.norm_eq_abs, abs_le]
  constructor
  · rintro ⟨x, hx, he⟩
    have hb : b ∈ Icc (-l1Norm w) (l1Norm w) := by
      have hm : b ∈ ((fun z : I → ℝ => w ⬝ᵥ z) '' {z | sourcePNorm ∞ z ≤ 1}) :=
        ⟨x, (hnorm x).mp hx, he⟩
      rw [himage] at hm
      simpa only [sourcePNorm, l1Norm, one_mul, neg_one_mul] using hm
    exact abs_le.mpr hb
  · intro hb
    have hm : b ∈ ((fun z : I → ℝ => w ⬝ᵥ z) '' {z | sourcePNorm ∞ z ≤ 1}) := by
      rw [himage]
      simpa only [sourcePNorm, l1Norm, one_mul, neg_one_mul, mem_Icc] using abs_le.mp hb
    rcases hm with ⟨x, hx, he⟩
    exact ⟨x, (hnorm x).mpr hx, he⟩



def sourceWeights : Fin 3 → ℝ := ![2,-1,3]

theorem actual_printed_example_one_norm_is_six : l1Norm sourceWeights = 6 := by
  norm_num [actual_l1_norm_is_sum_absolute_values, sourceWeights, Fin.sum_univ_succ]

theorem actual_printed_example_infinity_norm_is_three : ‖sourceWeights‖ = 3 := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 3)).mpr
    intro i
    fin_cases i <;> norm_num [sourceWeights]
  · simpa [sourceWeights] using norm_le_pi_norm sourceWeights (2 : Fin 3)

theorem actual_printed_example_two_norm_is_sqrt_fourteen :
    l2Norm sourceWeights = Real.sqrt 14 := by
  have hs := actual_l2_norm_squared sourceWeights
  norm_num [sourceWeights, Fin.sum_univ_succ] at hs
  change l2Norm sourceWeights ^ 2 = 14 at hs
  have hn : 0 ≤ l2Norm sourceWeights := norm_nonneg _
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 14), Real.sqrt_nonneg (14:ℝ)]

theorem actual_printed_three_endpoint_values_and_euclidean_rounding :
    (1/10:ℝ) * l1Norm sourceWeights = 3/5 ∧
    (1/10:ℝ) * ‖sourceWeights‖ = 3/10 ∧
    (1/10:ℝ) * l2Norm sourceWeights = Real.sqrt 14 / 10 ∧
    747/2000 < Real.sqrt (14:ℝ) / 10 ∧
    Real.sqrt (14:ℝ) / 10 < 749/2000 ∧
    187/500 < Real.sqrt (14:ℝ) / 10 := by
  rw [actual_printed_example_one_norm_is_six,
    actual_printed_example_infinity_norm_is_three,
    actual_printed_example_two_norm_is_sqrt_fourteen]
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 14)
  have hn := Real.sqrt_nonneg (14:ℝ)
  refine ⟨by norm_num, by norm_num, by ring, ?_, ?_, ?_⟩ <;> nlinarith

end SafeLearning.CompleteFoundationsHolderDualNormWholeUnits30
