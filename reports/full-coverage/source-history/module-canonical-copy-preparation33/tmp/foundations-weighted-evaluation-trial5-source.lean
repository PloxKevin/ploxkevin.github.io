import SafeLearning.CompleteFoundationsTransientNeumann

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Matrix Filter
open scoped BigOperators Topology NNReal Matrix.Norms.Operator
namespace SafeLearning.CompleteFoundationsWeightedEvaluation
open CompleteFoundationsTransientNeumann

variable {S : Type*} [Fintype S] [DecidableEq S]

local instance : TopologicalSpace (Matrix S S ℝ) :=
  (Matrix.linftyOpNormedRing (n:=S) (α:=ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace

def fundamentalWeight (P : Matrix S S ℝ) : S → ℝ :=
  (1-P)⁻¹ *ᵥ (fun _ => 1)

theorem actual_nonnegative_transient_matrix_has_positive_fundamental_weights
    (P : Matrix S S ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (hdecay : Tendsto (fun n : ℕ => P^n) atTop (𝓝 0)) :
    (∀ s, 1 ≤ fundamentalWeight P s) ∧
      P *ᵥ fundamentalWeight P = fun s => fundamentalWeight P s-1 := by
  have hp (n : ℕ) : ∀ i j, 0 ≤ (P^n) i j := by
    induction n with
    | zero => intro i j;simp only [pow_zero, Matrix.one_apply];split_ifs <;> norm_num
    | succ n ih =>
      intro i j
      rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg (fun k _ => mul_nonneg (ih i k) (hP k j))
  have hs := (actual_finite_transient_matrix_power_decay_implies_its_literal_inverse_series P hdecay).2.1
  have he (i j : S) : HasSum (fun n : ℕ => (P^n) i j) ((1-P)⁻¹ i j) :=
    Pi.hasSum.mp (Pi.hasSum.mp hs i) j
  have hentry (i j : S) : (1 : Matrix S S ℝ) i j ≤ (1-P)⁻¹ i j := by
    have h := (he i j).summable.le_tsum 0 (fun n _ => hp n i j)
    rw [(he i j).tsum_eq] at h
    simpa only [pow_zero] using h
  have hidentity := (actual_power_decay_implies_a_true_unit_and_inverse_neumann_series P hdecay).2.2.1
  have hsum := (actual_finite_transient_matrix_power_decay_implies_its_literal_inverse_series P hdecay).2.2
  rw [hsum] at hidentity
  have hvec : (1-P) *ᵥ fundamentalWeight P = (fun _ => 1) := by
    rw [fundamentalWeight, Matrix.mulVec_mulVec, hidentity, Matrix.one_mulVec]
  constructor
  · intro s
    calc
      1 = ∑ j, (1 : Matrix S S ℝ) s j := by simp [Matrix.one_apply]
      _ ≤ ∑ j, (1-P)⁻¹ s j := Finset.sum_le_sum (fun j _ => hentry s j)
      _ = fundamentalWeight P s := by simp [fundamentalWeight, Matrix.mulVec,dotProduct]
  · funext s
    have h := congrFun hvec s
    rw [Matrix.sub_mulVec, Matrix.one_mulVec] at h
    change fundamentalWeight P s-(P *ᵥ fundamentalWeight P) s=1 at h
    linarith

def normalizedEvaluation (P : Matrix S S ℝ) (reward weight : S → ℝ)
    (value : S → ℝ) (s : S) : ℝ :=
  (reward s+∑ j,P s j*weight j*value j)/weight s

def originalEvaluation (P : Matrix S S ℝ) (reward value : S → ℝ) : S → ℝ :=
  reward+P *ᵥ value

omit [DecidableEq S] in
theorem actual_weighted_row_bound_gives_the_uniform_normalized_error_bound
    (P : Matrix S S ℝ) (reward weight : S → ℝ) (q epsilon : ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hw : ∀ s, 0 < weight s) (hepsilon : 0 ≤ epsilon)
    (hrow : ∀ s, ∑ j,P s j*weight j ≤ q*weight s)
    (value other : S → ℝ) (herror : ∀ s, |value s-other s| ≤ epsilon) (s : S) :
    |normalizedEvaluation P reward weight value s-
      normalizedEvaluation P reward weight other s| ≤ q*epsilon := by
  have hdiff : normalizedEvaluation P reward weight value s-
      normalizedEvaluation P reward weight other s=
      (∑ j,P s j*weight j*(value j-other j))/weight s := by
    unfold normalizedEvaluation
    rw [←sub_div]
    congr 1
    rw [show reward s+(∑ j,P s j*weight j*value j)-
      (reward s+∑ j,P s j*weight j*other j)=
      (∑ j,P s j*weight j*value j)-(∑ j,P s j*weight j*other j) by ring]
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hdiff, abs_div, abs_of_pos (hw s)]
  apply (div_le_iff₀ (hw s)).mpr
  calc
    |∑ j,P s j*weight j*(value j-other j)|
      ≤ ∑ j,|P s j*weight j*(value j-other j)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j,(P s j*weight j)*|value j-other j| := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [abs_mul, abs_of_nonneg (mul_nonneg (hP s j) (hw j).le)]
    _ ≤ ∑ j,(P s j*weight j)*epsilon := Finset.sum_le_sum
      (fun j _ => mul_le_mul_of_nonneg_left (herror j) (mul_nonneg (hP s j) (hw j).le))
    _ = (∑ j,P s j*weight j)*epsilon := by rw [Finset.sum_mul]
    _ ≤ (q*weight s)*epsilon := mul_le_mul_of_nonneg_right (hrow s) hepsilon
    _ = q*epsilon*weight s := by ring

omit [DecidableEq S] in
theorem actual_weighted_evaluation_is_a_true_normalized_sup_norm_contraction
    (P : Matrix S S ℝ) (reward weight : S → ℝ) (q : ℝ≥0) (hq : q < 1)
    (hP : ∀ i j, 0 ≤ P i j) (hw : ∀ s, 0 < weight s)
    (hrow : ∀ s, ∑ j,P s j*weight j ≤ (q:ℝ)*weight s) :
    ContractingWith q (normalizedEvaluation P reward weight) := by
  refine ⟨hq,LipschitzWith.of_dist_le_mul ?_⟩
  intro value other
  apply (dist_pi_le_iff (mul_nonneg q.coe_nonneg dist_nonneg)).mpr
  intro s
  simpa only [Real.dist_eq] using actual_weighted_row_bound_gives_the_uniform_normalized_error_bound
    P reward weight q (dist value other) hP hw dist_nonneg hrow value other
    (fun t => by simpa only [Real.dist_eq] using dist_le_pi_dist value other t) s

theorem actual_positive_weight_row_identity_provides_a_strict_contraction_factor
    [Nonempty S] (P : Matrix S S ℝ) (weight : S → ℝ)
    (hw : ∀ s, 1 ≤ weight s) (hrow : P *ᵥ weight = fun s => weight s-1) :
    ∃ q : ℝ≥0, q < 1 ∧ ∀ s, ∑ j,P s j*weight j ≤ (q:ℝ)*weight s := by
  classical
  let maximum : ℝ := Finset.univ.sup' Finset.univ_nonempty weight
  have hm (s : S) : weight s ≤ maximum := Finset.le_sup' weight (Finset.mem_univ s)
  have hm1 : 1 ≤ maximum := (hw (Classical.arbitrary S)).trans (hm _)
  have hmp : 0 < maximum := by linarith
  have hq0 : 0 ≤ 1-1/maximum := by
    have h : 1/maximum ≤ (1:ℝ) := (div_le_iff₀ hmp).mpr (by simpa using hm1)
    linarith
  refine ⟨⟨1-1/maximum,hq0⟩,?_,?_⟩
  · change 1-1/maximum<1
    have h := one_div_pos.mpr hmp
    linarith
  · intro s
    have hr := congrFun hrow s
    change (∑ j,P s j*weight j)=weight s-1 at hr
    rw [hr]
    change weight s-1 ≤ (1-1/maximum)*weight s
    have h : weight s/maximum ≤ (1:ℝ) := (div_le_iff₀ hmp).mpr (by simpa using hm s)
    rw [show (1-1/maximum)*weight s=weight s-weight s/maximum by ring]
    linarith

omit [DecidableEq S] in
theorem actual_normalized_fixed_point_is_the_true_original_evaluation_fixed_point
    (P : Matrix S S ℝ) (reward weight value : S → ℝ) (hw : ∀ s, weight s≠0) :
    normalizedEvaluation P reward weight value=value ↔
      originalEvaluation P reward (fun s => weight s*value s)=fun s => weight s*value s := by
  constructor
  · intro h
    funext s
    have hs := congrFun h s
    change (reward s+∑ j,P s j*weight j*value j)/weight s=value s at hs
    have he := (div_eq_iff (hw s)).mp hs
    simpa only [originalEvaluation,Pi.add_apply,Matrix.mulVec, dotProduct,mul_assoc,mul_comm,mul_left_comm] using he
  · intro h
    funext s
    apply (div_eq_iff (hw s)).mpr
    have he := congrFun h s
    simpa only [originalEvaluation,Pi.add_apply,Matrix.mulVec,dotProduct,mul_assoc,mul_comm,mul_left_comm] using he

def normalize (weight value : S → ℝ) : S → ℝ := fun s => value s/weight s
def unnormalize (weight value : S → ℝ) : S → ℝ := fun s => weight s*value s

omit [Fintype S] [DecidableEq S] in
theorem actual_positive_coordinate_weights_have_two_sided_normalization
    (weight value : S → ℝ) (hw : ∀ s, weight s≠0) :
    unnormalize weight (normalize weight value)=value ∧
      normalize weight (unnormalize weight value)=value := by
  constructor <;> funext s <;> dsimp [normalize,unnormalize] <;> field_simp [hw s]

omit [DecidableEq S] in
theorem actual_original_evaluation_is_conjugate_to_the_normalized_map
    (P : Matrix S S ℝ) (reward weight value : S → ℝ) (hw : ∀ s, weight s≠0) :
    originalEvaluation P reward (unnormalize weight value)=
      unnormalize weight (normalizedEvaluation P reward weight value) := by
  funext s
  simp only [originalEvaluation,unnormalize,normalizedEvaluation,Pi.add_apply,
    Matrix.mulVec,dotProduct]
  rw [mul_div_cancel₀ _ (hw s)]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  ring

omit [DecidableEq S] in
theorem actual_every_original_evaluation_iterate_is_the_weighted_normalized_iterate
    (P : Matrix S S ℝ) (reward weight initial : S → ℝ) (hw : ∀ s, weight s≠0) (n : ℕ) :
    (originalEvaluation P reward)^[n] (unnormalize weight initial)=
      unnormalize weight ((normalizedEvaluation P reward weight)^[n] initial) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih,
      actual_original_evaluation_is_conjugate_to_the_normalized_map P reward weight _ hw,
      Function.iterate_succ_apply']

def weightedNorm (weight value : S → ℝ) : ℝ := ‖normalize weight value‖

omit [DecidableEq S] in
theorem actual_weighted_sup_norm_has_the_printed_coordinate_bound_characterization
    [Nonempty S] (weight value : S → ℝ) (hw : ∀ s, 0 < weight s) (bound : ℝ) :
    weightedNorm weight value ≤ bound ↔ ∀ s, |value s|/weight s ≤ bound := by
  rw [weightedNorm,pi_norm_le_iff_of_nonempty]
  simp only [normalize,Real.norm_eq_abs,abs_div,abs_of_pos (hw _)]

omit [DecidableEq S] in
theorem actual_normalization_of_original_evaluation_is_the_normalized_operator
    (P : Matrix S S ℝ) (reward weight value : S → ℝ) (hw : ∀ s, weight s≠0) :
    normalize weight (originalEvaluation P reward value)=
      normalizedEvaluation P reward weight (normalize weight value) := by
  have h := actual_original_evaluation_is_conjugate_to_the_normalized_map
    P reward weight (normalize weight value) hw
  rw [(actual_positive_coordinate_weights_have_two_sided_normalization weight value hw).1] at h
  have he := congrArg (normalize weight) h
  rw [(actual_positive_coordinate_weights_have_two_sided_normalization
    weight (normalizedEvaluation P reward weight (normalize weight value)) hw).2] at he
  exact he

omit [DecidableEq S] in
theorem actual_row_bound_proves_contraction_of_the_original_operator_in_the_weighted_norm
    (P : Matrix S S ℝ) (reward weight : S → ℝ) (q : ℝ≥0) (hq : q < 1)
    (hP : ∀ i j, 0 ≤ P i j) (hw : ∀ s, 0 < weight s)
    (hrow : ∀ s, ∑ j,P s j*weight j ≤ (q:ℝ)*weight s) (value other : S → ℝ) :
    weightedNorm weight (originalEvaluation P reward value-originalEvaluation P reward other) ≤
      (q:ℝ)*weightedNorm weight (value-other) := by
  have hsub (value other : S → ℝ) : normalize weight (value-other)=
      normalize weight value-normalize weight other := by
    funext s
    simp only [normalize,Pi.sub_apply,sub_div]
  have hwn : ∀ s, weight s≠0 := fun s => (hw s).ne'
  rw [weightedNorm,weightedNorm,hsub,hsub,←dist_eq_norm,←dist_eq_norm,
    actual_normalization_of_original_evaluation_is_the_normalized_operator P reward weight value hwn,
    actual_normalization_of_original_evaluation_is_the_normalized_operator P reward weight other hwn]
  exact (actual_weighted_evaluation_is_a_true_normalized_sup_norm_contraction
    P reward weight q hq hP hw hrow).2.dist_le_mul _ _

theorem actual_transient_policy_evaluation_contracts_in_its_derived_fundamental_weight_norm
    [Nonempty S] (P : Matrix S S ℝ) (reward : S → ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (hdecay : Tendsto (fun n : ℕ => P^n) atTop (𝓝 0)) :
    ∃ q : ℝ≥0,q < 1 ∧ ∀ value other,
      weightedNorm (fundamentalWeight P) (originalEvaluation P reward value-originalEvaluation P reward other) ≤
        (q:ℝ)*weightedNorm (fundamentalWeight P) (value-other) := by
  have hweights := actual_nonnegative_transient_matrix_has_positive_fundamental_weights P hP hdecay
  obtain ⟨q,hq,hrow⟩ := actual_positive_weight_row_identity_provides_a_strict_contraction_factor
    P (fundamentalWeight P) hweights.1 hweights.2
  refine ⟨q,hq,?_⟩
  intro value other
  exact actual_row_bound_proves_contraction_of_the_original_operator_in_the_weighted_norm
    P reward (fundamentalWeight P) q hq hP (fun s => by linarith [hweights.1 s]) hrow value other

theorem actual_transient_policy_evaluation_has_a_unique_inverse_value_and_all_start_convergence
    [Nonempty S] (P : Matrix S S ℝ) (reward initial : S → ℝ)
    (hP : ∀ i j, 0 ≤ P i j)
    (hdecay : Tendsto (fun n : ℕ => P^n) atTop (𝓝 0)) :
    ∃ value : S → ℝ,originalEvaluation P reward value=value ∧
      value=(1-P)⁻¹ *ᵥ reward ∧
      Tendsto (fun n : ℕ => (originalEvaluation P reward)^[n] initial) atTop (𝓝 value) ∧
      ∀ other,originalEvaluation P reward other=other → other=value := by
  have hfweights := actual_nonnegative_transient_matrix_has_positive_fundamental_weights P hP hdecay
  let weight := fundamentalWeight P
  have hw : ∀ s, 0 < weight s := fun s => by dsimp [weight];linarith [hfweights.1 s]
  have hwn : ∀ s, weight s≠0 := fun s => (hw s).ne'
  obtain ⟨q,hq,hrow⟩ := actual_positive_weight_row_identity_provides_a_strict_contraction_factor
    P weight hfweights.1 hfweights.2
  have hc := actual_weighted_evaluation_is_a_true_normalized_sup_norm_contraction
    P reward weight q hq hP hw hrow
  obtain ⟨fixed,hfixed,hlimit,_⟩ := hc.exists_fixedPoint (normalize weight initial) (edist_ne_top _ _)
  let value := unnormalize weight fixed
  have hactual : originalEvaluation P reward value=value := by
    dsimp [value]
    rw [actual_original_evaluation_is_conjugate_to_the_normalized_map P reward weight fixed hwn,hfixed]
  have hunique : ∀ other,originalEvaluation P reward other=other → other=value := by
    intro other ho
    have hnorm : normalizedEvaluation P reward weight (normalize weight other)=normalize weight other := by
      apply (actual_normalized_fixed_point_is_the_true_original_evaluation_fixed_point
        P reward weight (normalize weight other) hwn).mpr
      change originalEvaluation P reward (unnormalize weight (normalize weight other))=
        unnormalize weight (normalize weight other)
      rw [(actual_positive_coordinate_weights_have_two_sided_normalization weight other hwn).1]
      exact ho
    have he := hc.fixedPoint_unique' hnorm hfixed
    calc
      other=unnormalize weight (normalize weight other) :=
        (actual_positive_coordinate_weights_have_two_sided_normalization weight other hwn).1.symm
      _=value := by rw [he]
  have hcontinuous : Continuous (unnormalize weight) := by unfold unnormalize;fun_prop
  have hlimitActual : Tendsto (fun n : ℕ => (originalEvaluation P reward)^[n] initial)
      atTop (𝓝 value) := by
    have h := (hcontinuous.tendsto fixed).comp hlimit
    convert h using 1
    funext n
    change (originalEvaluation P reward)^[n] initial=
      unnormalize weight ((normalizedEvaluation P reward weight)^[n] (normalize weight initial))
    rw [←actual_every_original_evaluation_iterate_is_the_weighted_normalized_iterate
      P reward weight (normalize weight initial) hwn n,
      (actual_positive_coordinate_weights_have_two_sided_normalization weight initial hwn).1]
  have hright := (actual_power_decay_implies_a_true_unit_and_inverse_neumann_series P hdecay).2.2.2
  have hsum := (actual_finite_transient_matrix_power_decay_implies_its_literal_inverse_series P hdecay).2.2
  rw [hsum] at hright
  have hnormal : (1-P) *ᵥ value=reward := by
    rw [Matrix.sub_mulVec,Matrix.one_mulVec]
    have h := hactual
    change reward+P *ᵥ value=value at h
    ext s
    have he := congrFun h s
    change reward s+(P *ᵥ value) s=value s at he
    change value s-(P *ᵥ value) s=reward s
    linarith
  have hinverse : value=(1-P)⁻¹ *ᵥ reward := by
    calc
      value=1 *ᵥ value := by simp
      _=((1-P)⁻¹*(1-P)) *ᵥ value := by rw [hright]
      _=(1-P)⁻¹ *ᵥ reward := by rw [←Matrix.mulVec_mulVec,hnormal]
  exact ⟨value,hactual,hinverse,hlimitActual,hunique⟩

end SafeLearning.CompleteFoundationsWeightedEvaluation
