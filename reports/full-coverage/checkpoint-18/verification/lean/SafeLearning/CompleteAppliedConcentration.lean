import Mathlib
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedConcentration
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

/-- The book uses R in exp(t²R²/2); Mathlib's parameter is R². -/
theorem hoeffding_lemma {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (a b : ℝ)
    (hm : AEMeasurable X μ) (hb : ∀ᵐ w ∂μ, X w ∈ Set.Icc a b)
    (hc : ∫ w, X w ∂μ=0) :
    HasSubgaussianMGF X ((‖b-a‖₊/2)^2) μ :=
  hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hm hb hc

theorem centered_unit_interval_subgaussian {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hm : AEMeasurable X μ) (hb : ∀ᵐ w ∂μ, X w ∈ Set.Icc (0:ℝ) 1) :
    HasSubgaussianMGF (fun w => X w-∫ v, X v ∂μ) (1/4) μ := by
  convert hasSubgaussianMGF_of_mem_Icc hm hb using 1 <;> norm_num

theorem subgaussian_two_sided {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (c : ℝ≥0)
    (hX : HasSubgaussianMGF X c μ) (epsilon : ℝ) (he : 0≤epsilon) :
    μ.real {w | epsilon≤|X w|}≤2*Real.exp (-epsilon^2/(2*c)) := by
  have hset : {w | epsilon≤|X w|}=
      {w | epsilon≤X w} ∪ {w | epsilon≤(-X) w} := by
    ext w
    simp only [Set.mem_setOf_eq,Set.mem_union,Pi.neg_apply]
    by_cases hx : 0≤X w
    · rw [abs_of_nonneg hx]
      constructor
      · exact Or.inl
      · rintro (h | h) <;> linarith
    · rw [abs_of_neg (lt_of_not_ge hx)]
      constructor
      · exact Or.inr
      · rintro (h | h) <;> linarith
  rw [hset]
  calc
    μ.real ({w | epsilon≤X w} ∪ {w | epsilon≤(-X) w})≤
      μ.real {w | epsilon≤X w}+μ.real {w | epsilon≤(-X) w} := measureReal_union_le _ _
    _≤2*Real.exp (-epsilon^2/(2*c)) := by
      have h1 := hX.measure_ge_le he
      have h2 := hX.neg.measure_ge_le he
      linarith

theorem bounded_independent_average_hoeffding {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (hn : 0<n)
    (X : Fin n → Ω → ℝ) (m epsilon : ℝ) (he : 0≤epsilon)
    (hInd : iIndepFun X μ) (hm : ∀ i, AEMeasurable (X i) μ)
    (hb : ∀ i, ∀ᵐ w ∂μ, X i w ∈ Set.Icc (0:ℝ) 1)
    (hmean : ∀ i, ∫ w, X i w ∂μ=m) :
    μ.real {w | epsilon≤|(1/(n:ℝ))*∑ i, X i w-m|}≤
      2*Real.exp (-2*(n:ℝ)*epsilon^2) := by
  let Y : Fin n → Ω → ℝ := fun i w => X i w-m
  have hi : iIndepFun Y μ := hInd.comp (fun (_i : Fin n) (x : ℝ) => x-m)
    (fun _ => measurable_id.sub_const m)
  have hsg : ∀ i, HasSubgaussianMGF (Y i) (1/4) μ := by
    intro i
    have h := centered_unit_interval_subgaussian μ (X i) (hm i) (hb i)
    simpa only [hmean i] using h
  have hs : HasSubgaussianMGF (fun w => ∑ i, Y i w) ((n:ℝ≥0)/4) μ := by
    simpa [div_eq_mul_inv] using HasSubgaussianMGF.sum_of_iIndepFun hi
      (s := Finset.univ) (c := fun _ => (1/4:ℝ≥0)) (fun i _ => hsg i)
  have hnreal : (0:ℝ)<n := by exact_mod_cast hn
  have htail := subgaussian_two_sided μ _ _ hs ((n:ℝ)*epsilon) (mul_nonneg hnreal.le he)
  have hset : {w | epsilon≤|(1/(n:ℝ))*∑ i, X i w-m|}=
      {w | (n:ℝ)*epsilon≤|∑ i, Y i w|} := by
    ext w
    simp only [Set.mem_setOf_eq]
    have heq : (1/(n:ℝ))*∑ i, X i w-m=(1/(n:ℝ))*∑ i, Y i w := by
      simp only [Y,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      field_simp
    rw [heq,abs_mul,abs_of_pos (by positivity : (0:ℝ)<1/(n:ℝ))]
    rw [one_div_mul_eq_div,le_div_iff₀ hnreal,mul_comm epsilon (n:ℝ)]
  rw [hset]
  convert htail using 1
  push_cast
  congr 2
  field_simp
  ring

theorem hoeffding_sample_inequality (N delta : ℝ) (hd : 0<delta) :
    2*Real.exp (-N/50)≤delta ↔ 50*Real.log (2/delta)≤N := by
  have hd2 : 0<delta/2 := by positivity
  have he : 2*Real.exp (-N/50)≤delta ↔ Real.exp (-N/50)≤delta/2 := by
    constructor <;> intro h <;> linarith
  rw [he,← Real.exp_log hd2,Real.exp_le_exp]
  have hlog : Real.log (2/delta)=-Real.log (delta/2) := by
    rw [show (2:ℝ)/delta=(delta/2)⁻¹ by field_simp,Real.log_inv]
  rw [hlog]
  constructor <;> intro h <;> linarith

theorem symmetric_bounded_subgaussian {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hm : AEMeasurable X μ) (hb : ∀ᵐ w ∂μ, X w ∈ Set.Icc (-1:ℝ) 1)
    (hc : ∫ w, X w ∂μ=0) : HasSubgaussianMGF X 1 μ := by
  convert hoeffding_lemma μ X (-1) 1 hm hb hc using 1 <;> norm_num [← NNReal.coe_inj]

theorem lookahead_sign_square (epsilon : ℝ) (h : epsilon=-1 ∨ epsilon=1) :
    epsilon*epsilon=1 := by rcases h with (rfl | rfl) <;> norm_num

end SafeLearning.CompleteAppliedConcentration
