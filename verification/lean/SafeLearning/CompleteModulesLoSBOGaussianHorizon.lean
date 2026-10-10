import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
namespace SafeLearning.CompleteModulesLoSBOGaussianHorizon

theorem actual_centered_gaussian_law_has_its_genuine_subgaussian_mgf
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ) (variance : ℝ≥0)
    (hlaw : HasLaw X (gaussianReal 0 variance) P) : HasSubgaussianMGF X variance P := by
  have hg : HasSubgaussianMGF id variance (gaussianReal 0 variance) := by
    constructor
    · intro t
      exact integrable_exp_mul_gaussianReal t
    · intro t
      simp only [mgf_id_gaussianReal,zero_mul,zero_add,le_refl]
  rw [←HasSubgaussianMGF.id_map_iff hlaw.aemeasurable,hlaw.map_eq]
  exact hg

theorem actual_gaussian_two_sided_tail_has_the_literal_exponential_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (variance : ℝ≥0) (hlaw : HasLaw X (gaussianReal 0 variance) P)
    (radius : ℝ) (hr : 0 ≤ radius) :
    P.real {omega | radius < |X omega|} ≤ 2*Real.exp (-radius^2/(2*(variance:ℝ))) := by
  have hg := actual_centered_gaussian_law_has_its_genuine_subgaussian_mgf P X variance hlaw
  have hsub : {omega | radius < |X omega|} ⊆
      {omega | radius ≤ X omega} ∪ {omega | radius ≤ -X omega} := by
    intro omega ho
    change radius < |X omega| at ho
    rcases lt_abs.mp ho with ho | ho
    · exact Or.inl ho.le
    · exact Or.inr ho.le
  calc
    _ ≤ P.real ({omega | radius ≤ X omega} ∪ {omega | radius ≤ -X omega}) := measureReal_mono hsub
    _ ≤ P.real {omega | radius ≤ X omega}+P.real {omega | radius ≤ -X omega} := measureReal_union_le _ _
    _ ≤ Real.exp (-radius^2/(2*(variance:ℝ)))+Real.exp (-radius^2/(2*(variance:ℝ))) :=
      add_le_add (hg.measure_ge_le hr) (hg.neg.measure_ge_le hr)
    _ = _ := by ring

def actualHorizonRadius (sigma : ℝ≥0) (horizon : ℕ) (delta : ℝ) : ℝ :=
  (sigma:ℝ)*Real.sqrt (2*Real.log (2*(horizon:ℝ)/delta))

theorem actual_horizon_radius_gives_the_exact_delta_tail_allocation
    (sigma : ℝ≥0) (hs : 0 < sigma) (horizon : ℕ) (ht : 1 ≤ horizon)
    (delta : ℝ) (hd : 0 < delta) (hd1 : delta ≤ 1) :
    0 ≤ actualHorizonRadius sigma horizon delta ∧
      (horizon:ℝ)*2*Real.exp (-(actualHorizonRadius sigma horizon delta)^2/(2*(sigma:ℝ)^2))=delta := by
  have htr : (1:ℝ) ≤ horizon := by exact_mod_cast ht
  have hsp : 0 < (sigma:ℝ) := hs
  have hp : 0 < 2*(horizon:ℝ)/delta := by positivity
  have hratio : 1 ≤ 2*(horizon:ℝ)/delta := (le_div_iff₀ hd).mpr (by linarith)
  have hlog := Real.log_nonneg hratio
  have hsq := Real.sq_sqrt (mul_nonneg (by norm_num : (0:ℝ)≤2) hlog)
  have he : -(actualHorizonRadius sigma horizon delta)^2/(2*(sigma:ℝ)^2)=
      -Real.log (2*(horizon:ℝ)/delta) := by
    dsimp [actualHorizonRadius]
    rw [mul_pow,hsq]
    field_simp
  refine ⟨by dsimp [actualHorizonRadius];positivity,?_⟩
  rw [he,Real.exp_neg,Real.exp_log hp]
  field_simp

theorem actual_all_horizon_gaussian_noise_exceedance_probability_is_at_most_delta
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (horizon : ℕ) (ht : 1 ≤ horizon) (noise : Fin horizon → Ω → ℝ)
    (sigma : ℝ≥0) (hs : 0 < sigma) (delta : ℝ) (hd : 0 < delta) (hd1 : delta ≤ 1)
    (hlaw : ∀ t, HasLaw (noise t) (gaussianReal 0 (sigma^2)) P) :
    P.real {omega | ∃ t, actualHorizonRadius sigma horizon delta < |noise t omega|} ≤ delta := by
  have hb := actual_horizon_radius_gives_the_exact_delta_tail_allocation sigma hs horizon ht delta hd hd1
  have he : {omega | ∃ t, actualHorizonRadius sigma horizon delta < |noise t omega|}=
      ⋃ t, {omega | actualHorizonRadius sigma horizon delta < |noise t omega|} := by ext omega;simp
  rw [he]
  calc
    _ ≤ ∑ t, P.real {omega | actualHorizonRadius sigma horizon delta < |noise t omega|} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _t : Fin horizon, 2*Real.exp (-(actualHorizonRadius sigma horizon delta)^2/(2*(sigma:ℝ)^2)) := by
      apply Finset.sum_le_sum
      intro t _
      simpa only [NNReal.coe_pow] using actual_gaussian_two_sided_tail_has_the_literal_exponential_bound
        P (noise t) (sigma^2) (hlaw t) (actualHorizonRadius sigma horizon delta) hb.1
    _ = delta := by simpa [mul_assoc] using hb.2

end SafeLearning.CompleteModulesLoSBOGaussianHorizon
