import SafeLearning.CompleteAppliedMartingale
import SafeLearning.CompleteAppliedConcentration
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedAdaptiveSigns
open MeasureTheory ProbabilityTheory Filter
open SafeLearning.CompleteAppliedMartingale
open scoped ENNReal NNReal Topology

theorem actual_fair_sign_subgaussian {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (epsilon : Ω → ℝ)
    (hm : Measurable epsilon) (hlaw : HasLaw epsilon fairSignLaw μ) :
    HasSubgaussianMGF epsilon 1 μ := by
  apply SafeLearning.CompleteAppliedConcentration.symmetric_bounded_subgaussian
    μ epsilon hm.aemeasurable
  · filter_upwards [(fair_sign_moments μ epsilon hlaw).2.2] with omega homega
    exact abs_le.mp (le_of_eq homega)
  · exact (fair_sign_moments μ epsilon hlaw).2.1

theorem adaptive_conditional_mgf {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (epsilon : ℕ → Ω → ℝ)
    (hm : ∀ i,Measurable (epsilon i)) (hi : iIndepFun epsilon μ)
    (hlaw : ∀ i,HasLaw (epsilon i) fairSignLaw μ) (n : ℕ) (lambda : ℝ) :
    ∀ᵐ omega ∂μ,
      (μ[fun w => Real.exp (lambda*(predictableMultiplier epsilon n*epsilon n) w) |
        pastFiltration epsilon hm n]) omega≤
      Real.exp (lambda^2*(predictableMultiplier epsilon n omega)^2/2) := by
  let A : Set Ω := {omega | 0≤walk epsilon n omega}
  have hA : MeasurableSet[(pastFiltration epsilon hm n)] A := measurableSet_le measurable_const
    (walk_adapted epsilon hm n).measurable
  have hAg : MeasurableSet A := ((pastFiltration epsilon hm).le n) A hA
  let G1 : Ω → ℝ := fun omega => Real.exp (lambda*epsilon n omega)
  let G2 : Ω → ℝ := fun omega => Real.exp (lambda*(2*epsilon n omega))
  have hs := actual_fair_sign_subgaussian μ (epsilon n) (hm n) (hlaw n)
  have hb2 : ∀ᵐ omega ∂μ,(2:ℝ)*epsilon n omega ∈ Set.Icc (-2:ℝ) 2 := by
    filter_upwards [(fair_sign_moments μ (epsilon n) (hlaw n)).2.2] with omega homega
    obtain ⟨hl,hu⟩ := abs_le.mp (le_of_eq homega)
    constructor <;> linarith
  have hz2 : (∫ omega,(2:ℝ)*epsilon n omega ∂μ)=0 := by
    rw [integral_const_mul,(fair_sign_moments μ (epsilon n) (hlaw n)).2.1,mul_zero]
  have hs2 : HasSubgaussianMGF (fun omega => (2:ℝ)*epsilon n omega) 4 μ := by
    convert SafeLearning.CompleteAppliedConcentration.hoeffding_lemma μ
      (fun omega => (2:ℝ)*epsilon n omega) (-2) 2
      ((hm n).const_mul 2).aemeasurable hb2 hz2 using 1 <;>
      norm_num [← NNReal.coe_inj]
  have hint1 : Integrable G1 μ := hs.integrable_exp_mul lambda
  have hint2 : Integrable G2 μ := hs2.integrable_exp_mul lambda
  have split_exp : (fun w => Real.exp (lambda*(predictableMultiplier epsilon n*epsilon n) w))=
      A.indicator G2+Aᶜ.indicator G1 := by
    ext omega
    by_cases ha : 0≤walk epsilon n omega <;>
      simp [A,G1,G2,predictableMultiplier,ha]
  have hc1 : μ[G1 | (pastFiltration epsilon hm n)]=ᵐ[μ] fun _ => (∫ omega,G1 omega ∂μ) :=
    condExp_indep_eq (hm n).comap_le ((pastFiltration epsilon hm).le n)
      ((comap_measurable (epsilon n)).const_mul lambda).exp.stronglyMeasurable
      (next_sign_independent_past μ epsilon hm hi n)
  have hc2 : μ[G2 | (pastFiltration epsilon hm n)]=ᵐ[μ] fun _ => (∫ omega,G2 omega ∂μ) :=
    condExp_indep_eq (hm n).comap_le ((pastFiltration epsilon hm).le n)
      (((comap_measurable (epsilon n)).const_mul (2:ℝ)).const_mul lambda).exp.stronglyMeasurable
      (next_sign_independent_past μ epsilon hm hi n)
  have hsum := condExp_add (hint2.indicator hAg) (hint1.indicator hAg.compl) (pastFiltration epsilon hm n)
  have hind2 := condExp_indicator hint2 hA
  have hind1 := condExp_indicator hint1 hA.compl
  have hmg1 : (∫ omega,G1 omega ∂μ)≤Real.exp (lambda^2/2) := by
    simpa [G1,mgf] using hs.mgf_le lambda
  have hmg2 : (∫ omega,G2 omega ∂μ)≤Real.exp (4*lambda^2/2) := by
    simpa [G2,mgf] using hs2.mgf_le lambda
  rw [split_exp]
  filter_upwards [hsum,hind2,hind1,hc2,hc1] with omega hadd hi2 hi1 hc2' hc1'
  rw [hadd]
  simp only [Pi.add_apply]
  rw [hi2,hi1]
  by_cases ha : 0≤walk epsilon n omega
  · simpa [A,Set.indicator,ha,predictableMultiplier,hc2',mul_comm,show (2:ℝ)^2=4 by norm_num] using hmg2
  · simpa [A,Set.indicator,ha,predictableMultiplier,hc1'] using hmg1

theorem adaptive_uniform_parameter_two {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (epsilon : ℕ → Ω → ℝ)
    (hm : ∀ i,Measurable (epsilon i)) (hi : iIndepFun epsilon μ)
    (hlaw : ∀ i,HasLaw (epsilon i) fairSignLaw μ) (n : ℕ) (lambda : ℝ) :
    ∀ᵐ omega ∂μ,
      (μ[fun w => Real.exp (lambda*(predictableMultiplier epsilon n*epsilon n) w) |
        pastFiltration epsilon hm n]) omega≤Real.exp (lambda^2*4/2) := by
  filter_upwards [adaptive_conditional_mgf μ epsilon hm hi hlaw n lambda] with omega h
  refine h.trans (Real.exp_le_exp.mpr ?_)
  have ha := (multiplier_measurable_and_bound epsilon hm n).2 omega
  have hs : (predictableMultiplier epsilon n omega)^2≤4 := by
    nlinarith [(abs_le.mp ha.2).1,(abs_le.mp ha.2).2]
  nlinarith [sq_nonneg lambda]

theorem adaptive_exact_magnitude {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (epsilon : ℕ → Ω → ℝ)
    (hm : ∀ i,Measurable (epsilon i))
    (hlaw : ∀ i,HasLaw (epsilon i) fairSignLaw μ) (n : ℕ) :
    ∀ᵐ omega ∂μ,
      |(predictableMultiplier epsilon n*epsilon n) omega|=predictableMultiplier epsilon n omega ∧
      (predictableMultiplier epsilon n*epsilon n) omega ∈
        Set.Icc (-predictableMultiplier epsilon n omega) (predictableMultiplier epsilon n omega) := by
  filter_upwards [(fair_sign_moments μ (epsilon n) (hlaw n)).2.2] with omega homega
  have ha : 0≤predictableMultiplier epsilon n omega :=
    le_trans (by norm_num) ((multiplier_measurable_and_bound epsilon hm n).2 omega).1
  have heq : |(predictableMultiplier epsilon n*epsilon n) omega|=
      predictableMultiplier epsilon n omega := by
    simp only [Pi.mul_apply,abs_mul,homega,mul_one,abs_of_nonneg ha]
  exact ⟨heq,abs_le.mp heq.le⟩

end SafeLearning.CompleteAppliedAdaptiveSigns
