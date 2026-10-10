import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace SafeLearning.CompleteAppliedMeasuresIntegrals

theorem actual_measure_is_countably_additive_on_disjoint_legitimate_events
    {alpha : Type*} [MeasurableSpace alpha] (mu : Measure alpha)
    (A : ℕ → Set alpha) (hA : ∀ n,MeasurableSet (A n))
    (hd : Pairwise (fun i j => Disjoint (A i) (A j))) :
    mu (⋃ n,A n)=∑' n,mu (A n) := measure_iUnion hd hA

theorem actual_counting_integral_is_the_countable_sum
    {alpha : Type*} [MeasurableSpace alpha] [MeasurableSingletonClass alpha] [Countable alpha]
    (f : alpha → ℝ) (hi : Integrable f Measure.count) :
    (∫ x,f x ∂Measure.count)=∑' x,f x := by
  rw [integral_countable hi]
  simp only [measureReal_def,Measure.count_apply_singleton,ENNReal.toReal_one,one_smul]

theorem actual_general_normalized_density_is_a_probability_measure
    {alpha : Type*} [MeasurableSpace alpha] (mu : Measure alpha)
    (p : alpha → ℝ≥0∞) (hp : (∫⁻ x,p x ∂mu)=1) :
    IsProbabilityMeasure (mu.withDensity p) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,hp]

theorem actual_general_density_event_probability_is_the_reference_integral
    {alpha : Type*} [MeasurableSpace alpha] (mu : Measure alpha)
    (p : alpha → ℝ≥0∞) (A : Set alpha) (hA : MeasurableSet A) :
    mu.withDensity p A=∫⁻ x in A,p x ∂mu := withDensity_apply p hA

theorem actual_general_density_expectation_is_the_weighted_reference_integral
    {alpha : Type*} [MeasurableSpace alpha] (mu : Measure alpha)
    (p : alpha → ℝ≥0∞) (hp : Measurable p) (hf : ∀ᵐ x ∂mu,p x<⊤)
    (g : alpha → ℝ) :
    (∫ x,g x ∂mu.withDensity p)=∫ x,(p x).toReal*g x ∂mu := by
  simpa only [smul_eq_mul] using integral_withDensity_eq_integral_toReal_smul hp hf

theorem actual_countable_probability_mass_function_is_a_density_for_counting_measure
    {alpha : Type*} [MeasurableSpace alpha] [MeasurableSingletonClass alpha] [Countable alpha]
    (p : PMF alpha) :
    p.toMeasure=Measure.count.withDensity p := by
  apply Measure.ext
  intro A hA
  rw [withDensity_apply p hA,←lintegral_indicator hA,lintegral_count,
    PMF.toMeasure_apply_eq_toOuterMeasure_apply p hA,PMF.toOuterMeasure_apply]

def mixedLaw : Measure ℝ :=
  (1/2:ℝ≥0∞) • Measure.dirac 0+(1/2:ℝ≥0∞) • volume.restrict (Ioc 0 1)

theorem actual_mixed_atom_and_density_law_is_normalized : IsProbabilityMeasure mixedLaw := by
  constructor
  norm_num [mixedLaw,Measure.add_apply,Measure.smul_apply,Measure.restrict_apply,
    Real.volume_Ioc]

theorem actual_mixed_law_has_half_atom_and_half_positive_density_mass :
    mixedLaw {0}=1/2 ∧ mixedLaw (Ioi 0)=1/2 := by
  constructor
  · norm_num [mixedLaw,Measure.add_apply,Measure.smul_apply,Measure.restrict_apply,
      Measure.dirac_apply',Set.inter_def]
  · have he : Ioi (0:ℝ) ∩ Ioc 0 1=Ioc 0 1 := by
      exact inter_eq_right.mpr (fun _ h => h.1)
    norm_num [mixedLaw,Measure.add_apply,Measure.smul_apply,Measure.restrict_apply,
      Measure.dirac_apply',he,Real.volume_Ioc]

theorem actual_mixed_law_has_zero_mass_at_every_positive_singleton (x : ℝ) (hx : 0<x) :
    mixedLaw {x}=0 := by
  norm_num [mixedLaw,Measure.add_apply,Measure.smul_apply,Measure.restrict_apply,
    Measure.dirac_apply',ne_of_gt hx]

theorem actual_mixed_law_has_no_density_with_respect_to_lebesgue_measure :
    ¬∃ p : ℝ → ℝ≥0∞,mixedLaw=volume.withDensity p := by
  rintro ⟨p,hp⟩
  have ha := actual_mixed_law_has_half_atom_and_half_positive_density_mass.1
  rw [hp,withDensity_apply p (measurableSet_singleton _)] at ha
  simp only [Measure.restrict_singleton,measure_singleton,zero_smul,lintegral_zero_measure] at ha
  norm_num at ha

theorem actual_mixed_law_has_no_density_with_respect_to_counting_measure :
    ¬∃ p : ℝ → ℝ≥0∞,mixedLaw=Measure.count.withDensity p := by
  rintro ⟨p,hp⟩
  have hz : ∀ x∈Ioi (0:ℝ),p x=0 := by
    intro x hx
    have hs := actual_mixed_law_has_zero_mass_at_every_positive_singleton x hx
    rw [hp,withDensity_apply p (measurableSet_singleton _),lintegral_singleton] at hs
    simpa only [Measure.count_apply_singleton,mul_one] using hs
  have ha := actual_mixed_law_has_half_atom_and_half_positive_density_mass.2
  rw [hp,withDensity_apply p measurableSet_Ioi] at ha
  have he : (∫⁻ x in Ioi (0:ℝ),p x ∂Measure.count)=0 := by
    rw [←lintegral_indicator measurableSet_Ioi,lintegral_count]
    apply tsum_eq_zero
    intro x
    by_cases hx : x∈Ioi (0:ℝ)
    · simp [hx,hz x hx]
    · simp [hx]
  rw [he] at ha
  norm_num at ha

end SafeLearning.CompleteAppliedMeasuresIntegrals
