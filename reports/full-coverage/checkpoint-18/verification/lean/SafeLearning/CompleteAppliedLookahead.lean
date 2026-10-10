import SafeLearning.CompleteAppliedMartingale
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedLookahead
open MeasureTheory ProbabilityTheory Filter
open SafeLearning.CompleteAppliedMartingale
open scoped ENNReal NNReal Topology

theorem actual_lookahead_increment_one {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (epsilon : Ω → ℝ)
    (hlaw : HasLaw epsilon fairSignLaw μ) :
    epsilon*epsilon =ᵐ[μ] (1 : Ω → ℝ) := by
  filter_upwards [(fair_sign_moments μ epsilon hlaw).2.2] with omega homega
  simp only [Pi.mul_apply,Pi.one_apply]
  rw [← pow_two,← sq_abs,homega]
  norm_num

theorem actual_lookahead_conditional_mean_one {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (epsilon : Ω → ℝ) (hlaw : HasLaw epsilon fairSignLaw μ) :
    μ[epsilon*epsilon | m] =ᵐ[μ] (1 : Ω → ℝ) := by
  letI : MeasurableSpace Ω := mΩ
  refine (condExp_congr_ae (actual_lookahead_increment_one μ epsilon hlaw)).trans ?_
  change μ[(fun _ => (1:ℝ)) | m] =ᵐ[μ] fun _ => 1
  rw [condExp_const hm]

def lookaheadWalk {Ω : Type*} (epsilon : ℕ → Ω → ℝ) (n : ℕ) (omega : Ω) : ℝ :=
  ∑ i ∈ Finset.range n,epsilon i omega*epsilon i omega

theorem actual_lookahead_accumulation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (epsilon : ℕ → Ω → ℝ)
    (hlaw : ∀ i,HasLaw (epsilon i) fairSignLaw μ) :
    ∀ᵐ omega ∂μ,∀ n,lookaheadWalk epsilon n omega=(n:ℝ) := by
  filter_upwards [ae_all_iff.mpr (fun i => actual_lookahead_increment_one μ (epsilon i) (hlaw i))]
    with omega homega n
  simp only [lookaheadWalk]
  have hsum : (∑ i ∈ Finset.range n,epsilon i omega*epsilon i omega)=
      ∑ _i ∈ Finset.range n,(1:ℝ) := by
    apply Finset.sum_congr rfl
    intro i _
    exact homega i
  rw [hsum]
  simp

theorem lookahead_not_known_from_past {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (epsilon : ℕ → Ω → ℝ)
    (hm : ∀ i,Measurable (epsilon i)) (hi : iIndepFun epsilon μ)
    (hlaw : ∀ i,HasLaw (epsilon i) fairSignLaw μ) (n : ℕ) :
    ¬ StronglyMeasurable[pastFiltration epsilon hm n] (epsilon n) := by
  intro hknown
  have hself := condExp_of_stronglyMeasurable ((pastFiltration epsilon hm).le n)
    hknown (fair_sign_moments μ (epsilon n) (hlaw n)).1
  have hz := next_conditional_mean_zero μ epsilon hm hi hlaw n
  have hf : ∀ᵐ omega ∂μ,False := by
    filter_upwards [hz,(fair_sign_moments μ (epsilon n) (hlaw n)).2.2] with omega hzero habs
    rw [hself] at hzero
    simp only [Pi.zero_apply] at hzero
    norm_num [hzero] at habs
  exact (Filter.Eventually.exists hf).choose_spec

theorem actual_lookahead_walk_not_martingale {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (epsilon : ℕ → Ω → ℝ)
    (hm : ∀ i,Measurable (epsilon i))
    (hlaw : ∀ i,HasLaw (epsilon i) fairSignLaw μ) :
    ¬ Martingale (lookaheadWalk epsilon) (pastFiltration epsilon hm) μ := by
  intro hmart
  have hone : lookaheadWalk epsilon 1 =ᵐ[μ] (1 : Ω → ℝ) := by
    filter_upwards [actual_lookahead_accumulation μ epsilon hlaw] with omega homega
    simpa using homega 1
  have hc : μ[lookaheadWalk epsilon 1 | pastFiltration epsilon hm 0]=ᵐ[μ]
      (1:Ω → ℝ) := by
    refine (condExp_congr_ae hone).trans ?_
    change μ[(fun _ => (1:ℝ)) | pastFiltration epsilon hm 0] =ᵐ[μ] fun _ => 1
    rw [condExp_const ((pastFiltration epsilon hm).le 0)]
  have hm0 := hmart.2 0 1 (by omega)
  have hf : ∀ᵐ omega ∂μ,False := by
    filter_upwards [hc,hm0] with omega hcone hmartone
    simp [lookaheadWalk] at hmartone
    simp only [Pi.one_apply] at hcone
    linarith
  exact (Filter.Eventually.exists hf).choose_spec

end SafeLearning.CompleteAppliedLookahead
