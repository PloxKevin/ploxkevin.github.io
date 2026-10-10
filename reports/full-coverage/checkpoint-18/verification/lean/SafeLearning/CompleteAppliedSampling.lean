import SafeLearning.CompleteAppliedProbability
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedSampling
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

def bernoulliTrial : Measure ℝ := bernoulliMeasure 1 0 ⟨1/5,by norm_num⟩

instance bernoulli_trial_probability : IsProbabilityMeasure bernoulliTrial := by
  unfold bernoulliTrial
  infer_instance

theorem bernoulli_trial_bounded : ∀ᵐ x ∂bernoulliTrial,x ∈ Set.Icc (0:ℝ) 1 := by
  unfold bernoulliTrial
  rw [bernoulliMeasure_def,ae_add_measure_iff]
  constructor <;> apply Measure.ae_smul_measure
  all_goals simp [ae_dirac_eq]

theorem bernoulli_trial_moments :
    (∫ x,x ∂bernoulliTrial)=1/5 ∧ variance (fun x : ℝ => x) bernoulliTrial=4/25 := by
  have hmem : MemLp (fun x : ℝ => x) 2 bernoulliTrial :=
    memLp_of_bounded bernoulli_trial_bounded (by fun_prop) 2
  constructor
  · norm_num [bernoulliTrial,integral_bernoulliMeasure]
  · rw [variance_eq_sub hmem]
    norm_num [bernoulliTrial,integral_bernoulliMeasure]

theorem bernoulli_random_variable_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : HasLaw X bernoulliTrial μ) :
    MemLp X 2 μ ∧ (∫ omega,X omega ∂μ)=1/5 ∧ variance X μ=4/25 := by
  have hb : ∀ᵐ omega ∂μ,X omega ∈ Set.Icc (0:ℝ) 1 :=
    (hX.ae_iff (measurableSet_Icc.mem : Measurable (fun x : ℝ => x ∈ Set.Icc (0:ℝ) 1))).mpr
      bernoulli_trial_bounded
  refine ⟨memLp_of_bounded hb hX.aemeasurable.aestronglyMeasurable 2,?_,?_⟩
  · rw [hX.integral_eq]
    exact bernoulli_trial_moments.1
  · rw [hX.variance_eq]
    exact bernoulli_trial_moments.2

theorem bernoulli_average_mean_and_variance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (hn : 0<n)
    (X : Fin n → Ω → ℝ) (hi : iIndepFun X μ)
    (hLaw : ∀ i,HasLaw (X i) bernoulliTrial μ) :
    (∫ omega,(1/(n:ℝ))*∑ i,X i omega ∂μ)=1/5 ∧
    variance (fun omega => (1/(n:ℝ))*∑ i,X i omega) μ=(4/25)/(n:ℝ) := by
  have hm := fun i => (bernoulli_random_variable_moments μ (X i) (hLaw i)).1
  have hmean := fun i => (bernoulli_random_variable_moments μ (X i) (hLaw i)).2.1
  have hv := fun i => (bernoulli_random_variable_moments μ (X i) (hLaw i)).2.2
  constructor
  · rw [integral_const_mul,integral_finsetSum Finset.univ
      (fun i _ => (hm i).integrable (by norm_num))]
    simp_rw [hmean]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have hn0 : (n:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn)
    field_simp
  · exact SafeLearning.CompleteAppliedProbability.independent_average_variance μ n hn X
      hm (fun i j hij => hi.indepFun hij) (4/25) hv

def duplicatedAverage {Ω : Type*} (Z : Fin 50 → Ω → ℝ) (omega : Ω) : ℝ :=
  (1/100)*(∑ i : Fin 2 × Fin 50,Z i.2 omega)

theorem duplicated_average_identity {Ω : Type*} (Z : Fin 50 → Ω → ℝ) :
    duplicatedAverage Z=(fun omega => (1/50)*∑ i,Z i omega) := by
  ext omega
  unfold duplicatedAverage
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  ring

theorem source_copied_vs_independent {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Fin 100 → Ω → ℝ)
    (Z : Fin 50 → Ω → ℝ) (hi : iIndepFun X μ) (hz : iIndepFun Z μ)
    (hX : ∀ i,HasLaw (X i) bernoulliTrial μ)
    (hZ : ∀ i,HasLaw (Z i) bernoulliTrial μ) :
    (∫ omega,(1/100)*∑ i,X i omega ∂μ)=1/5 ∧
    (∫ omega,duplicatedAverage Z omega ∂μ)=1/5 ∧
    variance (fun omega => (1/100)*∑ i,X i omega) μ=1/625 ∧
    variance (duplicatedAverage Z) μ=2/625 := by
  have hx := bernoulli_average_mean_and_variance μ 100 (by omega) X hi hX
  have hz' := bernoulli_average_mean_and_variance μ 50 (by omega) Z hz hZ
  rw [duplicated_average_identity]
  norm_num at hx hz' ⊢
  exact ⟨hx.1,hz'.1,hx.2,hz'.2⟩

theorem source_standard_deviations :
    Real.sqrt (1/625:ℝ)=1/25 ∧
    (56565/1000000:ℝ)<Real.sqrt (2/625:ℝ) ∧
    Real.sqrt (2/625:ℝ)<56575/1000000 := by
  constructor
  · rw [show (1/625:ℝ)=(1/25:ℝ)^2 by norm_num,Real.sqrt_sq (by norm_num)]
  · have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤2/625)
    have hn := Real.sqrt_nonneg (2/625:ℝ)
    constructor <;> nlinarith

end SafeLearning.CompleteAppliedSampling
