import SafeLearning.CompleteAppliedGaussianCentralConfidence

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal
namespace SafeLearning.CompleteModulesLoSBOGaussianNoise

def actualBoundEvent (bound : ℝ) : Set ℝ := {x | |x| ≤ bound}

theorem actual_nondegenerate_gaussian_has_positive_probability_outside_every_finite_bound
    (bound : ℝ) (variance : NNReal) (hv : variance≠0) :
    0 ≤ (gaussianReal 0 variance).real (actualBoundEvent bound) ∧
      (gaussianReal 0 variance).real (actualBoundEvent bound)<1 := by
  have hmeas : MeasurableSet (actualBoundEvent bound) := by unfold actualBoundEvent; measurability
  have htail : (gaussianReal 0 variance) (Ioi bound)≠0 := by
    intro h
    have hvol := gaussianReal_absolutelyContinuous' 0 hv h
    simp only [Real.volume_Ioi] at hvol
    exact ENNReal.top_ne_zero hvol
  have hsub : Ioi bound ⊆ (actualBoundEvent bound)ᶜ := by
    intro x hx
    change ¬ |x| ≤ bound
    have hx' : bound<x := hx
    linarith [le_abs_self x]
  have hcomp : (gaussianReal 0 variance) ((actualBoundEvent bound)ᶜ)≠0 := by
    intro h
    have hle := measure_mono (μ:=gaussianReal 0 variance) hsub
    rw [h] at hle
    exact htail (le_zero_iff.mp hle)
  have hpos : 0 < (gaussianReal 0 variance).real ((actualBoundEvent bound)ᶜ) :=
    ENNReal.toReal_pos hcomp (measure_ne_top _ _)
  have hsum := probReal_add_probReal_compl (μ:=gaussianReal 0 variance) hmeas
  exact ⟨measureReal_nonneg,by linarith⟩

theorem actual_source_gaussian_interval_probability_is_the_scaled_two_sided_cdf
    (bound : ℝ) (hb : 0 ≤ bound) (sigma : NNReal) (hs : sigma≠0) :
    (gaussianReal 0 (sigma^2)).real (actualBoundEvent bound)=
      2*CompleteAppliedGaussianCDF.standardCDF (bound/(sigma:ℝ))-1 := by
  have hsig : 0 < (sigma:ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hs)
  have hid : HasLaw (id : ℝ → ℝ) (gaussianReal 0 (sigma^2)) (gaussianReal 0 (sigma^2)) :=
    ⟨measurable_id.aemeasurable,by simp⟩
  have hz := gaussianReal_div_const hid (sigma:ℝ)
  have hm : NNReal.mk ((sigma:ℝ)^2) (sq_nonneg (sigma:ℝ))=sigma^2 := by ext; rfl
  rw [hm,div_self (pow_ne_zero 2 hs)] at hz
  norm_num only [zero_div] at hz
  have hp := hz.measureReal_eq (p:=fun x:ℝ => |x|≤bound/(sigma:ℝ)) (by measurability)
  have he : {x:ℝ | |x/(sigma:ℝ)|≤bound/(sigma:ℝ)}=actualBoundEvent bound := by
    ext x
    simp only [mem_setOf_eq,actualBoundEvent,abs_div,abs_of_pos hsig]
    exact div_le_div_iff_of_pos_right hsig
  change (gaussianReal 0 (sigma^2)).real {x:ℝ | |x/(sigma:ℝ)|≤bound/(sigma:ℝ)}=_ at hp
  rw [he,CompleteAppliedGaussianCentralConfidence.actual_central_standard_gaussian_probability _ (div_nonneg hb hsig.le)] at hp
  exact hp

theorem actual_independent_gaussian_first_T_noise_bounds_have_probability_p_power_T
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (noise : ℕ → Ω → ℝ) (hind : iIndepFun noise P)
    (variance : NNReal) (hlaw : ∀ n, HasLaw (noise n) (gaussianReal 0 variance) P)
    (bound : ℝ) (T : ℕ) :
    P.real {ω | ∀ n < T, |noise n ω|≤bound}=
      ((gaussianReal 0 variance).real (actualBoundEvent bound))^T := by
  have hm : ∀ n, MeasurableSet[(borel ℝ).comap (noise n)] {ω | |noise n ω|≤bound} := by
    intro n
    exact MeasurableSet.preimage (by unfold actualBoundEvent; measurability : MeasurableSet (actualBoundEvent bound)) (comap_measurable (noise n))
  have hi := hind.meas_biInter (S:=Finset.range T) (s:=fun n => {ω | |noise n ω|≤bound}) (fun n _ => hm n)
  have he : (⋂ n∈Finset.range T, {ω | |noise n ω|≤bound})={ω | ∀ n<T, |noise n ω|≤bound} := by
    ext ω
    simp
  rw [he] at hi
  have hp : ∀ n, P {ω | |noise n ω|≤bound}=(gaussianReal 0 variance) (actualBoundEvent bound) :=
    fun n => (hlaw n).measure_eq (p:=fun x:ℝ => |x|≤bound) (by measurability)
  simp only [hp,Finset.prod_const,Finset.card_range] at hi
  simpa only [Measure.real,ENNReal.toReal_pow] using congrArg ENNReal.toReal hi

theorem actual_nondegenerate_independent_gaussian_finite_bound_success_probabilities_tend_to_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (noise : ℕ → Ω → ℝ) (hind : iIndepFun noise P)
    (variance : NNReal) (hv : variance≠0) (hlaw : ∀ n, HasLaw (noise n) (gaussianReal 0 variance) P)
    (bound : ℝ) :
    Tendsto (fun T => P.real {ω | ∀ n<T, |noise n ω|≤bound}) atTop (𝓝 0) := by
  simp_rw [actual_independent_gaussian_first_T_noise_bounds_have_probability_p_power_T P noise hind variance hlaw bound]
  obtain ⟨hp,hp1⟩ := actual_nondegenerate_gaussian_has_positive_probability_outside_every_finite_bound bound variance hv
  exact tendsto_pow_atTop_nhds_zero_of_lt_one hp hp1

theorem actual_nondegenerate_independent_gaussian_eventually_exceeds_each_chosen_finite_fixed_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (noise : ℕ → Ω → ℝ) (hmeas : ∀ n, Measurable (noise n)) (hind : iIndepFun noise P)
    (variance : NNReal) (hv : variance≠0) (hlaw : ∀ n, HasLaw (noise n) (gaussianReal 0 variance) P)
    (bound : ℝ) :
    P.real {ω | ∀ n, |noise n ω|≤bound}=0 ∧
      P.real {ω | ∃ n, bound < |noise n ω|}=1 := by
  have ht := actual_nondegenerate_independent_gaussian_finite_bound_success_probabilities_tend_to_zero P noise hind variance hv hlaw bound
  have hle : P.real {ω | ∀ n, |noise n ω|≤bound} ≤ 0 := by
    apply ge_of_tendsto ht
    exact Filter.Eventually.of_forall (fun T => measureReal_mono (fun ω h n _ => h n))
  have hz : P.real {ω | ∀ n, |noise n ω|≤bound}=0 := le_antisymm hle measureReal_nonneg
  have hs : MeasurableSet {ω | ∀ n, |noise n ω|≤bound} := by
    have he : {ω | ∀ n, |noise n ω|≤bound}=⋂ n, (noise n) ⁻¹' actualBoundEvent bound := by ext ω; simp [actualBoundEvent]
    rw [he]
    exact MeasurableSet.iInter (fun n => (by unfold actualBoundEvent; measurability : MeasurableSet (actualBoundEvent bound)).preimage (hmeas n))
  have hc := probReal_add_probReal_compl (μ:=P) hs
  have he : {ω | ∀ n, |noise n ω|≤bound}ᶜ={ω | ∃ n, bound < |noise n ω|} := by ext ω; simp
  rw [he,hz] at hc
  exact ⟨hz,by linarith⟩

end SafeLearning.CompleteModulesLoSBOGaussianNoise
