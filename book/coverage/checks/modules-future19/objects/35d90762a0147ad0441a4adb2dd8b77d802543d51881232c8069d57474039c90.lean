import SafeLearning.CompleteAppliedConditionalLaw
import Mathlib.Probability.Martingale.Basic
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedAzuma
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

def realConditionalLaw {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (m : MeasurableSpace Ω) (Y : Ω → ℝ) :
    @Kernel Ω ℝ m inferInstance :=
  @condDistrib Ω Ω ℝ inferInstance inferInstance inferInstance mΩ m Y id μ inferInstance

instance realConditionalLaw_markov {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (m : MeasurableSpace Ω) (Y : Ω → ℝ) :
    IsMarkovKernel (@realConditionalLaw Ω mΩ μ inferInstance m Y) := by
  unfold realConditionalLaw
  infer_instance

def RealConditionalSubGaussian {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (Y : Ω → ℝ) (c : ℝ≥0) : Prop :=
  Kernel.HasSubgaussianMGF id c ((@realConditionalLaw Ω mΩ μ inferInstance m Y)) (μ.trim hm)

theorem real_conditional_law_comp {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (Y : Ω → ℝ) (hY : @Measurable Ω ℝ mΩ inferInstance Y) :
    (@realConditionalLaw Ω mΩ μ inferInstance m Y) ∘ₘ μ.trim hm = @Measure.map Ω ℝ mΩ inferInstance Y μ := by
  letI : MeasurableSpace Ω := mΩ
  rw [realConditionalLaw,trim_eq_map]
  exact condDistrib_comp_map (mβ := m)
    (@Measurable.aemeasurable Ω Ω mΩ m id μ (measurable_id'' hm)) hY.aemeasurable

theorem bounded_centered_is_real_conditional_subgaussian {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (Y : Ω → ℝ) (hY : @Measurable Ω ℝ mΩ inferInstance Y) (R : ℝ≥0)
    (hb : ∀ᵐ omega ∂μ,Y omega ∈ Set.Icc (-(R:ℝ)) R)
    (hz : μ[Y | m]=ᵐ[μ] 0) : (@RealConditionalSubGaussian Ω mΩ μ inferInstance m hm Y) (R^2) := by
  letI : MeasurableSpace Ω := mΩ
  have hi : Integrable Y μ := (memLp_of_bounded hb hY.aestronglyMeasurable 2).integrable (by norm_num)
  have hmean : μ[Y | m]=ᵐ[μ] fun omega => ∫ y,y ∂(@realConditionalLaw Ω mΩ μ inferInstance m Y) omega := by
    simpa only [MeasurableSpace.comap_id,id_eq,realConditionalLaw] using
      condExp_ae_eq_integral_condDistrib (mβ := m) (measurable_id'' hm)
        hY.aemeasurable stronglyMeasurable_id hi
  have hright : StronglyMeasurable[m]
      (fun omega => ∫ y,y ∂(@realConditionalLaw Ω mΩ μ inferInstance m Y) omega) := by
    have hg := stronglyMeasurable_integral_condDistrib (X := id) (Y := Y) (μ := μ) (mβ := m)
      (@measurable_snd Ω ℝ m inferInstance).stronglyMeasurable
    rw [MeasurableSpace.comap_id] at hg
    exact hg
  have hmt := (StronglyMeasurable.ae_eq_trim_iff hm stronglyMeasurable_condExp hright).mpr hmean
  have hzt := (StronglyMeasurable.ae_eq_trim_iff hm stronglyMeasurable_condExp
    stronglyMeasurable_zero).mpr hz
  have hzero : ∀ᵐ omega ∂μ.trim hm,(∫ y,y ∂(@realConditionalLaw Ω mΩ μ inferInstance m Y) omega)=0 := by
    filter_upwards [hmt,hzt] with omega he hzero
    exact he.symm.trans hzero
  have hbound : ∀ᵐ omega ∂μ.trim hm,
      ∀ᵐ y ∂(@realConditionalLaw Ω mΩ μ inferInstance m Y) omega,y ∈ Set.Icc (-(R:ℝ)) R := by
    apply Measure.ae_ae_of_ae_comp
    rw [real_conditional_law_comp μ m hm Y hY]
    exact (ae_map_iff hY.aemeasurable measurableSet_Icc).mpr hb
  refine ⟨?_,?_⟩
  · intro lambda
    rw [real_conditional_law_comp μ m hm Y hY]
    apply (integrable_map_measure
      ((measurable_const.mul measurable_id).exp.aestronglyMeasurable) hY.aemeasurable).mpr
    exact integrable_exp_mul_of_mem_Icc hY.aemeasurable hb
  · filter_upwards [hzero,hbound] with omega hzero hbound lambda
    have hh := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (measurable_id.aemeasurable (μ := (@realConditionalLaw Ω mΩ μ inferInstance m Y) omega)) hbound hzero
    have hp : (‖(R:ℝ)-(-(R:ℝ))‖₊/2)^2=R^2 := by
      apply NNReal.coe_injective
      simp only [NNReal.coe_pow,NNReal.coe_div,coe_nnnorm,NNReal.coe_ofNat]
      rw [Real.norm_eq_abs,abs_of_nonneg (by linarith [R.property])]
      ring
    rw [hp] at hh
    exact hh.mgf_le lambda

theorem add_real_conditional_subgaussian {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (X Y : Ω → ℝ) (hX : @Measurable Ω ℝ m inferInstance X)
    (hY : @Measurable Ω ℝ mΩ inferInstance Y) (cX cY : ℝ≥0)
    (hsgX : HasSubgaussianMGF X cX μ) (hsgY : (@RealConditionalSubGaussian Ω mΩ μ inferInstance m hm Y) cY) :
    HasSubgaussianMGF (X+Y) (cX+cY) μ := by
  letI : MeasurableSpace Ω := mΩ
  have hXt : HasSubgaussianMGF X cX (μ.trim hm) := hsgX.trim hm hX
  have hxk := HasSubgaussianMGF_iff_kernel.mp hXt
  have hyk : Kernel.HasSubgaussianMGF id cY ((@realConditionalLaw Ω mΩ μ inferInstance m Y))
      (Kernel.const Unit (μ.trim hm) ∘ₘ Measure.dirac ()) := by simpa [RealConditionalSubGaussian] using hsgY
  have hadd := hxk.add_comp hyk
  have hprod : HasSubgaussianMGF (fun p : Ω × ℝ => X p.1+p.2) (cX+cY)
      ((μ.trim hm) ⊗ₘ (@realConditionalLaw Ω mΩ μ inferInstance m Y)) := by
    rw [HasSubgaussianMGF_iff_kernel]
    convert hadd using 1
    · rfl
    · rfl
  have heq : ((μ.trim hm) ⊗ₘ (@realConditionalLaw Ω mΩ μ inferInstance m Y))=
      @Measure.map Ω (Ω×ℝ) mΩ (m.prod inferInstance) (fun omega => (omega,Y omega)) μ := by
    rw [realConditionalLaw,trim_eq_map]
    exact compProd_map_condDistrib
      (@Measurable.aemeasurable Ω Ω mΩ m id μ (measurable_id'' hm)) hY.aemeasurable
  rw [heq] at hprod
  have hmap : @AEMeasurable Ω (Ω×ℝ) (m.prod inferInstance) mΩ
      (fun omega => (omega,Y omega)) μ :=
    @Measurable.aemeasurable Ω (Ω×ℝ) mΩ (m.prod inferInstance)
      (fun omega => (omega,Y omega)) μ ((measurable_id'' hm).prodMk hY)
  have hh := @HasSubgaussianMGF.of_map (Ω×ℝ) (m.prod inferInstance) (cX+cY)
    Ω mΩ μ (fun omega => (omega,Y omega)) (fun p => X p.1+p.2) hmap hprod
  simpa only [Function.comp_def,Pi.add_def] using hh

def partialSum {Ω : Type*} (Y : ℕ → Ω → ℝ) (n : ℕ) (omega : Ω) : ℝ :=
  ∑ i ∈ Finset.range n,Y i omega

theorem partialSum_initial_step {Ω : Type*} (Y : ℕ → Ω → ℝ) (n : ℕ) :
    partialSum Y 0=0 ∧ partialSum Y (n+1)=partialSum Y n+Y n := by
  constructor
  · ext omega;simp [partialSum]
  · ext omega;simp [partialSum,Finset.sum_range_succ]

theorem partialSum_adapted {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (F : Filtration ℕ mΩ) (Y : ℕ → Ω → ℝ)
    (hY : ∀ i,StronglyMeasurable[F (i+1)] (Y i)) : StronglyAdapted F (partialSum Y) := by
  intro n
  have hs : StronglyMeasurable[F n] (∑ i ∈ Finset.range n,Y i) := by
    apply Finset.stronglyMeasurable_sum
    intro i hi
    have hi' := Finset.mem_range.mp hi
    exact (hY i).mono (F.mono (by omega))
  change StronglyMeasurable[F n] (fun omega => ∑ i ∈ Finset.range n,Y i omega)
  simpa only [Finset.sum_fn] using hs

theorem actual_azuma_sum_subgaussian {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (Y : ℕ → Ω → ℝ) (hY : ∀ i,StronglyMeasurable[F (i+1)] (Y i)) (R : ℝ≥0)
    (hcond : ∀ i,RealConditionalSubGaussian μ (F i) (F.le i) (Y i) (R^2)) (n : ℕ) :
    HasSubgaussianMGF (partialSum Y n) ((n:ℝ≥0)*R^2) μ := by
  induction n with
  | zero => simpa [(partialSum_initial_step Y 0).1] using
      (show HasSubgaussianMGF (0:Ω → ℝ) 0 μ from HasSubgaussianMGF.zero)
  | succ n hn =>
    have hm : Measurable (Y n) := ((hY n).mono (F.le (n+1))).measurable
    have hh := add_real_conditional_subgaussian μ (F n) (F.le n)
      (partialSum Y n) (Y n) (partialSum_adapted F Y hY n).measurable hm
      ((n:ℝ≥0)*R^2) (R^2) hn (hcond n)
    simpa only [(partialSum_initial_step Y n).2,Nat.cast_add,Nat.cast_one,add_mul,one_mul] using hh

theorem actual_azuma_tail {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (Y : ℕ → Ω → ℝ) (hY : ∀ i,StronglyMeasurable[F (i+1)] (Y i)) (R : ℝ≥0)
    (hcond : ∀ i,RealConditionalSubGaussian μ (F i) (F.le i) (Y i) (R^2))
    (T : ℕ) (a : ℝ) (ha : 0 < a) :
    μ.real {omega | a ≤ partialSum Y T omega} ≤
      Real.exp (-a^2/(2*((T:ℝ)*(R:ℝ)^2))) := by
  simpa only [NNReal.coe_mul,NNReal.coe_pow,NNReal.coe_natCast] using
    (actual_azuma_sum_subgaussian μ F Y hY R hcond T).measure_ge_le ha.le

theorem bounded_martingale_difference_azuma {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (Y : ℕ → Ω → ℝ) (hY : ∀ i,StronglyMeasurable[F (i+1)] (Y i)) (R : ℝ≥0)
    (hb : ∀ i,∀ᵐ omega ∂μ,Y i omega ∈ Set.Icc (-(R:ℝ)) R)
    (hz : ∀ i,μ[Y i | F i]=ᵐ[μ] 0) (T : ℕ) (a : ℝ) (ha : 0 < a) :
    μ.real {omega | a ≤ partialSum Y T omega} ≤
      Real.exp (-a^2/(2*((T:ℝ)*(R:ℝ)^2))) := by
  apply actual_azuma_tail μ F Y hY R _ T a ha
  intro i
  exact bounded_centered_is_real_conditional_subgaussian μ (F i) (F.le i) (Y i)
    ((hY i).mono (F.le (i+1))).measurable R (hb i) (hz i)

end SafeLearning.CompleteAppliedAzuma
