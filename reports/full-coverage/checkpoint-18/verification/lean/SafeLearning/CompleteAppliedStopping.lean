import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.MeasureTheory.Measure.Continuity
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedStopping
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

theorem bounded_optional_stopping {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : Filtration ℕ mΩ)
    (M : ℕ → Ω → ℝ) (hM : Supermartingale M F μ)
    (tau : Ω → WithTop ℕ) (htau : IsStoppingTime F tau)
    (T : ℕ) (hbound : ∀ omega,tau omega ≤ T) :
    (∫ omega,stoppedValue M tau omega ∂μ) ≤ ∫ omega,M 0 omega ∂μ := by
  have hh := hM.neg.expected_stoppedValue_mono (isStoppingTime_const F 0) htau
    (fun omega => bot_le) hbound
  simpa only [stoppedValue_const,stoppedValue_neg,Pi.neg_apply,integral_neg,neg_le_neg_iff]
    using hh

theorem finite_ville {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : Filtration ℕ mΩ)
    (M : ℕ → Ω → ℝ) (hM : Supermartingale M F μ)
    (hnonneg : ∀ n,∀ᵐ omega ∂μ,0 ≤ M n omega)
    (c : ℝ) (hc : 0 < c) (T : ℕ) :
    μ.real {omega | ∃ n ≤ T,c ≤ M n omega} ≤ (∫ omega,M 0 omega ∂μ)/c := by
  classical
  let tau : Ω → WithTop ℕ := fun omega => (hittingBtwn M (Set.Ici c) 0 T omega : ℕ)
  have htau : IsStoppingTime F tau :=
    hM.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici
  have hbound : ∀ omega,tau omega ≤ T := by
    intro omega
    change (↑(hittingBtwn M (Set.Ici c) 0 T omega : ℕ) : WithTop ℕ) ≤ (T:WithTop ℕ)
    exact_mod_cast hittingBtwn_le (u := M) (s := Set.Ici c) (n := 0) (m := T) omega
  have hint : Integrable (stoppedValue M tau) μ :=
    integrable_stoppedValue ℕ htau hM.integrable hbound
  have hA : MeasurableSet {omega | ∃ n ≤ T,c ≤ M n omega} := by
    have heq : {omega | ∃ n ≤ T,c ≤ M n omega} =
        ⋃ n ∈ Finset.range (T+1),{omega | c ≤ M n omega} := by
      ext omega
      simp
    rw [heq]
    exact MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun _ =>
      measurableSet_le measurable_const
        ((hM.stronglyAdapted n).measurable.mono (F.le n) le_rfl)
  have hstop_nonneg : ∀ᵐ omega ∂μ,0 ≤ stoppedValue M tau omega := by
    filter_upwards [ae_all_iff.mpr hnonneg] with omega homega
    exact homega _
  have hind : ∀ᵐ omega ∂μ,
      {omega | ∃ n ≤ T,c ≤ M n omega}.indicator (fun _ => c) omega ≤
        stoppedValue M tau omega := by
    filter_upwards [hstop_nonneg] with omega homega
    by_cases ha : ∃ n ≤ T,c ≤ M n omega
    · rw [Set.indicator_of_mem (show omega ∈ {omega | ∃ n ≤ T,c ≤ M n omega} from ha)]
      apply stoppedValue_hittingBtwn_mem
      obtain ⟨n,hn,hval⟩ := ha
      exact ⟨n,⟨Nat.zero_le _,hn⟩,hval⟩
    · rw [Set.indicator_of_notMem (show omega ∉ {omega | ∃ n ≤ T,c ≤ M n omega} from ha)]
      exact homega
  have hh := integral_mono_ae ((integrable_const c).indicator hA) hint hind
  rw [integral_indicator hA,integral_const] at hh
  have hopt := bounded_optional_stopping μ F M hM tau htau T hbound
  apply (le_div_iff₀ hc).mpr
  simpa only [MeasureTheory.Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_comm]
    using hh.trans hopt

theorem ville {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : Filtration ℕ mΩ)
    (M : ℕ → Ω → ℝ) (hM : Supermartingale M F μ)
    (hnonneg : ∀ n,∀ᵐ omega ∂μ,0 ≤ M n omega)
    (c : ℝ) (hc : 0 < c) :
    μ.real {omega | ∃ n,c ≤ M n omega} ≤ (∫ omega,M 0 omega ∂μ)/c := by
  let A : ℕ → Set Ω := fun T => {omega | ∃ n ≤ T,c ≤ M n omega}
  have hmono : Monotone A := by
    intro i j hij omega homega
    obtain ⟨n,hn,hval⟩ := homega
    exact ⟨n,hn.trans hij,hval⟩
  have hunion : (⋃ T,A T) = {omega | ∃ n,c ≤ M n omega} := by
    ext omega
    simp only [Set.mem_iUnion,Set.mem_ofPred_eq,A]
    constructor
    · rintro ⟨T,n,_,h⟩
      exact ⟨n,h⟩
    · rintro ⟨n,h⟩
      exact ⟨n,n,le_rfl,h⟩
  have hfinite (T : ℕ) : μ (A T) ≤ ENNReal.ofReal ((∫ omega,M 0 omega ∂μ)/c) := by
    rw [← ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (div_nonneg (integral_nonneg_of_ae (hnonneg 0)) hc.le)]
    exact finite_ville μ F M hM hnonneg c hc T
  have htotal : μ {omega | ∃ n,c ≤ M n omega} ≤
      ENNReal.ofReal ((∫ omega,M 0 omega ∂μ)/c) := by
    rw [← hunion,hmono.measure_iUnion]
    exact iSup_le hfinite
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top htotal
  rwa [ENNReal.toReal_ofReal (div_nonneg (integral_nonneg_of_ae (hnonneg 0)) hc.le)] at hh

theorem finite_almost_sure_optional_stopping {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : Filtration ℕ mΩ)
    (M : ℕ → Ω → ℝ) (hM : Supermartingale M F μ)
    (hnonneg : ∀ n,∀ᵐ omega ∂μ,0 ≤ M n omega)
    (tau : Ω → WithTop ℕ) (htau : IsStoppingTime F tau)
    (hfinite : ∀ᵐ omega ∂μ,tau omega ≠ ⊤) :
    Integrable (stoppedValue M tau) μ ∧
      (∫ omega,stoppedValue M tau omega ∂μ) ≤ ∫ omega,M 0 omega ∂μ := by
  let G : ℕ → Ω → ℝ := fun T => stoppedValue M (fun omega => min (tau omega) T)
  have hmin (T : ℕ) : IsStoppingTime F (fun omega => min (tau omega) T) :=
    htau.min (isStoppingTime_const F T)
  have hbound (T : ℕ) (omega : Ω) : min (tau omega) (T:WithTop ℕ) ≤ T := min_le_right _ _
  have hint (T : ℕ) : Integrable (G T) μ :=
    integrable_stoppedValue ℕ (hmin T) hM.integrable (hbound T)
  have hNN : ∀ᵐ omega ∂μ,∀ n,0 ≤ M n omega := ae_all_iff.mpr hnonneg
  have hGnn (T : ℕ) : ∀ᵐ omega ∂μ,0 ≤ G T omega := by
    filter_upwards [hNN] with omega homega
    exact homega _
  have hstopnn : ∀ᵐ omega ∂μ,0 ≤ stoppedValue M tau omega := by
    filter_upwards [hNN] with omega homega
    exact homega _
  have hGi (T : ℕ) : (∫ omega,G T omega ∂μ) ≤ ∫ omega,M 0 omega ∂μ :=
    bounded_optional_stopping μ F M hM _ (hmin T) T (hbound T)
  have hlimit : ∀ᵐ omega ∂μ,Tendsto (fun T => G T omega) atTop
      (𝓝 (stoppedValue M tau omega)) := by
    filter_upwards [hfinite] with omega homega
    obtain ⟨n,hn⟩ := WithTop.ne_top_iff_exists.mp homega
    have heq : (fun T => G T omega) =ᶠ[atTop] fun _ => stoppedValue M tau omega := by
      filter_upwards [eventually_ge_atTop n] with T hT
      have hle : (n:WithTop ℕ) ≤ T := by exact_mod_cast hT
      simp [G,stoppedValue,← hn,min_eq_left hle]
    exact tendsto_const_nhds.congr' heq.symm
  have hmeas := aestronglyMeasurable_of_tendsto_ae atTop
    (fun T => (hint T).aestronglyMeasurable) hlimit
  have hlin (T : ℕ) : (∫⁻ omega,ENNReal.ofReal (G T omega) ∂μ) ≤
      ENNReal.ofReal (∫ omega,M 0 omega ∂μ) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hint T) (hGnn T)]
    exact ENNReal.ofReal_le_ofReal (hGi T)
  have hFatou : (∫⁻ omega,ENNReal.ofReal (stoppedValue M tau omega) ∂μ) ≤
      ENNReal.ofReal (∫ omega,M 0 omega ∂μ) := by
    calc
      _ = ∫⁻ omega,liminf (fun T => ENNReal.ofReal (G T omega)) atTop ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hlimit] with omega homega
        exact (ENNReal.tendsto_ofReal homega).liminf_eq.symm
      _ ≤ liminf (fun T => ∫⁻ omega,ENNReal.ofReal (G T omega) ∂μ) atTop :=
        lintegral_liminf_le' fun T => (hint T).aestronglyMeasurable.aemeasurable.ennreal_ofReal
      _ ≤ _ := liminf_le_of_frequently_le' (Filter.Eventually.frequently (Eventually.of_forall hlin))
  have hstopint : Integrable (stoppedValue M tau) μ :=
    (lintegral_ofReal_ne_top_iff_integrable hmeas hstopnn).mp
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hFatou)
  refine ⟨hstopint,?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hstopint hstopnn] at hFatou
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg_of_ae (hnonneg 0))).mp hFatou

theorem first_hit_truncated_proof {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : Filtration ℕ mΩ)
    (M : ℕ → Ω → ℝ) (hM : Supermartingale M F μ)
    (hnonneg : ∀ n,∀ᵐ omega ∂μ,0 ≤ M n omega) (c : ℝ) (hc : 0 < c) (T : ℕ) :
    let tau := hittingAfter M (Set.Ici c) 0
    IsStoppingTime F tau ∧
    IsStoppingTime F (fun omega => min (tau omega) T) ∧
    ((∫ omega,stoppedValue M (fun w => min (tau w) T) omega ∂μ) ≤
      ∫ omega,M 0 omega ∂μ) ∧
    (∀ omega,tau omega ≤ T ↔ ∃ n ≤ T,c ≤ M n omega) ∧
    (∀ᵐ omega ∂μ,
      {omega | tau omega ≤ T}.indicator (fun _ => c) omega ≤
        stoppedValue M (fun w => min (tau w) T) omega) := by
  classical
  dsimp only
  let tau := hittingAfter M (Set.Ici c) 0
  have htau : IsStoppingTime F tau :=
    hM.stronglyAdapted.adapted.isStoppingTime_hittingAfter measurableSet_Ici
  have hmin := htau.min (isStoppingTime_const F T)
  refine ⟨htau,hmin,bounded_optional_stopping μ F M hM _ hmin T
    (fun _ => min_le_right _ _),?_,?_⟩
  · intro omega
    change tau omega ≤ (T:WithTop ℕ) ↔ ∃ n ≤ T,c ≤ M n omega
    have hh := hittingAfter_le_iff (u := M) (s := Set.Ici c) (n := 0) (i := T) (ω := omega)
    constructor
    · intro h
      obtain ⟨j,hj,hval⟩ := hh.mp h
      exact ⟨j,hj.2,hval⟩
    · rintro ⟨j,hj,hval⟩
      exact hh.mpr ⟨j,⟨Nat.zero_le _,hj⟩,hval⟩
  · filter_upwards [ae_all_iff.mpr hnonneg] with omega homega
    by_cases ha : tau omega ≤ T
    · rw [Set.indicator_of_mem (show omega ∈ {omega | tau omega ≤ T} from ha)]
      have hn : tau omega ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top ha
      have hh := hittingAfter_mem_set_of_ne_top (u := M) (s := Set.Ici c) (n := 0) hn
      change c ≤ M (min (tau omega) (T:WithTop ℕ)).untopA omega
      rw [min_eq_left ha]
      exact hh
    · rw [Set.indicator_of_notMem (show omega ∉ {omega | tau omega ≤ T} from ha)]
      exact homega _

end SafeLearning.CompleteAppliedStopping
