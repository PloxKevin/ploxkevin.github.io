import SafeLearning.CompleteBarrierAbsolutelyContinuous

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped Topology NNReal
open Set Filter MeasureTheory
namespace SafeLearning.CompleteAppliedSmallGainStorage

theorem actual_one_lipschitz_zero_nonlinearity_has_origin_gain_and_sector_product_bound
    (phi : ℝ→ℝ) (hl : LipschitzWith 1 phi) (hz : phi 0=0) (state : ℝ) :
    |phi state|≤ |state| ∧ state*phi state≤ state^2 := by
  have hb := hl.dist_le_mul state 0
  simp only [hz,Real.dist_eq,sub_zero,NNReal.coe_one,one_mul] at hb
  refine ⟨hb,?_⟩
  calc
    state*phi state ≤ |state*phi state| := le_abs_self _
    _ = |state| *|phi state| := abs_mul _ _
    _ ≤ |state| *|state| := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    _ = state^2 := by rw [←sq_abs,pow_two]

theorem actual_source_positive_feedback_storage_derivative_is_derived
    (phi : ℝ→ℝ) (hl : LipschitzWith 1 phi) (hz : phi 0=0) (state : ℝ) :
    2*state*(-state+(4/5)*phi state)=-2*state^2+(8/5)*state*phi state ∧
      2*state*(-state+(4/5)*phi state)≤ -(2/5)*state^2 := by
  have hp := (actual_one_lipschitz_zero_nonlinearity_has_origin_gain_and_sector_product_bound
    phi hl hz state).2
  constructor
  · ring
  · nlinarith

theorem actual_source_negative_feedback_storage_derivative_uses_the_sector_sign
    (phi : ℝ→ℝ) (hsector : ∀state,0≤ state*phi state ∧ state*phi state≤3*state^2)
    (state : ℝ) :
    2*state*(-state-phi state)=-2*state^2-2*state*phi state ∧
      2*state*(-state-phi state)≤ -2*state^2 := by
  constructor
  · ring
  · nlinarith [(hsector state).1]

theorem actual_existing_ac_trajectory_square_decrease_implies_the_true_norm_bound
    (state velocity : ℝ→ℝ) (rate horizon : ℝ) (hT : 0≤horizon)
    (hc : AbsolutelyContinuousOnInterval state 0 horizon)
    (hd : ∀ᵐ time ∂volume,time∈Icc 0 horizon→HasDerivAt state (velocity time) time)
    (hb : ∀ᵐ time ∂volume,time∈Icc 0 horizon→2*state time*velocity time≤ -2*rate*state time^2)
    (time : ℝ) (ht : time∈Icc 0 horizon) :
    |state time|≤ |state 0| *Real.exp (-rate*time) := by
  have hs : AbsolutelyContinuousOnInterval (fun time=>-(state time)^2) 0 horizon := by
    have hm : AbsolutelyContinuousOnInterval (fun time=>state time*state time) 0 horizon :=
      hc.mul hc
    convert hm.neg using 1
    funext time
    simp only [Pi.neg_apply,pow_two]
  have hds : ∀ᵐ time ∂volume,time∈Icc 0 horizon→
      HasDerivAt (fun time=>-(state time)^2) (-2*state time*velocity time) time := by
    filter_upwards [hd] with time hd ht
    convert ((hd ht).pow 2).neg using 1 <;> ring
  have hbs : ∀ᵐ time ∂volume,time∈Icc 0 horizon→
      -(2*rate)*(-(state time)^2)≤ -2*state time*velocity time := by
    filter_upwards [hb] with time hb ht
    nlinarith [hb ht]
  have hi := CompleteBarrierAbsolutelyContinuous.genuine_ae_integrating_factor
    (fun time=>-(state time)^2) (fun time=>-2*state time*velocity time)
    (2*rate) horizon hT hs hds hbs time ht
  have he : Real.exp (-(2*rate)*time)=Real.exp (-rate*time)^2 := by
    rw [pow_two,←Real.exp_add]
    congr 1
    ring
  rw [he] at hi
  have hn : 0≤ |state 0| *Real.exp (-rate*time) := by positivity
  nlinarith [sq_abs (state time),sq_abs (state 0),abs_nonneg (state time)]

theorem actual_source_small_gain_ac_ode_has_the_literal_exponential_bound
    (phi : ℝ→ℝ) (hl : LipschitzWith 1 phi) (hz : phi 0=0)
    (state : ℝ→ℝ) (horizon : ℝ) (hT : 0≤horizon)
    (hc : AbsolutelyContinuousOnInterval state 0 horizon)
    (hd : ∀ᵐ time ∂volume,time∈Icc 0 horizon→
      HasDerivAt state (-state time+(4/5)*phi (state time)) time)
    (time : ℝ) (ht : time∈Icc 0 horizon) :
    |state time|≤ |state 0| *Real.exp (-(1/5)*time) := by
  apply actual_existing_ac_trajectory_square_decrease_implies_the_true_norm_bound
    state (fun time=>-state time+(4/5)*phi (state time)) (1/5) horizon hT hc hd _ time ht
  filter_upwards [] with time _
  have hp := (actual_source_positive_feedback_storage_derivative_is_derived phi hl hz (state time)).2
  nlinarith

theorem actual_source_sector_negative_feedback_ac_ode_has_the_literal_exponential_bound
    (phi : ℝ→ℝ) (hsector : ∀state,0≤ state*phi state ∧ state*phi state≤3*state^2)
    (state : ℝ→ℝ) (horizon : ℝ) (hT : 0≤horizon)
    (hc : AbsolutelyContinuousOnInterval state 0 horizon)
    (hd : ∀ᵐ time ∂volume,time∈Icc 0 horizon→
      HasDerivAt state (-state time-phi (state time)) time)
    (time : ℝ) (ht : time∈Icc 0 horizon) :
    |state time|≤ |state 0| *Real.exp (-time) := by
  have hi := actual_existing_ac_trajectory_square_decrease_implies_the_true_norm_bound
    state (fun time=>-state time-phi (state time)) 1 horizon hT hc hd (by
      filter_upwards [] with time _
      have hp := (actual_source_negative_feedback_storage_derivative_uses_the_sector_sign
        phi hsector (state time)).2
      nlinarith) time ht
  simpa only [neg_one_mul] using hi

theorem actual_sector_zero_nonlinearity_has_the_true_origin_gain_at_most_three
    (phi : ℝ→ℝ) (hz : phi 0=0)
    (hsector : ∀state,0≤ state*phi state ∧ state*phi state≤3*state^2) :
    ∀state,|phi state|≤3*|state| := by
  intro state
  by_cases hs : state=0
  · simp [hs,hz]
  · have hp := hsector state
    have he : |state| *|phi state|=state*phi state := by
      rw [←abs_mul,abs_of_nonneg hp.1]
    have hab : 0 < |state| := abs_pos.mpr hs
    have hb : |state| *|phi state|≤ |state| *(3*|state|) := by
      rw [he]
      nlinarith [sq_abs state]
    exact (mul_le_mul_iff_right₀ hab).mp hb

def actualLinearFrequencyGain (gain omega : ℝ) : ℝ :=
  ‖(gain:ℂ)/(((omega:ℂ)*Complex.I)+1)‖

theorem actual_first_order_frequency_gain_is_the_true_complex_modulus
    (gain omega : ℝ) (hg : 0≤gain) :
    actualLinearFrequencyGain gain omega=gain/Real.sqrt (1+omega^2) := by
  have hd : ‖((omega:ℂ)*Complex.I)+1‖=Real.sqrt (1+omega^2) := by
    rw [Complex.norm_def]
    congr 1
    simp [Complex.normSq_apply]
    ring
  rw [actualLinearFrequencyGain,norm_div,hd,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hg]

theorem actual_first_order_worst_frequency_gain_is_attained_at_zero
    (gain : ℝ) (hg : 0≤gain) :
    IsGreatest (range (actualLinearFrequencyGain gain)) gain ∧
      sSup (range (actualLinearFrequencyGain gain))=gain := by
  have h0 : actualLinearFrequencyGain gain 0=gain := by
    rw [actual_first_order_frequency_gain_is_the_true_complex_modulus gain 0 hg]
    norm_num
  have hb : ∀omega,actualLinearFrequencyGain gain omega≤gain := by
    intro omega
    rw [actual_first_order_frequency_gain_is_the_true_complex_modulus gain omega hg]
    have hs : 1≤Real.sqrt (1+omega^2) := (Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith [sq_nonneg omega])
    rw [div_le_iff₀ (by linarith : 0<Real.sqrt (1+omega^2))]
    nlinarith
  have hgreat : IsGreatest (range (actualLinearFrequencyGain gain)) gain :=
    ⟨⟨0,h0⟩,by rintro value ⟨omega,rfl⟩;exact hb omega⟩
  exact ⟨hgreat,hgreat.csSup_eq⟩

theorem actual_source_coarse_loop_products_distinguish_certificate_from_stability :
    sSup (range (actualLinearFrequencyGain (4/5)))=4/5 ∧
    (4/5:ℝ)*1<1 ∧ sSup (range (actualLinearFrequencyGain 1))=1 ∧
    (1:ℝ)*3>1 := by
  exact ⟨(actual_first_order_worst_frequency_gain_is_attained_at_zero _ (by norm_num)).2,
    by norm_num,(actual_first_order_worst_frequency_gain_is_attained_at_zero _ (by norm_num)).2,by norm_num⟩

end SafeLearning.CompleteAppliedSmallGainStorage
