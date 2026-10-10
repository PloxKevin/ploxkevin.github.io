import SafeLearning.CompleteModulesTanhSharpBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace SafeLearning.CompleteAppliedCircleFeedback
open CompleteModulesTheory CompleteModulesTanhChords CompleteModulesTanhSharpBounds

def sourceNonlinearity (kappa x : ℝ) : ℝ := kappa*Real.tanh x

theorem actual_scaled_tanh_has_the_stated_derivative_and_sector (kappa : ℝ) (hk : 0≤kappa)
    (x : ℝ) :
    HasDerivAt (sourceNonlinearity kappa) (kappa*(1-(Real.tanh x)^2)) x ∧
    0≤kappa*(1-(Real.tanh x)^2) ∧ kappa*(1-(Real.tanh x)^2)≤kappa ∧
    0≤x*sourceNonlinearity kappa x ∧ x*sourceNonlinearity kappa x≤kappa*x^2 := by
  have h := actual_tanh_has_the_literal_strictly_positive_bounded_derivative x
  have hs := actual_tanh_literal_origin_sector_bounds x
  refine ⟨h.1.const_mul kappa,mul_nonneg hk h.2.1.le,?_,?_,?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left h.2.2 hk]
  · dsimp [sourceNonlinearity];nlinarith [mul_nonneg hk hs.1]
  · dsimp [sourceNonlinearity];nlinarith [mul_le_mul_of_nonneg_left hs.2 hk]

theorem actual_scaled_tanh_gain_is_the_least_global_gain (kappa : ℝ) (hk : 0≤kappa) :
    IsLeast {gain : ℝ | ∀x : ℝ,|sourceNonlinearity kappa x|≤gain*|x|} kappa := by
  have hbound (x : ℝ) : |sourceNonlinearity kappa x|≤kappa*|x| := by
    have h := tanh_lipschitz.dist_le_mul x 0
    simp only [Real.dist_eq,Real.tanh_zero,sub_zero,NNReal.coe_one,one_mul] at h
    rw [sourceNonlinearity,abs_mul,abs_of_nonneg hk]
    exact mul_le_mul_of_nonneg_left h hk
  refine ⟨hbound,?_⟩
  intro gain hgain
  have hlimit : Tendsto (fun x : ℝ=>kappa*(Real.tanh x/x))
      (nhdsWithin 0 (Ioi 0)) (𝓝 kappa) := by
    have h := (actual_origin_ratio_approaches_the_upper_endpoint_one_at_zero.mono_left
      (nhdsGT_le_nhdsNE 0)).const_mul kappa
    simpa only [mul_one] using h
  apply le_of_tendsto hlimit
  filter_upwards [show ∀ᶠ x : ℝ in nhdsWithin 0 (Ioi 0),0<x from self_mem_nhdsWithin] with x hx
  have h := hgain x
  have ht : 0≤Real.tanh x := by
    simpa only [Real.tanh_zero] using tanh_monotone (show (0:ℝ)≤x from hx.le)
  rw [sourceNonlinearity,abs_of_nonneg (mul_nonneg hk ht),abs_of_pos hx] at h
  rw [←mul_div_assoc,div_le_iff₀ hx]
  exact h

theorem actual_source_small_gain_test_iff (kappa : ℝ) :
    (3*kappa<1 ↔ kappa<1/3) ∧ (3:ℝ)=9*(1/3:ℝ) := by
  constructor
  · constructor <;> intro h <;> linarith
  · norm_num

def constantTrajectory (gain initial : ℝ) (n : ℕ) : ℝ := (4/5-3/5*gain)^n*initial

theorem actual_constant_feedback_recurrence (gain initial : ℝ) :
    constantTrajectory gain initial 0=initial ∧ ∀n,
      constantTrajectory gain initial (n+1)=(4/5)*constantTrajectory gain initial n-
        gain*((3/5)*constantTrajectory gain initial n) := by
  constructor
  · simp [constantTrajectory]
  · intro n;simp only [constantTrajectory,pow_succ];ring

theorem actual_every_constant_feedback_recurrence_is_the_geometric_trajectory
    (gain initial : ℝ) (x : ℕ→ℝ) (h0 : x 0=initial)
    (hnext : ∀n,x (n+1)=(4/5)*x n-gain*((3/5)*x n)) :
    ∀n,x n=constantTrajectory gain initial n := by
  intro n;induction n with
  | zero => simpa only [constantTrajectory,pow_zero,one_mul] using h0
  | succ n ih => rw [hnext,ih,(actual_constant_feedback_recurrence gain initial).2]

theorem actual_all_initial_constant_gain_decay_iff (gain : ℝ) :
    (∀initial : ℝ,Tendsto (constantTrajectory gain initial) atTop (𝓝 0)) ↔
      -1/3<gain ∧ gain<3 := by
  have hiff : (∀initial : ℝ,Tendsto (constantTrajectory gain initial) atTop (𝓝 0)) ↔
      |(4/5:ℝ)-3/5*gain|<1 := by
    constructor
    · intro h
      have h1 := h 1
      change Tendsto (fun n : ℕ=>(4/5-3/5*gain)^n*1) atTop (𝓝 0) at h1
      simp only [mul_one] at h1
      exact tendsto_pow_atTop_nhds_zero_iff.mp h1
    · intro h initial
      have hp := tendsto_pow_atTop_nhds_zero_iff.mpr h
      change Tendsto (fun n : ℕ=>(4/5-3/5*gain)^n*initial) atTop (𝓝 0)
      simpa only [zero_mul] using hp.mul_const initial
  rw [hiff,abs_lt]
  constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith

def sectorContraction (kappa : ℝ) : ℝ := max (4/5) |4/5-3/5*kappa|
def actualStep (phi : ℝ→ℝ) (x : ℝ) : ℝ := (4/5)*x-phi ((3/5)*x)

theorem actual_every_sector_feedback_step_has_a_uniform_contraction_bound
    (kappa : ℝ) (hk : 0≤kappa) (phi : ℝ→ℝ) (hzero : phi 0=0)
    (hsector : ∀z : ℝ,0≤z*phi z ∧ z*phi z≤kappa*z^2) (x : ℝ) :
    |actualStep phi x|≤ sectorContraction kappa*|x| := by
  have hq0 : (4/5:ℝ)≤ sectorContraction kappa := le_max_left _ _
  have hq1 : |(4/5:ℝ)-3/5*kappa|≤ sectorContraction kappa := le_max_right _ _
  have hqlo : -(sectorContraction kappa)≤(4/5:ℝ)-3/5*kappa := (abs_le.mp hq1).1
  have hs := hsector ((3/5)*x)
  by_cases hx : x=0
  · subst x;simp [actualStep,hzero]
  · rcases lt_or_gt_of_ne hx with hx | hx
    · have hp : phi ((3/5)*x)≤0 := by nlinarith [hs.1]
      have hl : (3/5)*kappa*x≤phi ((3/5)*x) := by nlinarith [hs.2]
      rw [abs_of_neg hx]
      apply abs_le.mpr
      dsimp [actualStep]
      constructor
      · nlinarith
      · nlinarith
    · have hp : 0≤phi ((3/5)*x) := by nlinarith [hs.1]
      have hu : phi ((3/5)*x)≤(3/5)*kappa*x := by nlinarith [hs.2]
      rw [abs_of_pos hx]
      apply abs_le.mpr
      dsimp [actualStep]
      constructor
      · nlinarith
      · nlinarith

theorem actual_sector_contraction_is_strictly_less_than_one (kappa : ℝ)
    (hk : 0≤kappa) (hk3 : kappa<3) :
    0≤ sectorContraction kappa ∧ sectorContraction kappa<1 := by
  constructor
  · exact le_trans (by norm_num : (0:ℝ)≤4/5) (le_max_left _ _)
  · rw [sectorContraction,max_lt_iff,abs_lt]
    refine ⟨by norm_num,?_⟩
    constructor <;> linarith

def sectorTrajectory (phi : ℕ→ℝ→ℝ) (initial : ℝ) : ℕ→ℝ
  | 0 => initial
  | n+1 => actualStep (phi n) (sectorTrajectory phi initial n)

theorem actual_every_time_varying_sector_trajectory_has_the_geometric_bound
    (kappa : ℝ) (hk : 0≤kappa) (phi : ℕ→ℝ→ℝ)
    (hzero : ∀n,phi n 0=0)
    (hsector : ∀n z,0≤z*phi n z ∧ z*phi n z≤kappa*z^2)
    (initial : ℝ) (n : ℕ) :
    |sectorTrajectory phi initial n|≤ sectorContraction kappa^n*|initial| := by
  induction n with
  | zero => simp [sectorTrajectory]
  | succ n ih =>
    rw [sectorTrajectory]
    have hq : 0≤ sectorContraction kappa := le_trans (by norm_num : (0:ℝ)≤4/5) (le_max_left _ _)
    calc
      |actualStep (phi n) (sectorTrajectory phi initial n)|≤
          sectorContraction kappa*|sectorTrajectory phi initial n| :=
        actual_every_sector_feedback_step_has_a_uniform_contraction_bound kappa hk (phi n)
          (hzero n) (hsector n) _
      _≤ sectorContraction kappa*(sectorContraction kappa^n*|initial|) :=
        mul_le_mul_of_nonneg_left ih hq
      _=sectorContraction kappa^(n+1)*|initial| := by rw [pow_succ];ring

theorem actual_every_time_varying_sector_trajectory_tends_to_zero
    (kappa : ℝ) (hk : 0≤kappa) (hk3 : kappa<3) (phi : ℕ→ℝ→ℝ)
    (hzero : ∀n,phi n 0=0)
    (hsector : ∀n z,0≤z*phi n z ∧ z*phi n z≤kappa*z^2) (initial : ℝ) :
    Tendsto (sectorTrajectory phi initial) atTop (𝓝 0) := by
  have hq := actual_sector_contraction_is_strictly_less_than_one kappa hk hk3
  have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one hq.1 hq.2).mul_const |initial|
  apply squeeze_zero_norm
  · intro n
    simpa only [Real.norm_eq_abs] using
      actual_every_time_varying_sector_trajectory_has_the_geometric_bound kappa hk phi hzero hsector initial n
  · simpa only [zero_mul] using hp

theorem actual_sector_feedback_is_lyapunov_stable (kappa : ℝ) (hk : 0≤kappa)
    (hk3 : kappa<3) (phi : ℕ→ℝ→ℝ) (hzero : ∀n,phi n 0=0)
    (hsector : ∀n z,0≤z*phi n z ∧ z*phi n z≤kappa*z^2) :
    ∀epsilon : ℝ,0<epsilon → ∃delta : ℝ,0<delta ∧
      ∀initial : ℝ,|initial|<delta → ∀n,|sectorTrajectory phi initial n|<epsilon := by
  intro epsilon he
  refine ⟨epsilon,he,?_⟩
  intro initial hi n
  have hq := actual_sector_contraction_is_strictly_less_than_one kappa hk hk3
  have hp : sectorContraction kappa^n≤1 := pow_le_one₀ hq.1 hq.2.le
  exact (actual_every_time_varying_sector_trajectory_has_the_geometric_bound kappa hk phi hzero hsector initial n).trans_lt
    ((mul_le_mul_of_nonneg_right hp (abs_nonneg initial)).trans_lt (by simpa using hi))

end SafeLearning.CompleteAppliedCircleFeedback
