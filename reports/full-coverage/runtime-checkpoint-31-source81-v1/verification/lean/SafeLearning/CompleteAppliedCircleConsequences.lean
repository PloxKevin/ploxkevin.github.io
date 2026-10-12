import SafeLearning.CompleteAppliedCircleFrequency
import SafeLearning.CompleteAppliedCircleFeedback

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace SafeLearning.CompleteAppliedCircleConsequences
open CompleteAppliedCircleFrequency CompleteAppliedCircleFeedback CompleteModulesTheory

theorem actual_unit_point_is_the_printed_complex_exponential (omega : ℝ) :
    unitPoint omega=Complex.exp ((omega:ℂ)*Complex.I) := by
  simpa only [unitPoint] using (Complex.exp_ofReal_mul_I omega).symm

theorem actual_source_scaled_tanh_incremental_gain_bound (kappa : ℝ) (hk : 0≤kappa)
    (x y : ℝ) :
    |sourceNonlinearity kappa x-sourceNonlinearity kappa y|≤kappa*|x-y| := by
  have h := tanh_lipschitz.dist_le_mul x y
  simp only [Real.dist_eq,NNReal.coe_one,one_mul] at h
  have he : sourceNonlinearity kappa x-sourceNonlinearity kappa y=
      kappa*(Real.tanh x-Real.tanh y) := by dsimp [sourceNonlinearity];ring
  rw [he,abs_mul,abs_of_nonneg hk]
  exact mul_le_mul_of_nonneg_left h hk

def actualTanhTrajectory (kappa initial : ℝ) : ℕ→ℝ :=
  sectorTrajectory (fun _=>sourceNonlinearity kappa) initial

theorem actual_source_tanh_closed_loop_and_all_initial_decay (kappa : ℝ)
    (hk : 0≤kappa) (hk3 : kappa<3) (initial : ℝ) :
    actualTanhTrajectory kappa initial 0=initial ∧
    (∀n,actualTanhTrajectory kappa initial (n+1)=
      (4/5)*actualTanhTrajectory kappa initial n-
        kappa*Real.tanh ((3/5)*actualTanhTrajectory kappa initial n)) ∧
    (∀n,|actualTanhTrajectory kappa initial n|≤ sectorContraction kappa^n*|initial|) ∧
    Tendsto (actualTanhTrajectory kappa initial) atTop (𝓝 0) := by
  have hz : ∀n : ℕ,(fun _=>sourceNonlinearity kappa) n 0=0 := by
    intro n;simp [sourceNonlinearity]
  have hs : ∀n z,0≤z*(fun _ : ℕ=>sourceNonlinearity kappa) n z ∧
      z*(fun _ : ℕ=>sourceNonlinearity kappa) n z≤kappa*z^2 := by
    intro n z
    exact (actual_scaled_tanh_has_the_stated_derivative_and_sector kappa hk z).2.2.2
  refine ⟨rfl,?_,?_,?_⟩
  · intro n;rfl
  · exact actual_every_time_varying_sector_trajectory_has_the_geometric_bound kappa hk _ hz hs initial
  · exact actual_every_time_varying_sector_trajectory_tends_to_zero kappa hk hk3 _ hz hs initial

theorem actual_small_gain_certified_source_tanh_loops_are_stable (kappa : ℝ)
    (hk : 0≤kappa) (hsmall : 3*kappa<1) :
    (∀initial : ℝ,Tendsto (actualTanhTrajectory kappa initial) atTop (𝓝 0)) ∧
    (∀epsilon : ℝ,0<epsilon → ∃delta : ℝ,0<delta ∧
      ∀initial : ℝ,|initial|<delta → ∀n,|actualTanhTrajectory kappa initial n|<epsilon) := by
  have hk3 : kappa<3 := by linarith
  have hz : ∀n : ℕ,(fun _=>sourceNonlinearity kappa) n 0=0 := by
    intro n;simp [sourceNonlinearity]
  have hs : ∀n z,0≤z*(fun _ : ℕ=>sourceNonlinearity kappa) n z ∧
      z*(fun _ : ℕ=>sourceNonlinearity kappa) n z≤kappa*z^2 := by
    intro n z
    exact (actual_scaled_tanh_has_the_stated_derivative_and_sector kappa hk z).2.2.2
  exact ⟨fun initial=>(actual_source_tanh_closed_loop_and_all_initial_decay kappa hk hk3 initial).2.2.2,
    actual_sector_feedback_is_lyapunov_stable kappa hk hk3 _ hz hs⟩

theorem actual_entire_sector_class_all_initial_decay_iff (kappa : ℝ) (hk : 0≤kappa) :
    (∀phi : ℕ→ℝ→ℝ,(∀n,phi n 0=0) →
      (∀n z,0≤z*phi n z ∧ z*phi n z≤kappa*z^2) →
      ∀initial : ℝ,Tendsto (sectorTrajectory phi initial) atTop (𝓝 0)) ↔ kappa<3 := by
  constructor
  · intro h
    let phi : ℕ→ℝ→ℝ := fun _ z=>kappa*z
    have hz : ∀n,phi n 0=0 := by intro n;simp [phi]
    have hs : ∀n z,0≤z*phi n z ∧ z*phi n z≤kappa*z^2 := by
      intro n z
      dsimp [phi]
      constructor
      · nlinarith [mul_nonneg hk (sq_nonneg z)]
      · nlinarith
    have hall : ∀initial : ℝ,Tendsto (constantTrajectory kappa initial) atTop (𝓝 0) := by
      intro initial
      have he : sectorTrajectory phi initial=constantTrajectory kappa initial := by
        funext n
        apply actual_every_constant_feedback_recurrence_is_the_geometric_trajectory
          kappa initial (sectorTrajectory phi initial) rfl
        intro m;rfl
      rw [←he]
      exact h phi hz hs initial
    exact (actual_all_initial_constant_gain_decay_iff kappa).mp hall |>.2
  · intro hk3 phi hz hs initial
    exact actual_every_time_varying_sector_trajectory_tends_to_zero kappa hk hk3 phi hz hs initial

def constantFeedbackStable (gain : ℝ) : Prop :=
  ∀epsilon : ℝ,0<epsilon → ∃delta : ℝ,0<delta ∧
    ∀initial : ℝ,|initial|<delta → ∀n,|constantTrajectory gain initial n|<epsilon

theorem actual_strictly_schur_constant_feedback_is_lyapunov_stable (gain : ℝ)
    (hgain : -1/3<gain ∧ gain<3) : constantFeedbackStable gain := by
  have ha : |(4/5:ℝ)-3/5*gain|<1 := abs_lt.mpr ⟨by linarith [hgain.2],by linarith [hgain.1]⟩
  intro epsilon he
  refine ⟨epsilon,he,?_⟩
  intro initial hi n
  have hp : |(4/5:ℝ)-3/5*gain|^n≤1 := pow_le_one₀ (abs_nonneg _) ha.le
  rw [constantTrajectory,abs_mul,abs_pow]
  exact (mul_le_mul_of_nonneg_right hp (abs_nonneg initial)).trans_lt (by simpa using hi)

theorem actual_constant_gain_stability_and_attraction_range (gain : ℝ) :
    (constantFeedbackStable gain ∧
      ∀initial : ℝ,Tendsto (constantTrajectory gain initial) atTop (𝓝 0)) ↔
      -1/3<gain ∧ gain<3 := by
  constructor
  · intro h
    exact (actual_all_initial_constant_gain_decay_iff gain).mp h.2
  · intro h
    exact ⟨actual_strictly_schur_constant_feedback_is_lyapunov_stable gain h,
      (actual_all_initial_constant_gain_decay_iff gain).mpr h⟩

end SafeLearning.CompleteAppliedCircleConsequences
