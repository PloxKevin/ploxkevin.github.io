import SafeLearning.CompleteDualPILinearModel

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Filter
open scoped Topology
open SafeLearning.CompleteDualPILinearModel
namespace SafeLearning.CompleteDualPIOscillation

def actualPureTrajectory (gain : ℝ) (initial : ℝ×ℝ) : ℕ→ℝ×ℝ
  | 0 => initial
  | n+1 => ((1-gain)*(actualPureTrajectory gain initial n).1-
      gain*(actualPureTrajectory gain initial n).2,
      (actualPureTrajectory gain initial n).2+(actualPureTrajectory gain initial n).1)

theorem actual_pure_trajectory_is_source_loop (c ki : ℝ) (initial : ℝ×ℝ) (n : ℕ) :
    actualPureTrajectory (c*ki) initial (n+1)=
      loopStep 1 c 0 ki (actualPureTrajectory (c*ki) initial n).1
        (actualPureTrajectory (c*ki) initial n).2 := by
  simp [actualPureTrajectory,loopStep]

theorem actual_every_pure_trajectory_preserves_energy
    (gain : ℝ) (state : ℕ→ℝ×ℝ)
    (hrec : ∀ n,state (n+1)=((1-gain)*(state n).1-gain*(state n).2,
      (state n).2+(state n).1)) (n : ℕ) :
    oscillatorEnergy gain (state n).1 (state n).2=
      oscillatorEnergy gain (state 0).1 (state 0).2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [hrec]
    simpa only [actual_pure_integral_energy_conserved] using ih

theorem actual_nonzero_pure_trajectory_does_not_decay_to_origin
    (gain : ℝ) (hgain : 0<gain ∧ gain<4) (state : ℕ→ℝ×ℝ)
    (hrec : ∀ n,state (n+1)=((1-gain)*(state n).1-gain*(state n).2,
      (state n).2+(state n).1)) (hnonzero : (state 0).1≠0 ∨ (state 0).2≠0) :
    ¬(Tendsto (fun n=>(state n).1) atTop (𝓝 0) ∧
      Tendsto (fun n=>(state n).2) atTop (𝓝 0)) := by
  rintro ⟨he,hd⟩
  have hp := actual_pure_integral_energy_positive gain (state 0).1 (state 0).2 hgain hnonzero
  have hlim : Tendsto (fun n=>oscillatorEnergy gain (state n).1 (state n).2) atTop (𝓝 0) := by
    simpa [oscillatorEnergy] using ((he.pow 2).add ((he.const_mul gain).mul hd)).add
      ((hd.pow 2).const_mul gain)
  have heq : (fun n=>oscillatorEnergy gain (state n).1 (state n).2)=
      (fun _ : ℕ=>oscillatorEnergy gain (state 0).1 (state 0).2) := by
    funext n
    exact actual_every_pure_trajectory_preserves_energy gain state hrec n
  rw [heq] at hlim
  have hz : oscillatorEnergy gain (state 0).1 (state 0).2=0 :=
    tendsto_nhds_unique tendsto_const_nhds hlim
  linarith

theorem actual_pure_integral_has_a_nondecaying_source_trajectory
    (c ki : ℝ) (hgain : 0<c*ki ∧ c*ki<4) :
    (actualPureTrajectory (c*ki) (1,0) 0=(1,0)) ∧
      (∀ n,actualPureTrajectory (c*ki) (1,0) (n+1)=
        loopStep 1 c 0 ki (actualPureTrajectory (c*ki) (1,0) n).1
          (actualPureTrajectory (c*ki) (1,0) n).2) ∧
      ¬(Tendsto (fun n=>(actualPureTrajectory (c*ki) (1,0) n).1) atTop (𝓝 0) ∧
        Tendsto (fun n=>(actualPureTrajectory (c*ki) (1,0) n).2) atTop (𝓝 0)) := by
  refine ⟨rfl,actual_pure_trajectory_is_source_loop c ki (1,0),?_⟩
  apply actual_nonzero_pure_trajectory_does_not_decay_to_origin (c*ki) hgain
    (actualPureTrajectory (c*ki) (1,0))
  · intro n
    rfl
  · norm_num [actualPureTrajectory]

theorem actual_pure_integral_frequency_angle (gain : ℝ) (hgain : 0<gain ∧ gain<4) :
    0<Real.arccos (1-gain/2) ∧ Real.arccos (1-gain/2)<Real.pi ∧
      Real.cos (Real.arccos (1-gain/2))=1-gain/2 ∧
      complexRoot (2-gain) 1=
        Complex.exp ((Real.arccos (1-gain/2):ℂ)*Complex.I) := by
  have hl : -1<1-gain/2 := by linarith
  have hu : 1-gain/2<1 := by linarith
  refine ⟨Real.arccos_pos.mpr hu,Real.arccos_lt_pi.mpr hl,
    Real.cos_arccos hl.le hu.le,?_⟩
  rw [Complex.exp_ofReal_mul_I,Real.cos_arccos hl.le hu.le,Real.sin_arccos]
  unfold complexRoot
  congr 1
  · congr 1
    ring
  · congr 2
    ring

theorem actual_angular_mode_has_constant_pure_amplitude (gain : ℝ)
    (hgain : 0<gain ∧ gain<4) (n : ℕ) :
    ‖(complexRoot (2-gain) 1)^n‖=1 := by
  have hc : ((2-gain)/2)^2 < (1:ℝ) := by
    nlinarith [mul_pos hgain.1 (sub_pos.mpr hgain.2)]
  rw [norm_pow,(actual_complex_root_modulus (2-gain) 1 hc).2.1]
  norm_num

end SafeLearning.CompleteDualPIOscillation
