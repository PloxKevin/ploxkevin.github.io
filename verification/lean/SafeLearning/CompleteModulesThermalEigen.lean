import SafeLearning.CompleteModulesThermalTubes

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix Set Filter
namespace SafeLearning.CompleteModulesThermalEigen
open CompleteModulesThermalTubes CompleteModulesDynamics

def actualSlowEigenvector : E := WithLp.toLp 2 ![1,(1+Real.sqrt 5)/2]
def actualUnitSlowEigenvector : E := ‖actualSlowEigenvector‖⁻¹ • actualSlowEigenvector

theorem actual_slow_eigenvector_is_nonzero_and_has_the_true_source_eigenvalue :
    actualSlowEigenvector≠0 ∧ actualThermalOperator actualSlowEigenvector=
      thermalGain • actualSlowEigenvector := by
  constructor
  · intro h
    have he:=congrArg (fun x : E=>x 0) h
    norm_num [actualSlowEigenvector] at he
  · ext index
    fin_cases index
    · change actualThermalOperator actualSlowEigenvector 0=thermalGain*actualSlowEigenvector 0
      rw [(actual_thermal_operator_coordinates actualSlowEigenvector).1]
      change thermalFirst 1 ((1+Real.sqrt 5)/2)=thermalGain*1
      simpa only [mul_one] using thermal_gain_eigenvector.1
    · change actualThermalOperator actualSlowEigenvector 1=thermalGain*actualSlowEigenvector 1
      rw [(actual_thermal_operator_coordinates actualSlowEigenvector).2]
      exact thermal_gain_eigenvector.2

theorem actual_slow_eigenvector_normalization_has_norm_one_and_true_eigenvalue :
    ‖actualUnitSlowEigenvector‖=1 ∧ actualThermalOperator actualUnitSlowEigenvector=
      thermalGain • actualUnitSlowEigenvector := by
  have hn : 0<‖actualSlowEigenvector‖ := norm_pos_iff.mpr
    actual_slow_eigenvector_is_nonzero_and_has_the_true_source_eigenvalue.1
  constructor
  · rw [actualUnitSlowEigenvector,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hn]
    exact inv_mul_cancel₀ hn.ne'
  · rw [actualUnitSlowEigenvector,map_smul,
      actual_slow_eigenvector_is_nonzero_and_has_the_true_source_eigenvalue.2,
      smul_smul,smul_smul,mul_comm]

theorem actual_source_gain_is_attained_by_a_genuine_unit_vector :
    ‖actualUnitSlowEigenvector‖=1 ∧
      ‖actualThermalOperator actualUnitSlowEigenvector‖=thermalGain := by
  obtain ⟨hn,he⟩:=actual_slow_eigenvector_normalization_has_norm_one_and_true_eigenvalue
  refine ⟨hn,?_⟩
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos thermal_gain_positive_lt_one.1,hn,mul_one]

def actualSlowDisturbance : E := (1/20 : ℝ) • actualUnitSlowEigenvector
def actualSlowForcedEquilibrium : E := actualTubeRadius • actualUnitSlowEigenvector

theorem actual_source_constant_slow_forcing_has_the_literal_norm_and_equilibrium :
    ‖actualSlowDisturbance‖=1/20 ∧ ‖actualSlowForcedEquilibrium‖=actualTubeRadius ∧
      actualThermalOperator actualSlowForcedEquilibrium+actualSlowDisturbance=
        actualSlowForcedEquilibrium := by
  obtain ⟨hn,he⟩:=actual_slow_eigenvector_normalization_has_norm_one_and_true_eigenvalue
  obtain ⟨hr,hfixed⟩:=actual_source_tube_radius_is_positive_and_solves_the_fixed_radius_equation
  refine ⟨?_,?_,?_⟩
  · simp [actualSlowDisturbance,norm_smul,hn]
  · rw [actualSlowForcedEquilibrium,norm_smul,Real.norm_eq_abs,abs_of_pos hr,hn,mul_one]
  · rw [actualSlowForcedEquilibrium,actualSlowDisturbance,map_smul,he,smul_smul,←add_smul]
    congr 1
    linarith [hfixed]

theorem actual_nonzero_constant_forcing_gives_a_true_admissible_trajectory_without_zero_convergence :
    ∃ x w : ℕ→E,
      (∀ n,x (n+1)=actualThermalOperator (x n)+w n) ∧
      (∀ n,‖w n‖=1/20) ∧ (∀ n,‖x n‖=actualTubeRadius) ∧
      ¬Tendsto x atTop (nhds 0) := by
  obtain ⟨hw,hx,he⟩:=actual_source_constant_slow_forcing_has_the_literal_norm_and_equilibrium
  refine ⟨(fun _=>actualSlowForcedEquilibrium),(fun _=>actualSlowDisturbance),
    (fun _=>he.symm),(fun _=>hw),(fun _=>hx),?_⟩
  intro h
  have hn:=h.norm
  have hc : Tendsto (fun _ : ℕ=>‖actualSlowForcedEquilibrium‖) atTop
      (nhds actualTubeRadius) := by simpa only [hx] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ=>actualTubeRadius) atTop (nhds actualTubeRadius))
  have hz:=tendsto_nhds_unique hc hn
  simp only [norm_zero] at hz
  linarith [actual_source_tube_radius_is_positive_and_solves_the_fixed_radius_equation.1]

theorem actual_all_horizon_invariance_of_every_source_tube
    (x w : ℕ→E) (hstep : ∀ n,x (n+1)=actualThermalOperator (x n)+w n)
    (hw : ∀ n,‖w n‖≤1/20) (radius : ℝ) (hr : actualTubeRadius≤radius)
    (hzero : ‖x 0‖≤radius) : ∀ n,‖x n‖≤radius := by
  intro n
  induction n with
  | zero => exact hzero
  | succ n ih => rw [hstep];exact actual_tube_radius_invariant_step _ _ _ ih (hw n) hr

theorem actual_source_coordinate_bound_converts_to_degrees
    (x : E) (index : Fin 2) (bound : ℝ) (hx : |x index|≤bound) :
    |5*x index|≤5*bound := by
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<5)]
  exact mul_le_mul_of_nonneg_left hx (by norm_num)

end SafeLearning.CompleteModulesThermalEigen
