import SafeLearning.CompleteDualPIStability
import SafeLearning.CompleteDualPIOscillation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Matrix Filter
open scoped BigOperators Topology
namespace SafeLearning.CompleteAppliedMultiplierLoop
open SafeLearning.CompleteDualPILinearModel
open SafeLearning.CompleteDualPIStability
open SafeLearning.CompleteDualPIOscillation

def sourceMatrix (c kp ki : ℝ) := loopMatrix 1 c kp ki
def complexMatrix (c kp ki : ℝ) := (sourceMatrix c kp ki).map Complex.ofReal

theorem actual_source_trace_and_determinant (c kp ki : ℝ) :
    (sourceMatrix c kp ki).trace=2-c*(kp+ki) ∧
      (sourceMatrix c kp ki).det=1-c*kp := by
  have h := actual_trace_and_determinant 1 c kp ki
  norm_num at h
  exact h

theorem actual_official_complex_spectrum_is_the_source_characteristic
    (c kp ki : ℝ) (z : ℂ) :
    z∈spectrum ℂ (complexMatrix c kp ki) ↔
      characteristic (2-c*(kp+ki)) (1-c*kp) z=0 := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
  change (complexMatrix c kp ki).charpoly.eval z=0 ↔ _
  have he : (complexMatrix c kp ki).charpoly.eval z=
      characteristic (2-c*(kp+ki)) (1-c*kp) z := by
    rw [Matrix.charpoly_fin_two]
    simp [complexMatrix,sourceMatrix,loopMatrix,Matrix.trace,Fin.sum_univ_two,
      Matrix.det_fin_two,characteristic]
    ring
  rw [he]

theorem actual_pure_integral_has_nonreal_eigenvalues_iff (c ki : ℝ) :
    (∃z : ℂ,z∈spectrum ℂ (complexMatrix c 0 ki) ∧ z.im≠0) ↔
      0<c*ki ∧ c*ki<4 := by
  constructor
  · rintro ⟨z,hz,him⟩
    rw [actual_official_complex_spectrum_is_the_source_characteristic] at hz
    have hz' : characteristic (2-c*ki) 1 z=0 := by simpa using hz
    obtain ⟨hr,hn,_⟩ := actual_any_nonreal_root_has_source_modulus (2-c*ki) 1 z hz' him
    rw [Complex.normSq_apply] at hn
    have hs := congrArg (fun x : ℝ=>x^2) hr
    have hp : 0<(c*ki)*(4-c*ki) := by nlinarith [hs,sq_pos_of_ne_zero him]
    constructor
    · by_contra h
      have hg : c*ki≤0 := le_of_not_gt h
      have hm := mul_nonpos_of_nonpos_of_nonneg hg (show 0≤4-c*ki by linarith)
      linarith
    · by_contra h
      have hg : 4≤c*ki := le_of_not_gt h
      have hm := mul_nonpos_of_nonneg_of_nonpos (show 0≤c*ki by linarith)
        (show 4-c*ki≤0 by linarith)
      linarith
  · intro h
    have hc : ((2-c*ki)/2)^2<(1:ℝ) := by
      nlinarith [mul_pos h.1 (sub_pos.mpr h.2)]
    refine ⟨complexRoot (2-c*ki) 1,?_,?_⟩
    · rw [actual_official_complex_spectrum_is_the_source_characteristic]
      have hh := (actual_all_complex_roots (2-c*ki) 1 hc
        (complexRoot (2-c*ki) 1)).mpr (Or.inl rfl)
      simpa using hh
    · exact ne_of_gt (actual_complex_root_modulus (2-c*ki) 1 hc).2.2

theorem actual_pure_integral_unit_circle_and_source_angle (c ki : ℝ)
    (h : 0<c*ki ∧ c*ki<4) :
    (∀z∈spectrum ℂ (complexMatrix c 0 ki),‖z‖=1) ∧
      Real.cos (Real.arccos (1-c*ki/2))=1-c*ki/2 ∧
      complexRoot (2-c*ki) 1=
        Complex.exp ((Real.arccos (1-c*ki/2):ℂ)*Complex.I) := by
  refine ⟨?_,(actual_pure_integral_frequency_angle (c*ki) h).2.2.1,
    (actual_pure_integral_frequency_angle (c*ki) h).2.2.2⟩
  intro z hz
  rw [actual_official_complex_spectrum_is_the_source_characteristic] at hz
  exact pure_integral_roots_have_unit_modulus c ki h z (by simpa using hz)

theorem actual_gain_one_pure_loop_has_period_six :
    (sourceMatrix 1 0 1)^6=1 ∧ Real.arccos (1-(1:ℝ)/2)=Real.pi/3 := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [sourceMatrix,loopMatrix,pow_succ,Matrix.mul_apply,Fin.sum_univ_two,
        Matrix.one_apply]
  · rw [show (1-(1:ℝ)/2)=(1/2:ℝ) by norm_num,←Real.cos_pi_div_three]
    exact Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])

theorem actual_every_gain_one_pure_source_trajectory_repeats_after_six
    (state : ℕ→ℝ×ℝ)
    (hrec : ∀n,state (n+1)=loopStep 1 1 0 1 (state n).1 (state n).2) (n : ℕ) :
    state (n+6)=state n := by
  rw [show n+6=n+5+1 by omega,hrec,
    show n+5=n+4+1 by omega,hrec,
    show n+4=n+3+1 by omega,hrec,
    show n+3=n+2+1 by omega,hrec,
    show n+2=n+1+1 by omega,hrec,hrec n]
  apply Prod.ext <;> simp [loopStep] <;> ring

theorem actual_source_Schur_region_and_all_trajectory_decay (c kp ki : ℝ) :
    ((∀z∈spectrum ℂ (complexMatrix c kp ki),‖z‖<1) ↔
      0<c*kp ∧ c*kp<2 ∧ 0<c*ki ∧ c*(2*kp+ki)<4) ∧
    ((∀state : ℕ→ℝ×ℝ,
      (∀n,state (n+1)=loopStep 1 c kp ki (state n).1 (state n).2) →
      Tendsto (fun n=>(state n).1) atTop (𝓝 0) ∧
        Tendsto (fun n=>(state n).2) atTop (𝓝 0)) ↔
      0<c*kp ∧ c*kp<2 ∧ 0<c*ki ∧ c*(2*kp+ki)<4) := by
  constructor
  · simp only [actual_official_complex_spectrum_is_the_source_characteristic]
    exact SafeLearning.CompleteDualPIJury.actual_uncurved_spectral_stability_region c kp ki
  · exact actual_all_source_uncurved_trajectories_decay_iff_gain_region c kp ki

theorem actual_numeric_loop_spectrum_and_eight_step_envelope :
    (∀z : ℂ,z∈spectrum ℂ (complexMatrix 1 (1/2) (1/2)) ↔
      z=(1/2:ℂ)+(1/2:ℂ)*Complex.I ∨ z=(1/2:ℂ)-(1/2:ℂ)*Complex.I) ∧
    (sourceMatrix 1 (1/2) (1/2))^8=(1/16:ℝ) • (1:Matrix (Fin 2) (Fin 2) ℝ) := by
  constructor
  · intro z
    rw [actual_official_complex_spectrum_is_the_source_characteristic]
    have hf : characteristic (2-(1:ℝ)*(1/2+1/2)) (1-(1:ℝ)*(1/2)) z=
      (z-((1/2:ℂ)+(1/2:ℂ)*Complex.I))*(z-((1/2:ℂ)-(1/2:ℂ)*Complex.I)) := by
      apply Complex.ext <;>
        simp [characteristic,Complex.mul_re,Complex.mul_im,pow_two] <;> ring
    rw [hf,mul_eq_zero,sub_eq_zero,sub_eq_zero]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [sourceMatrix,loopMatrix,pow_succ,Matrix.mul_apply,Fin.sum_univ_two,
        Matrix.one_apply,Matrix.smul_apply]

theorem actual_numeric_eigenmode_has_the_true_angle_modulus_and_rounding :
    (1/2:ℂ)+(1/2:ℂ)*Complex.I=
      (Real.sqrt (1/2:ℝ):ℂ)*Complex.exp ((Real.pi/4:ℂ)*Complex.I) ∧
    ‖(1/2:ℂ)+(1/2:ℂ)*Complex.I‖=Real.sqrt (1/2:ℝ) ∧
    |Real.sqrt (1/2:ℝ)-707/1000|<1/2000 ∧ Real.sqrt (1/2:ℝ)≠707/1000 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤1/2)
  have hn := Real.sqrt_nonneg (1/2:ℝ)
  have hs2 := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hn2 := Real.sqrt_nonneg (2:ℝ)
  have hp : Real.sqrt (1/2:ℝ)*Real.sqrt 2=1 := by
    rw [←Real.sqrt_mul (by norm_num),show (1/2:ℝ)*2=1 by norm_num,Real.sqrt_one]
  refine ⟨?_,?_,?_,?_⟩
  · rw [show (Real.pi/4:ℂ)=((Real.pi/4:ℝ):ℂ) by push_cast;ring,
      Complex.exp_ofReal_mul_I,Real.cos_pi_div_four,Real.sin_pi_div_four]
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im] <;> nlinarith
  · rw [Complex.norm_def]
    norm_num [Complex.normSq_apply]
  · rw [abs_lt]
    constructor <;> nlinarith
  · intro h
    nlinarith

end SafeLearning.CompleteAppliedMultiplierLoop
