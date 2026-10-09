import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Matrix
namespace SafeLearning.CompleteDualPILinearModel

/-- The actual two-state source loop, including its optional curvature coefficient. -/
def loopMatrix (a c kp ki : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![a-c*(kp+ki), -c*ki; 1, 1]

def loopStep (a c kp ki e delta : ℝ) : ℝ × ℝ :=
  ((a-c*(kp+ki))*e-c*ki*delta,delta+e)

theorem actual_state_matrix (a c kp ki e delta : ℝ) :
    (loopMatrix a c kp ki).mulVec ![e,delta] =
      ![(loopStep a c kp ki e delta).1,(loopStep a c kp ki e delta).2] := by
  ext i
  fin_cases i <;> simp [loopMatrix,loopStep,Matrix.mulVec,Fin.sum_univ_two] <;> ring

theorem actual_shifted_integral_recurrence (c kp ki target e integral : ℝ)
    (hki : ki ≠ 0) :
    e-c*(kp*e+ki*(integral+e)-target) =
      (loopStep 1 c kp ki e (integral-target/ki)).1 ∧
    integral+e-target/ki = (loopStep 1 c kp ki e (integral-target/ki)).2 := by
  constructor
  · unfold loopStep
    field_simp
    <;> ring
  · simp [loopStep]
    ring

theorem actual_trace_and_determinant (a c kp ki : ℝ) :
    Matrix.trace (loopMatrix a c kp ki) = 1+a-c*(kp+ki) ∧
      Matrix.det (loopMatrix a c kp ki) = a-c*kp := by
  constructor
  · simp [Matrix.trace,loopMatrix,Fin.sum_univ_two]
    ring
  · simp [loopMatrix,Matrix.det_fin_two]
    ring

def characteristic (trace determinant : ℝ) (z : ℂ) : ℂ :=
  z^2-(trace:ℂ)*z+(determinant:ℂ)

theorem actual_characteristic_determinant (a c kp ki : ℝ) (z : ℂ) :
    Matrix.det (z • (1 : Matrix (Fin 2) (Fin 2) ℂ) -
      (loopMatrix a c kp ki).map (algebraMap ℝ ℂ)) =
      characteristic (1+a-c*(kp+ki)) (a-c*kp) z := by
  simp [Matrix.det_fin_two,loopMatrix,characteristic]
  push_cast
  ring

def complexRoot (trace determinant : ℝ) : ℂ :=
  (trace/2:ℝ) + (Real.sqrt (determinant-(trace/2)^2):ℂ)*Complex.I

theorem actual_complex_root_factorization (trace determinant : ℝ)
    (hcomplex : (trace/2)^2 < determinant) (z : ℂ) :
    characteristic trace determinant z =
      (z-complexRoot trace determinant)*(z-star (complexRoot trace determinant)) := by
  have hs := Real.sq_sqrt (le_of_lt (sub_pos.mpr hcomplex))
  simp only [pow_two] at hs
  apply Complex.ext <;>
    simp [characteristic,complexRoot,Complex.mul_re,Complex.mul_im,pow_two] <;>
    nlinarith

theorem actual_all_complex_roots (trace determinant : ℝ)
    (hcomplex : (trace/2)^2 < determinant) (z : ℂ) :
    characteristic trace determinant z=0 ↔
      z=complexRoot trace determinant ∨ z=star (complexRoot trace determinant) := by
  rw [actual_complex_root_factorization trace determinant hcomplex,mul_eq_zero,
    sub_eq_zero,sub_eq_zero]

theorem actual_complex_root_modulus (trace determinant : ℝ)
    (hcomplex : (trace/2)^2 < determinant) :
    Complex.normSq (complexRoot trace determinant)=determinant ∧
      ‖complexRoot trace determinant‖=Real.sqrt determinant ∧
      0<(complexRoot trace determinant).im := by
  have hp : 0 < determinant-(trace/2)^2 := sub_pos.mpr hcomplex
  have hs := Real.sq_sqrt hp.le
  have hn : Complex.normSq (complexRoot trace determinant)=determinant := by
    simp [complexRoot,Complex.normSq_apply,pow_two] at *
    nlinarith
  refine ⟨hn,?_,?_⟩
  · rw [Complex.norm_def,hn]
  · simpa [complexRoot] using Real.sqrt_pos.mpr hp

theorem actual_any_nonreal_root_has_source_modulus (trace determinant : ℝ) (z : ℂ)
    (hroot : characteristic trace determinant z=0) (him : z.im≠0) :
    2*z.re=trace ∧ Complex.normSq z=determinant ∧ ‖z‖=Real.sqrt determinant := by
  have hr := congrArg Complex.re hroot
  have hi := congrArg Complex.im hroot
  simp [characteristic,Complex.mul_re,Complex.mul_im,pow_two] at hr hi
  have ht : 2*z.re=trace := by
    have h : z.im*(2*z.re-trace)=0 := by nlinarith
    rcases mul_eq_zero.mp h with hz | hz
    · exact False.elim (him hz)
    · linarith
  have hn : Complex.normSq z=determinant := by
    rw [Complex.normSq_apply]
    have hm := congrArg (fun t : ℝ => t*z.re) ht
    nlinarith [hm]
  exact ⟨ht,hn,by rw [Complex.norm_def,hn]⟩

theorem pure_integral_roots_have_unit_modulus (c ki : ℝ)
    (hgain : 0<c*ki ∧ c*ki<4) (z : ℂ)
    (hroot : characteristic (2-c*ki) 1 z=0) : ‖z‖=1 := by
  have hc : ((2-c*ki)/2)^2 < (1:ℝ) := by
    nlinarith [mul_pos hgain.1 (sub_pos.mpr hgain.2)]
  rcases (actual_all_complex_roots (2-c*ki) 1 hc z).mp hroot with hz | hz
  · rw [hz,(actual_complex_root_modulus (2-c*ki) 1 hc).2.1]
    norm_num
  · rw [hz,norm_star,(actual_complex_root_modulus (2-c*ki) 1 hc).2.1]
    norm_num

theorem proportional_complex_roots_decay_factor (c kp ki : ℝ)
    (hkp : 0<c*kp) (hcomplex : ((2-c*(kp+ki))/2)^2 < 1-c*kp) (z : ℂ)
    (hroot : characteristic (2-c*(kp+ki)) (1-c*kp) z=0) :
    ‖z‖=Real.sqrt (1-c*kp) ∧ ‖z‖<1 := by
  have hn : ‖z‖=Real.sqrt (1-c*kp) := by
    rcases (actual_all_complex_roots _ _ hcomplex z).mp hroot with hz | hz
    · rw [hz];exact (actual_complex_root_modulus _ _ hcomplex).2.1
    · rw [hz,norm_star];exact (actual_complex_root_modulus _ _ hcomplex).2.1
  refine ⟨hn,?_⟩
  rw [hn]
  have hnonneg : 0≤1-c*kp := by nlinarith [sq_nonneg ((2-c*(kp+ki))/2)]
  exact (Real.sqrt_lt hnonneg (by norm_num : (0:ℝ)≤1)).mpr (by linarith)

/-- The source Jury inequalities, with no assumed positivity of the curvature. -/
theorem actual_curved_jury_gain_region (a c kp ki : ℝ) :
    |a-c*kp|<1 ∧ |1+a-c*(kp+ki)|<1+(a-c*kp) ↔
      a-1<c*kp ∧ c*kp<a+1 ∧ 0<c*ki ∧ c*(2*kp+ki)<2*(1+a) := by
  simp only [abs_lt]
  constructor
  · rintro ⟨⟨h1,h2⟩,h3,h4⟩
    refine ⟨?_,?_,?_,?_⟩ <;> nlinarith
  · rintro ⟨h1,h2,h3,h4⟩
    refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩ <;> nlinarith

theorem actual_uncurved_jury_gain_region (c kp ki : ℝ) :
    |1-c*kp|<1 ∧ |2-c*(kp+ki)|<1+(1-c*kp) ↔
      0<c*kp ∧ c*kp<2 ∧ 0<c*ki ∧ c*(2*kp+ki)<4 := by
  have h := actual_curved_jury_gain_region 1 c kp ki
  norm_num at h
  exact h

def oscillatorEnergy (gain e delta : ℝ) : ℝ := e^2+gain*e*delta+gain*delta^2

theorem actual_pure_integral_energy_conserved (gain e delta : ℝ) :
    oscillatorEnergy gain ((1-gain)*e-gain*delta) (delta+e)=
      oscillatorEnergy gain e delta := by
  unfold oscillatorEnergy
  ring

theorem actual_pure_integral_energy_positive (gain e delta : ℝ)
    (hgain : 0<gain ∧ gain<4) (hstate : e≠0 ∨ delta≠0) :
    0<oscillatorEnergy gain e delta := by
  have hid : oscillatorEnergy gain e delta =
      (e+gain*delta/2)^2+gain*(1-gain/4)*delta^2 := by unfold oscillatorEnergy;ring
  rw [hid]
  by_cases hd : delta=0
  · subst delta
    simp only [ne_eq,not_true_eq_false,or_false] at hstate
    simpa using sq_pos_of_ne_zero hstate
  · have hp : 0<gain*(1-gain/4)*delta^2 :=
      mul_pos (mul_pos hgain.1 (by linarith)) (sq_pos_of_ne_zero hd)
    nlinarith [sq_nonneg (e+gain*delta/2)]

theorem actual_source_numeric_trace_and_discriminant :
    2-(2/5:ℝ)*(1/2+1/10)=44/25 ∧
      1-(2/5:ℝ)*(1/2)=4/5 ∧
      (44/25:ℝ)^2=1936/625 ∧ (44/25:ℝ)^2<4*(4/5) ∧
      (44/25:ℝ)^2≠31/10 := by norm_num

theorem actual_source_damped_modulus_rounding :
    |Real.sqrt (4/5:ℝ)-894/1000|<1/2000 ∧
      Real.sqrt (4/5:ℝ)≠894/1000 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤4/5)
  have hn := Real.sqrt_nonneg (4/5:ℝ)
  constructor
  · rw [abs_lt]
    constructor <;> nlinarith
  · intro he
    rw [he] at hs
    norm_num at hs

theorem learning_rate_and_cost_scale_gain_identities (eta b kp ki kappa : ℝ) :
    loopMatrix 1 (2*eta*b^2) kp ki = loopMatrix 1 (eta*b^2) (2*kp) (2*ki) ∧
      eta*(kappa*b)^2=kappa^2*(eta*b^2) := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [loopMatrix] <;> ring
  · ring

end SafeLearning.CompleteDualPILinearModel
