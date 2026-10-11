import SafeLearning.CompleteAppliedScalarEnergyBound

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SafeLearning.CompleteAppliedScalarEnergyAttainers

def pulseInput (rate time : ℝ) : ℝ := Real.exp (-rate*time)
def pulseState (rate time : ℝ) : ℝ :=
  (Real.exp (-rate*time)-Real.exp (-2*time))/(2-rate)

theorem actual_exponential_pulse_has_the_true_zero_initial_ode
    (rate : ℝ) (hne : rate ≠ 2) :
    pulseState rate 0=0 ∧ ∀time:ℝ,
      HasDerivAt (pulseState rate) (-2*pulseState rate time+pulseInput rate time) time := by
  refine ⟨by simp [pulseState],?_⟩
  intro time
  have hd := ((((hasDerivAt_id time).const_mul (-rate)).exp).sub
    (((hasDerivAt_id time).const_mul (-2)).exp)).div_const (2-rate)
  have hd' : HasDerivAt (pulseState rate)
      ((Real.exp (-rate*time)*(-rate)-Real.exp (-2*time)*(-2))/(2-rate)) time := by
    change HasDerivAt (fun point:ℝ=>(Real.exp (-rate*point)-Real.exp (-2*point))/(2-rate)) _ time
    simpa only [id_eq,Pi.sub_apply,mul_one] using hd
  convert hd' using 1
  unfold pulseState pulseInput
  field_simp [sub_ne_zero.mpr hne.symm]
  ring

theorem actual_exponential_pulse_input_and_output_have_finite_energy
    (rate : ℝ) (hr : 0<rate) :
    MemLp (pulseInput rate) 2 (volume.restrict (Ioi (0:ℝ))) ∧
      MemLp (pulseState rate) 2 (volume.restrict (Ioi (0:ℝ))) := by
  have hi (c : ℝ) (hc : 0<c) :
      MemLp (fun time:ℝ=>Real.exp (-c*time)) 2 (volume.restrict (Ioi (0:ℝ))) := by
    apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
    have he : (fun time:ℝ=>Real.exp (-c*time)^2)=
        (fun time:ℝ=>Real.exp (-(2*c)*time)) := by
      funext time
      rw [←Real.exp_nat_mul]
      congr 1
      ring
    rw [he]
    exact integrableOn_exp_mul_Ioi (by linarith : -(2*c)<0) 0
  refine ⟨hi rate hr,?_⟩
  unfold pulseState
  simpa only [div_eq_mul_inv,Pi.sub_apply] using ((hi rate hr).sub (hi 2 (by norm_num))).mul_const ((2-rate)⁻¹)

theorem actual_exponential_input_energy (rate : ℝ) (hr : 0<rate) :
    (∫time in Ioi (0:ℝ),pulseInput rate time^2)=1/(2*rate) := by
  have he : (fun time:ℝ=>pulseInput rate time^2)=
      (fun time:ℝ=>Real.exp (-(2*rate)*time)) := by
    funext time
    unfold pulseInput
    rw [←Real.exp_nat_mul]
    congr 1
    ring
  rw [he,integral_exp_mul_Ioi (by linarith : -(2*rate)<0)]
  simp

theorem actual_exponential_output_energy (rate : ℝ) (hr : 0<rate) (hne : rate ≠ 2) :
    (∫time in Ioi (0:ℝ),pulseState rate time^2)=1/(4*rate*(rate+2)) := by
  have h1 := integrableOn_exp_mul_Ioi (by linarith : -(2*rate)<0) (0:ℝ)
  have h2 := (integrableOn_exp_mul_Ioi (by linarith : -(rate+2)<0) (0:ℝ)).const_mul 2
  have h3 := integrableOn_exp_mul_Ioi (by norm_num : (-4:ℝ)<0) (0:ℝ)
  have he : (fun time:ℝ=>pulseState rate time^2)=
      (fun time:ℝ=>(Real.exp (-(2*rate)*time)-2*Real.exp (-(rate+2)*time)+Real.exp (-4*time))/(2-rate)^2) := by
    funext time
    unfold pulseState
    rw [div_pow]
    congr 1
    have ha : Real.exp (-rate*time)^2=Real.exp (-(2*rate)*time) := by
      rw [←Real.exp_nat_mul];congr 1;ring
    have hb : Real.exp (-2*time)^2=Real.exp (-4*time) := by
      rw [←Real.exp_nat_mul];congr 1;ring
    have hc : Real.exp (-rate*time)*Real.exp (-2*time)=Real.exp (-(rate+2)*time) := by
      rw [←Real.exp_add];congr 1;ring
    rw [sub_sq,ha,hb]
    calc
      _=Real.exp (-(2*rate)*time)-2*(Real.exp (-rate*time)*Real.exp (-2*time))+Real.exp (-4*time) := by ring
      _=_ := by rw [hc]
  have hadd := integral_add (h1.sub h2) h3
  have hsub := integral_sub h1 h2
  simp only [Pi.sub_apply] at hadd
  rw [he,integral_div,hadd,hsub,
    integral_const_mul,integral_exp_mul_Ioi (by linarith : -(2*rate)<0),
    integral_exp_mul_Ioi (by linarith : -(rate+2)<0),
    integral_exp_mul_Ioi (by norm_num : (-4:ℝ)<0)]
  simp only [mul_zero,Real.exp_zero]
  field_simp [hr.ne',sub_ne_zero.mpr hne.symm,show rate+2≠0 by linarith]
  ring

end SafeLearning.CompleteAppliedScalarEnergyAttainers
