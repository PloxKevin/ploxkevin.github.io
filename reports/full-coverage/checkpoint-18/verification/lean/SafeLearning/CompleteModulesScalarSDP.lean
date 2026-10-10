import SafeLearning.Modules

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteModulesScalarSDP

def scalarRho (alpha beta w0 w1 t : ℝ) : ℝ :=
  w0^2*((alpha+beta)^2*t^2/(2*t-w1^2)-2*alpha*beta*t)

theorem negative_scalar_schur_iff (a b c : ℝ) (hc : c < 0) :
    (∀ x y : ℝ, a*x^2+2*b*x*y+c*y^2 ≤ 0) ↔ a-b^2/c ≤ 0 := by
  constructor
  · intro h
    have hh := h 1 (-b/c)
    have hi : a*1^2+2*b*1*(-b/c)+c*(-b/c)^2=a-b^2/c := by
      field_simp; ring
    rwa [hi] at hh
  · intro h x y
    exact SafeLearning.Modules.negative_quadratic_from_schur hc h

theorem scalar_lipsdp_feasibility_iff (alpha beta w0 w1 t rho : ℝ)
    (ht : w1^2 < 2*t) :
    (∀ x y : ℝ, (-2*alpha*beta*w0^2*t-rho)*x^2+
      2*((alpha+beta)*w0*t)*x*y+(-2*t+w1^2)*y^2 ≤ 0) ↔
      scalarRho alpha beta w0 w1 t ≤ rho := by
  rw [negative_scalar_schur_iff _ _ _ (by linarith)]
  have hd : 2*t-w1^2 ≠ 0 := by linarith
  have hd' : -2*t+w1^2 ≠ 0 := by linarith
  have hi : (-2*alpha*beta*w0^2*t-rho)-((alpha+beta)*w0*t)^2/(-2*t+w1^2)=
      scalarRho alpha beta w0 w1 t-rho := by
    rw [show -2*t+w1^2= -(2*t-w1^2) by ring,div_neg,sub_neg_eq_add]
    unfold scalarRho
    field_simp [hd,show t*2-w1^2 ≠ 0 by simpa [mul_comm] using hd]
    ring
  rw [hi]
  constructor <;> intro h <;> linarith

theorem scalar_rho_gap_identity (alpha beta w0 w1 t : ℝ) (ht : 2*t-w1^2 ≠ 0) :
    scalarRho alpha beta w0 w1 t-beta^2*w0^2*w1^2=
      w0^2*((beta-alpha)*t-beta*w1^2)^2/(2*t-w1^2) := by
  unfold scalarRho
  field_simp [ht,show t*2-w1^2 ≠ 0 by simpa [mul_comm] using ht]
  ring

theorem scalar_rho_global_lower (alpha beta w0 w1 t : ℝ) (ht : w1^2 < 2*t) :
    beta^2*w0^2*w1^2 ≤ scalarRho alpha beta w0 w1 t := by
  have hi := scalar_rho_gap_identity alpha beta w0 w1 t (by linarith)
  have hn : 0 ≤ w0^2*((beta-alpha)*t-beta*w1^2)^2/(2*t-w1^2) := by positivity
  linarith

theorem scalar_optimal_multiplier_domain (alpha beta w1 : ℝ)
    (ha : 0 ≤ alpha) (hab : alpha < beta) (hw : w1 ≠ 0) :
    w1^2 < 2*(beta*w1^2/(beta-alpha)) := by
  have hd : 0 < beta-alpha := by linarith
  have hw' : 0 < w1^2 := sq_pos_of_ne_zero hw
  have hp : 0 < (alpha+beta)*w1^2 := mul_pos (by linarith) hw'
  rw [← mul_div_assoc]
  apply (lt_div_iff₀ hd).mpr
  nlinarith

theorem scalar_optimal_rho_attained (alpha beta w0 w1 : ℝ)
    (ha0 : 0 ≤ alpha) (ha : alpha < beta) (hw : w1 ≠ 0) :
    scalarRho alpha beta w0 w1 (beta*w1^2/(beta-alpha))=beta^2*w0^2*w1^2 := by
  have hd : beta-alpha ≠ 0 := by linarith
  have hdom := scalar_optimal_multiplier_domain alpha beta w1 ha0 ha hw
  have hden : 2*(beta*w1^2/(beta-alpha))-w1^2 ≠ 0 := by linarith
  have hi := scalar_rho_gap_identity alpha beta w0 w1
    (beta*w1^2/(beta-alpha)) hden
  have hn : (beta-alpha)*(beta*w1^2/(beta-alpha))-beta*w1^2=0 := by field_simp; ring
  rw [hn] at hi
  simp at hi
  linarith

theorem scalar_relu_certificate (x y : ℝ) :
    -36*x^2+24*x*y-4*y^2= -4*(3*x-y)^2 := by ring

theorem scalar_relu_upper (w0 w1 bias x y : ℝ) :
    |w1*max (w0*x+bias) 0-w1*max (w0*y+bias) 0| ≤ |w0*w1| * |x-y| := by
  have h := abs_max_sub_max_le_abs (w0*x+bias) (w0*y+bias) 0
  have hi : (w0*x+bias)-(w0*y+bias)=w0*(x-y) := by ring
  rw [hi,abs_mul] at h
  have ho : w1*max (w0*x+bias) 0-w1*max (w0*y+bias) 0=
      w1*(max (w0*x+bias) 0-max (w0*y+bias) 0) := by ring
  rw [ho,abs_mul,abs_mul]
  nlinarith [mul_le_mul_of_nonneg_left h (abs_nonneg w1)]

theorem scalar_relu_exact_gain_necessary (w0 w1 bias L : ℝ)
    (hL : 0 ≤ L) (hw0 : w0 ≠ 0)
    (hgain : ∀ x y : ℝ,
      |w1*max (w0*x+bias) 0-w1*max (w0*y+bias) 0| ≤ L*|x-y|) :
    |w0*w1| ≤ L := by
  have h := hgain ((2-bias)/w0) ((1-bias)/w0)
  have h₂ : w0*((2-bias)/w0)+bias=2 := by field_simp; ring
  have h₁ : w0*((1-bias)/w0)+bias=1 := by field_simp; ring
  have hd : ((2-bias)/w0)-((1-bias)/w0)=1/w0 := by ring
  rw [h₂,h₁,hd] at h
  norm_num at h
  have hden : 0 < |w0| := abs_pos.mpr hw0
  have hmul := mul_le_mul_of_nonneg_right h (le_of_lt hden)
  rw [abs_mul]
  have hi : |w0|⁻¹*|w0|=1 := inv_mul_cancel₀ (ne_of_gt hden)
  rw [show w1*2-w1=w1 by ring,mul_assoc,hi,mul_one] at hmul
  simpa [mul_comm] using hmul

theorem scalar_relu_example :
    (1:ℝ)^2*((13/10)^2)*((-7/10)^2)=8281/10000 ∧
    |(13/10:ℝ)*(-7/10)|=91/100 := by norm_num

end SafeLearning.CompleteModulesScalarSDP
