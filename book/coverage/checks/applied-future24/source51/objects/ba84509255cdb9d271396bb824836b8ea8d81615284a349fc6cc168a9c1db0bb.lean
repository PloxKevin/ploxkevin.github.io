import SafeLearning.CompleteModulesGoSafeToyIslands
import SafeLearning.CompleteFoundationsCosineNumerics
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Set
namespace SafeLearning.CompleteModulesGoSafeToyBoundaryNumerics
open SafeLearning.CompleteModulesGoSafeToyIslands SafeLearning.CompleteFoundationsCosineNumerics

def actualDoubleAngleCosinePolynomial (x : ℝ) : ℝ := 2*(cosPoly (x/2))^2-1

theorem actual_cosine_rational_double_angle_polynomial_error
    (x : ℝ) (hx : |x| ≤ 2) :
    |Real.cos x-actualDoubleAngleCosinePolynomial x| ≤ 1/1000000000 := by
  have hh : |x/2| ≤ 1 := by rw [abs_div]; norm_num; linarith
  have he := actual_real_cosine_uniform_rational_error (x/2) hh
  have hc : |Real.cos (x/2)| ≤ 1 := Real.abs_cos_le_one _
  have hp : |cosPoly (x/2)| ≤ 1+1/80000000000 := by
    calc
      |cosPoly (x/2)|=|Real.cos (x/2)-(Real.cos (x/2)-cosPoly (x/2))| := by ring_nf
      _ ≤ |Real.cos (x/2)|+|Real.cos (x/2)-cosPoly (x/2)| := abs_sub _ _
      _ ≤ 1+1/80000000000 := add_le_add hc he
  have hsum : |Real.cos (x/2)+cosPoly (x/2)| ≤ 2+1/80000000000 := by
    exact (abs_add_le _ _).trans (by linarith)
  have hdouble : Real.cos x=2*(Real.cos (x/2))^2-1 := by
    have hxid : 2*(x/2)=x := by ring
    simpa only [hxid] using Real.cos_two_mul (x/2)
  have hid : Real.cos x-actualDoubleAngleCosinePolynomial x=
      2*(Real.cos (x/2)-cosPoly (x/2))*(Real.cos (x/2)+cosPoly (x/2)) := by
    rw [hdouble]
    unfold actualDoubleAngleCosinePolynomial
    ring
  rw [hid,abs_mul,abs_mul]
  norm_num only [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  calc
    2 * |Real.cos (x/2)-cosPoly (x/2)| * |Real.cos (x/2)+cosPoly (x/2)|
        ≤ (2*(1/80000000000))*(2+1/80000000000) :=
      mul_le_mul (mul_le_mul_of_nonneg_left he (by norm_num)) hsum (abs_nonneg _) (by norm_num)
    _ ≤ 1/1000000000 := by norm_num

theorem actual_four_rational_angle_checks_for_the_printed_boundary_roundings :
    (5/12:ℝ) < Real.cos (4*(3141593/1000000)*(363/4000)) ∧
      Real.cos (4*(3141592/1000000)*(1817/20000)) < 5/12 ∧
      (5/16:ℝ) < Real.cos (4*(3141593/1000000)*(1993/20000)) ∧
      Real.cos (4*(3141592/1000000)*(399/4000)) < 5/16 ∧
      Real.cos (4*(3141592/1000000)*(227/2500)) < 5/12 ∧
      (5/16:ℝ) < Real.cos (4*(3141593/1000000)*(997/10000)) := by
  have h₁ := actual_cosine_rational_double_angle_polynomial_error
    (4*(3141593/1000000)*(363/4000)) (by norm_num)
  have h₂ := actual_cosine_rational_double_angle_polynomial_error
    (4*(3141592/1000000)*(1817/20000)) (by norm_num)
  have h₃ := actual_cosine_rational_double_angle_polynomial_error
    (4*(3141593/1000000)*(1993/20000)) (by norm_num)
  have h₄ := actual_cosine_rational_double_angle_polynomial_error
    (4*(3141592/1000000)*(399/4000)) (by norm_num)
  have h₅ := actual_cosine_rational_double_angle_polynomial_error
    (4*(3141592/1000000)*(227/2500)) (by norm_num)
  have h₆ := actual_cosine_rational_double_angle_polynomial_error
    (4*(3141593/1000000)*(997/10000)) (by norm_num)
  norm_num [actualDoubleAngleCosinePolynomial,cosPoly] at h₁ h₂ h₃ h₄ h₅ h₆
  constructor
  · linarith [(abs_le.mp h₁).1]
  constructor
  · linarith [(abs_le.mp h₂).2]
  constructor
  · linarith [(abs_le.mp h₃).1]
  constructor
  · linarith [(abs_le.mp h₄).2]
  constructor
  · linarith [(abs_le.mp h₅).2]
  · linarith [(abs_le.mp h₆).1]

theorem actual_boundary_three_and_eight_have_true_nearest_four_decimal_enclosures :
    (363/4000:ℝ) < actualBoundary 3 ∧ actualBoundary 3 < 1817/20000 ∧
      (1993/20000:ℝ) < actualBoundary 8 ∧ actualBoundary 8 < 399/4000 ∧
      actualBoundary 3 < 227/2500 ∧ (997/10000:ℝ) < actualBoundary 8 := by
  have hh := actual_four_rational_angle_checks_for_the_printed_boundary_roundings
  have hpiL : (3141592/1000000:ℝ) < Real.pi := by
    have h := Real.pi_gt_d6
    norm_num at h ⊢
    exact h
  have hpiU : Real.pi < (3141593/1000000:ℝ) := by
    have h := Real.pi_lt_d6
    norm_num at h ⊢
    exact h
  have hlow : ∀ b c : ℝ, 0 < b → b < 1/8 →
      c < Real.cos (4*(3141593/1000000)*b) → -1 ≤ c → c ≤ 1 →
      b < Real.arccos c/(4*Real.pi) := by
    intro b c hb hbq hcos hcL hcU
    have hangle : 0 ≤ 4*Real.pi*b := by positivity
    have hangleU : 4*(3141593/1000000)*b ≤ Real.pi := by nlinarith [hpiL]
    have hanglele : 4*Real.pi*b ≤ 4*(3141593/1000000)*b := by nlinarith
    have hactual : c < Real.cos (4*Real.pi*b) := hcos.trans_le
      (Real.cos_le_cos_of_nonneg_of_le_pi hangle hangleU hanglele)
    have hanti := Real.strictAntiOn_cos.lt_iff_gt
      (show Real.arccos c ∈ Icc 0 Real.pi from ⟨Real.arccos_nonneg _,Real.arccos_le_pi _⟩)
      (show 4*Real.pi*b ∈ Icc 0 Real.pi from ⟨hangle,by nlinarith⟩)
    have hnum : 4*Real.pi*b < Real.arccos c := by
      apply hanti.mp
      simpa [Real.cos_arccos hcL hcU] using hactual
    exact (lt_div_iff₀ (by positivity)).mpr (by nlinarith)
  have hupp : ∀ b c : ℝ, 0 < b → b < 1/8 →
      Real.cos (4*(3141592/1000000)*b) < c → -1 ≤ c → c ≤ 1 →
      Real.arccos c/(4*Real.pi) < b := by
    intro b c hb hbq hcos hcL hcU
    have hangle : 0 ≤ 4*(3141592/1000000)*b := by positivity
    have hangleU : 4*Real.pi*b ≤ Real.pi := by nlinarith [Real.pi_pos]
    have hanglele : 4*(3141592/1000000)*b ≤ 4*Real.pi*b := by nlinarith
    have hactual : Real.cos (4*Real.pi*b) < c :=
      (Real.cos_le_cos_of_nonneg_of_le_pi hangle hangleU hanglele).trans_lt hcos
    have hanti := Real.strictAntiOn_cos.lt_iff_gt
      (show 4*Real.pi*b ∈ Icc 0 Real.pi from ⟨by positivity,hangleU⟩)
      (show Real.arccos c ∈ Icc 0 Real.pi from ⟨Real.arccos_nonneg _,Real.arccos_le_pi _⟩)
    have hnum : Real.arccos c < 4*Real.pi*b := by
      apply hanti.mp
      simpa [Real.cos_arccos hcL hcU] using hactual
    exact (div_lt_iff₀ (by positivity)).mpr (by nlinarith)
  have hc₃ : actualThreshold 3=(5/12:ℝ) := by norm_num [actualThreshold]
  have hc₈ : actualThreshold 8=(5/16:ℝ) := by norm_num [actualThreshold]
  unfold actualBoundary
  rw [hc₃,hc₈]
  exact ⟨hlow _ _ (by norm_num) (by norm_num) hh.1 (by norm_num) (by norm_num),
    hupp _ _ (by norm_num) (by norm_num) hh.2.1 (by norm_num) (by norm_num),
    hlow _ _ (by norm_num) (by norm_num) hh.2.2.1 (by norm_num) (by norm_num),
    hupp _ _ (by norm_num) (by norm_num) hh.2.2.2.1 (by norm_num) (by norm_num),
    hupp _ _ (by norm_num) (by norm_num) hh.2.2.2.2.1 (by norm_num) (by norm_num),
    hlow _ _ (by norm_num) (by norm_num) hh.2.2.2.2.2 (by norm_num) (by norm_num)⟩

theorem actual_printed_four_decimal_boundaries_are_approximations_rather_than_equalities :
    actualBoundary 3 ≠ (908/10000:ℝ) ∧ actualBoundary 8 ≠ (997/10000:ℝ) := by
  have h := actual_boundary_three_and_eight_have_true_nearest_four_decimal_enclosures
  constructor
  · have hh := h.2.2.2.2.1
    norm_num at hh ⊢
    linarith
  · have hh := h.2.2.2.2.2
    exact ne_of_gt hh

end SafeLearning.CompleteModulesGoSafeToyBoundaryNumerics
