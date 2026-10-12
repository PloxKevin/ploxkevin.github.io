import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Set Filter
open scoped Topology
namespace SafeLearning.CompleteModulesDesignScalarLayers

def sourceResidual (T x : ℝ) : ℝ := x-(4/T)*max (2*x) 0
def admissibleGains (f : ℝ → ℝ) : Set ℝ := {L | 0≤L ∧ ∀ x y, |f x-f y|≤L*|x-y|}
def sourceInput : ℝ := 2*Real.sqrt 2/5
def sourceOutput : ℝ := 6*Real.sqrt 2/5
def sourceSandwich (x : ℝ) : ℝ := sourceOutput*max (sourceInput*x) 0
def sourceSchur (lambda : ℝ) : ℝ := 2*lambda-sourceOutput^2-lambda^2*sourceInput^2

theorem actual_source_residual_piecewise_and_absolute_forms (x : ℝ) :
    sourceResidual 4 x= -|x| ∧ sourceResidual 2 x= -x-2*|x| ∧
      (x≤0 → sourceResidual 4 x=x ∧ sourceResidual 2 x=x) ∧
      (0≤x → sourceResidual 4 x= -x ∧ sourceResidual 2 x= -3*x) := by
  by_cases hx : 0≤x
  · have hmax : max (2*x) 0=2*x := max_eq_left (by linarith)
    simp only [sourceResidual,hmax,abs_of_nonneg hx]
    norm_num
    constructor
    · ring
    constructor
    · ring
    constructor
    · intro hl;have hz : x=0 := le_antisymm hl hx;subst x;norm_num
    · intro _;constructor <;> ring
  · have hl : x≤0 := le_of_not_ge hx
    have hmax : max (2*x) 0=0 := max_eq_right (by linarith)
    simp [sourceResidual,hmax,abs_of_nonpos hl]
    constructor
    · ring
    intro hh;have hz : x=0 := le_antisymm hl hh;subst x;norm_num

theorem actual_source_residual_exact_least_lipschitz_gains :
    IsLeast (admissibleGains (sourceResidual 4)) 1 ∧
      IsLeast (admissibleGains (sourceResidual 2)) 3 := by
  have h4 : ∀ x y, |sourceResidual 4 x-sourceResidual 4 y|≤1*|x-y| := by
    intro x y
    rw [(actual_source_residual_piecewise_and_absolute_forms x).1,
      (actual_source_residual_piecewise_and_absolute_forms y).1]
    simpa only [neg_sub_neg,abs_sub_comm,one_mul] using abs_abs_sub_abs_le_abs_sub x y
  have h2 : ∀ x y, |sourceResidual 2 x-sourceResidual 2 y|≤3*|x-y| := by
    intro x y
    rw [(actual_source_residual_piecewise_and_absolute_forms x).2.1,
      (actual_source_residual_piecewise_and_absolute_forms y).2.1]
    calc
      _ = |-(x-y)-2*(|x|-|y|)| := by congr 1;ring
      _ ≤ |-(x-y)|+|2*(|x|-|y|)| := abs_sub _ _
      _ = |x-y|+2*abs (abs x-abs y) := by rw [abs_neg,abs_mul];norm_num
      _ ≤ |x-y|+2*|x-y| := by linarith [abs_abs_sub_abs_le_abs_sub x y]
      _ = _ := by ring
  constructor
  · refine ⟨⟨by norm_num,h4⟩,?_⟩
    intro L hL
    have h:=hL.2 1 0
    norm_num [sourceResidual] at h
    exact h
  · refine ⟨⟨by norm_num,h2⟩,?_⟩
    intro L hL
    have h:=hL.2 1 0
    norm_num [sourceResidual] at h
    exact h

theorem actual_source_residual_derivatives_on_the_two_open_halves
    (x : ℝ) :
    (x<0 → HasDerivAt (sourceResidual 4) 1 x ∧ HasDerivAt (sourceResidual 2) 1 x) ∧
      (0<x → HasDerivAt (sourceResidual 4) (-1) x ∧ HasDerivAt (sourceResidual 2) (-3) x) := by
  constructor
  · intro hx
    have hl : ∀ᶠ y in 𝓝 x, y≤0 := (eventually_lt_nhds hx).mono (fun _ h=>h.le)
    constructor
    · exact (hasDerivAt_id x).congr_of_eventuallyEq (hl.mono (fun y hy=>(actual_source_residual_piecewise_and_absolute_forms y).2.2.1 hy |>.1))
    · exact (hasDerivAt_id x).congr_of_eventuallyEq (hl.mono (fun y hy=>(actual_source_residual_piecewise_and_absolute_forms y).2.2.1 hy |>.2))
  · intro hx
    have hl : ∀ᶠ y in 𝓝 x, 0≤y := (eventually_gt_nhds hx).mono (fun _ h=>h.le)
    constructor
    · exact (hasDerivAt_id x).neg.congr_of_eventuallyEq (hl.mono (fun y hy=>(actual_source_residual_piecewise_and_absolute_forms y).2.2.2 hy |>.1))
    · simpa using ((hasDerivAt_id x).const_mul (-3)).congr_of_eventuallyEq
        (hl.mono (fun y hy=>(actual_source_residual_piecewise_and_absolute_forms y).2.2.2 hy |>.2))

theorem actual_source_residual_certificate_boundary_and_positive_failure :
    (2:ℝ)^2=4 ∧ (0:ℝ)<4 ∧ (4:ℝ)≥2^2 ∧ (0:ℝ)<2 ∧ ¬(2:ℝ)≥2^2 := by norm_num

theorem actual_source_sandwich_coefficients_squares_and_layer (x : ℝ) :
    Real.sqrt 2*(1/(2:ℝ))*(4/5)=sourceInput ∧
      Real.sqrt 2*(3/5:ℝ)*2=sourceOutput ∧
      (3/5:ℝ)^2+(4/5)^2=1 ∧
      sourceInput^2=8/25 ∧ sourceOutput^2=72/25 ∧
      sourceSandwich x=(24/25:ℝ)*max x 0 := by
  have hs:=Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  have hp : 0 ≤ sourceInput := by unfold sourceInput;positivity
  have hm : max (sourceInput*x) 0=sourceInput*max x 0 := by
    simpa only [mul_zero] using (mul_max_of_nonneg x (0:ℝ) hp).symm
  unfold sourceInput sourceOutput at *
  refine ⟨by ring,by ring,by norm_num,by nlinarith,by nlinarith,?_⟩
  unfold sourceSandwich sourceInput sourceOutput
  rw [hm]
  calc
    _ = (12/25:ℝ)*(Real.sqrt 2)^2*max x 0 := by ring
    _ = _ := by rw [hs];ring

theorem actual_source_sandwich_exact_least_gain_and_two_multipliers :
    IsLeast (admissibleGains sourceSandwich) (24/25) ∧
      sourceSchur 4=0 ∧ sourceSchur 2= -4/25 ∧ sourceSchur 2<0 := by
  have hs:=actual_source_sandwich_coefficients_squares_and_layer (0:ℝ)
  refine ⟨?_,?_,?_,?_⟩
  · refine ⟨⟨by norm_num,?_⟩,?_⟩
    · intro x y
      rw [(actual_source_sandwich_coefficients_squares_and_layer x).2.2.2.2.2,
        (actual_source_sandwich_coefficients_squares_and_layer y).2.2.2.2.2,←mul_sub,abs_mul]
      norm_num
      linarith [abs_max_sub_max_le_abs x y (0:ℝ)]
    · intro L hL
      have h:=hL.2 1 0
      rw [(actual_source_sandwich_coefficients_squares_and_layer 1).2.2.2.2.2,
        (actual_source_sandwich_coefficients_squares_and_layer 0).2.2.2.2.2] at h
      norm_num at h
      exact h
  all_goals unfold sourceSchur;rw [hs.2.2.2.1,hs.2.2.2.2.1];norm_num

end SafeLearning.CompleteModulesDesignScalarLayers
