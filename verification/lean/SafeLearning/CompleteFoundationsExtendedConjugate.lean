import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SafeLearning.CompleteFoundationsExtendedConjugate
open Set

def sourceFunction (x : ℝ) : EReal := if 0≤x then ((x^2/2 : ℝ) : EReal) else ⊤
def pairingMinusFunction (y x : ℝ) : EReal := ((y*x : ℝ) : EReal)-sourceFunction x
def sourceConjugate (y : ℝ) : EReal := sSup (range (pairingMinusFunction y))
def conjugateValue (y : ℝ) : ℝ := (max y 0)^2/2

theorem actual_extended_domain_and_objective (y x : ℝ) :
    (sourceFunction x=⊤↔x<0) ∧
    pairingMinusFunction y x=if 0≤x then ((y*x-x^2/2:ℝ):EReal) else ⊥ := by
  constructor
  · unfold sourceFunction
    by_cases hx : 0≤x
    · simp [hx,not_lt.mpr hx]
    · simp [hx,lt_of_not_ge hx]
  · unfold pairingMinusFunction sourceFunction
    split_ifs
    · rw [←EReal.coe_sub]
    · exact EReal.sub_top _

theorem actual_completed_square (y x : ℝ) :
    y*x-x^2/2=y^2/2-(x-y)^2/2 := by ring

theorem actual_every_admissible_objective_upper (y x : ℝ) (hx : 0≤x) :
    y*x-x^2/2≤conjugateValue y := by
  by_cases hy : 0≤y
  · rw [conjugateValue,max_eq_left hy]
    nlinarith [sq_nonneg (x-y)]
  · rw [conjugateValue,max_eq_right (le_of_not_ge hy)]
    have hp : y*x≤0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hy) hx
    nlinarith [sq_nonneg x]

theorem actual_maximizing_argument (y : ℝ) :
    0≤ max y 0 ∧ y*(max y 0)-(max y 0)^2/2=conjugateValue y := by
  refine ⟨le_max_right _ _,?_⟩
  by_cases hy : 0≤y
  · rw [max_eq_left hy,conjugateValue,max_eq_left hy];ring
  · rw [max_eq_right (le_of_not_ge hy),conjugateValue,max_eq_right (le_of_not_ge hy)];ring

theorem actual_extended_real_conjugate (y : ℝ) :
    sourceConjugate y=(conjugateValue y : EReal) := by
  apply le_antisymm
  · apply sSup_le
    rintro z ⟨x,rfl⟩
    rw [(actual_extended_domain_and_objective y x).2]
    split_ifs with hx
    · exact EReal.coe_le_coe (actual_every_admissible_objective_upper y x hx)
    · exact bot_le
  · have he : pairingMinusFunction y (max y 0)=(conjugateValue y : EReal) := by
      rw [(actual_extended_domain_and_objective y (max y 0)).2,
        if_pos (actual_maximizing_argument y).1,(actual_maximizing_argument y).2]
    exact le_sSup ⟨max y 0,he⟩

theorem actual_piecewise_conjugate_and_attainer (y : ℝ) :
    sourceConjugate y=((if 0≤y then y^2/2 else 0 : ℝ):EReal) ∧
    pairingMinusFunction y (if 0≤y then y else 0)=sourceConjugate y := by
  rw [actual_extended_real_conjugate]
  by_cases hy : 0≤y
  · simp only [if_pos hy,conjugateValue,max_eq_left hy]
    constructor
    · trivial
    · rw [(actual_extended_domain_and_objective y y).2,if_pos hy]
      congr 1
      ring
  · simp only [if_neg hy,conjugateValue,max_eq_right (le_of_not_ge hy)]
    norm_num [pairingMinusFunction,sourceFunction]

theorem actual_fenchel_young (x y : ℝ) :
    ((x*y:ℝ):EReal)≤ sourceFunction x+sourceConjugate y := by
  rw [actual_extended_real_conjugate]
  by_cases hx : 0≤x
  · rw [sourceFunction,if_pos hx,←EReal.coe_add,EReal.coe_le_coe_iff]
    have h := actual_every_admissible_objective_upper y x hx
    nlinarith
  · rw [sourceFunction,if_neg hx,EReal.top_add_coe]
    exact le_top

theorem actual_two_fenchel_young_equalities :
    sourceFunction 2=(2:ℝ) ∧ sourceConjugate 2=(2:ℝ) ∧
    sourceFunction 2+sourceConjugate 2=((2*2:ℝ):EReal) ∧
    sourceFunction 0=0 ∧ sourceConjugate (-1)=0 ∧
    sourceFunction 0+sourceConjugate (-1)=((0*(-1):ℝ):EReal) := by
  norm_num [sourceFunction,actual_extended_real_conjugate,conjugateValue,←EReal.coe_add]

theorem actual_negative_slopes_support_boundary (y : ℝ) (hy : y≤0) :
    ∀ x : ℝ,sourceFunction 0+((y*(x-0):ℝ):EReal)≤ sourceFunction x := by
  intro x
  have hc : sourceConjugate y=0 := by
    rw [actual_extended_real_conjugate,conjugateValue,max_eq_right hy]
    norm_num
  have hf := actual_fenchel_young x y
  rw [hc,add_zero] at hf
  simpa [sourceFunction,mul_comm] using hf

theorem actual_unrestricted_negative_formula_fails_boundary_equality :
    (conjugateValue (-1):ℝ)=0 ∧ ((-1:ℝ)^2/2)=1/2 ∧
    sourceFunction 0+((((-1:ℝ)^2/2):ℝ):EReal)≠((0*(-1):ℝ):EReal) := by
  refine ⟨by norm_num [conjugateValue],by norm_num,?_⟩
  rw [show sourceFunction 0=0 by norm_num [sourceFunction],zero_add,
    show ((-1:ℝ)^2/2)=1/2 by norm_num,show (0*(-1:ℝ))=0 by ring]
  intro h
  have hn := EReal.coe_injective h
  norm_num at hn
end SafeLearning.CompleteFoundationsExtendedConjugate
