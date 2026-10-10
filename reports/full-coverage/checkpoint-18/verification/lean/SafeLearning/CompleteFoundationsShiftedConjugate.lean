import SafeLearning.CompleteFoundationsOptimization
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SafeLearning.CompleteFoundationsShiftedConjugate
open Set

def sourceFunction (w : ℝ) : EReal := if 0 ≤ w then (((w-1)^2/2 : ℝ):EReal) else ⊤
def objective (e w : ℝ) : ℝ := w*e-(w-1)^2/2
def extendedObjective (e w : ℝ) : EReal := ((w*e:ℝ):EReal)-sourceFunction w
def sourceConjugate (e : ℝ) : EReal := sSup (range (extendedObjective e))
def value (e : ℝ) : ℝ := if -1 ≤ e then e+e^2/2 else -1/2

theorem actual_restricted_domain_and_objective (e w : ℝ) :
    (sourceFunction w=⊤ ↔ w<0) ∧
    extendedObjective e w=if 0 ≤ w then (objective e w:EReal) else ⊥ := by
  constructor
  · unfold sourceFunction
    by_cases hw : 0 ≤ w
    · simp [hw,not_lt.mpr hw]
    · simp [hw,lt_of_not_ge hw]
  · unfold extendedObjective sourceFunction objective
    split_ifs
    · rw [←EReal.coe_sub]
    · exact EReal.sub_top _

theorem actual_completed_square_and_unrestricted_derivative (e w : ℝ) :
    objective e w=e+e^2/2-(w-(1+e))^2/2 ∧
    HasDerivAt (objective e) (e-(w-1)) w := by
  constructor
  · unfold objective;ring
  · convert ((hasDerivAt_id w).mul_const e).sub
      (((hasDerivAt_id w).sub_const 1).pow 2 |>.div_const 2) using 1
    · funext z;unfold objective;simp
    · simp

theorem actual_unrestricted_unique_global_maximum (e w : ℝ) :
    objective e w ≤ e+e^2/2 ∧ (objective e w=e+e^2/2 ↔ w=1+e) := by
  rw [(actual_completed_square_and_unrestricted_derivative e w).1]
  constructor
  · nlinarith [sq_nonneg (w-(1+e))]
  · constructor
    · intro h;nlinarith [sq_nonneg (w-(1+e))]
    · intro h;rw [h];ring

theorem actual_admissible_objective_upper (e w : ℝ) (hw : 0 ≤ w) :
    objective e w ≤ value e := by
  have h:=SafeLearning.CompleteFoundationsOptimization.translated_square_conjugate_supremum e
  exact h.1 ⟨w,hw,rfl⟩

theorem actual_maximizing_argument (e : ℝ) :
    0 ≤ max (1+e) 0 ∧ objective e (max (1+e) 0)=value e := by
  refine ⟨le_max_right _ _,?_⟩
  by_cases he : -1 ≤ e
  · rw [max_eq_left (by linarith),value,if_pos he]
    unfold objective;ring
  · rw [max_eq_right (by linarith),value,if_neg he]
    norm_num [objective]

theorem actual_extended_real_conjugate (e : ℝ) : sourceConjugate e=(value e:EReal) := by
  apply le_antisymm
  · apply sSup_le
    rintro z ⟨w,rfl⟩
    rw [(actual_restricted_domain_and_objective e w).2]
    split_ifs with hw
    · exact EReal.coe_le_coe (actual_admissible_objective_upper e w hw)
    · exact bot_le
  · have he : extendedObjective e (max (1+e) 0)=(value e:EReal) := by
      rw [(actual_restricted_domain_and_objective e (max (1+e) 0)).2,
        if_pos (actual_maximizing_argument e).1,(actual_maximizing_argument e).2]
    exact le_sSup ⟨max (1+e) 0,he⟩

theorem actual_negative_case_strictly_decreasing_on_domain (e : ℝ) (he : e < -1) :
    StrictAntiOn (objective e) (Ici 0) := by
  intro w hw z hz hwz
  change 0 ≤ w at hw
  change 0 ≤ z at hz
  have hm:=mul_neg_of_pos_of_neg (sub_pos.mpr hwz)
    (show e+1-(z+w)/2<0 by linarith [hw,hz])
  unfold objective
  nlinarith [hm]

theorem actual_fenchel_young (w e : ℝ) :
    ((w*e:ℝ):EReal) ≤ sourceFunction w+sourceConjugate e := by
  rw [actual_extended_real_conjugate]
  by_cases hw : 0 ≤ w
  · rw [sourceFunction,if_pos hw,←EReal.coe_add,EReal.coe_le_coe_iff]
    have h:=actual_admissible_objective_upper e w hw
    unfold objective at h
    linarith
  · rw [sourceFunction,if_neg hw,EReal.top_add_coe]
    exact le_top

theorem actual_two_source_fenchel_checks :
    sourceFunction 2=((1/2:ℝ):EReal) ∧ sourceConjugate (1/2)=((5/8:ℝ):EReal) ∧
    sourceFunction 2+sourceConjugate (1/2)=((9/8:ℝ):EReal) ∧
    ((2*(1/2):ℝ):EReal) ≤ sourceFunction 2+sourceConjugate (1/2) ∧
    sourceConjugate 1=((3/2:ℝ):EReal) ∧
    sourceFunction 2+sourceConjugate 1=((2*1:ℝ):EReal) := by
  norm_num [sourceFunction,actual_extended_real_conjugate,value,←EReal.coe_add]
  change ((1:ℝ):EReal) ≤ ((9/8:ℝ):EReal)
  exact EReal.coe_le_coe (by norm_num)

theorem actual_source_w_two_equality_iff_ordinary_slope (e : ℝ) :
    sourceFunction 2+sourceConjugate e=((2*e:ℝ):EReal) ↔ e=1 := by
  rw [show sourceFunction 2=((1/2:ℝ):EReal) by norm_num [sourceFunction],
    actual_extended_real_conjugate,←EReal.coe_add,EReal.coe_eq_coe_iff]
  unfold value
  split_ifs with he
  · constructor
    · intro h;nlinarith [sq_nonneg (e-1)]
    · intro h;rw [h];ring
  · constructor
    · intro h;exfalso;linarith
    · intro h;exfalso;linarith
end SafeLearning.CompleteFoundationsShiftedConjugate
