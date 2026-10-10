import SafeLearning.CompleteModulesGoSafeToyAffine

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Set
namespace SafeLearning.CompleteModulesGoSafeToyBounds
open SafeLearning.CompleteModulesGoSafeToyAffine

def actualClosedFormConstraint (equilibrium initial : ℝ) : ℝ := 1-max |initial| equilibrium

theorem actual_closed_form_constraint_is_lipschitz_with_constant_one (equilibrium x y : ℝ) :
    |actualClosedFormConstraint equilibrium x-actualClosedFormConstraint equilibrium y| ≤ |x-y| := by
  have h1 := abs_max_sub_max_le_abs |x| |y| equilibrium
  have h2 := abs_abs_sub_abs_le_abs_sub x y
  have heq : actualClosedFormConstraint equilibrium x-actualClosedFormConstraint equilibrium y=
      -(max |x| equilibrium-max |y| equilibrium) := by unfold actualClosedFormConstraint;ring
  rw [heq,abs_neg]
  exact h1.trans h2

theorem actual_constant_one_is_the_least_lipschitz_constant_of_the_source_constraint
    (equilibrium : ℝ) (he : 0 ≤ equilibrium) :
    IsLeast {constant : ℝ | ∀ x y : ℝ,
      |actualClosedFormConstraint equilibrium x-actualClosedFormConstraint equilibrium y| ≤ constant*|x-y|} 1 := by
  constructor
  · intro x y
    simpa using actual_closed_form_constraint_is_lipschitz_with_constant_one equilibrium x y
  · intro constant hc
    have h := hc (equilibrium+1) (equilibrium+2)
    have hx : |equilibrium+1|=equilibrium+1 := abs_of_nonneg (by linarith)
    have hy : |equilibrium+2|=equilibrium+2 := abs_of_nonneg (by linarith)
    simp only [actualClosedFormConstraint,hx,hy,max_eq_left (by linarith : equilibrium ≤ equilibrium+1),
      max_eq_left (by linarith : equilibrium ≤ equilibrium+2)] at h
    have hleft : (1-(equilibrium+1))-(1-(equilibrium+2))=1 := by ring
    have hright : (equilibrium+1)-(equilibrium+2)=(-1:ℝ) := by ring
    rw [hleft,hright] at h
    norm_num at h ⊢
    exact h

theorem actual_source_euler_and_every_iterate_are_nonexpansive
    (gain reference x y : ℝ) (hg : gain ∈ Icc (3:ℝ) 8) (n : ℕ) :
    |actualEuler gain reference x-actualEuler gain reference y| ≤ |x-y| ∧
      |actualTrajectory (actualRatio gain) (actualEquilibrium gain reference) x n-
        actualTrajectory (actualRatio gain) (actualEquilibrium gain reference) y n| ≤ |x-y| := by
  have hq : 0 ≤ actualRatio gain ∧ actualRatio gain ≤ 1 := by
    unfold actualRatio
    constructor <;> linarith [hg.1,hg.2]
  have hqe : actualEuler gain reference x-actualEuler gain reference y=actualRatio gain*(x-y) := by
    unfold actualEuler actualRatio
    ring
  have hte : actualTrajectory (actualRatio gain) (actualEquilibrium gain reference) x n-
      actualTrajectory (actualRatio gain) (actualEquilibrium gain reference) y n=(actualRatio gain)^n*(x-y) := by
    unfold actualTrajectory
    ring
  have hp0 := pow_nonneg hq.1 n
  have hp1 := pow_le_one₀ hq.1 hq.2 (n:=n)
  constructor
  · rw [hqe,abs_mul,abs_of_nonneg hq.1]
    nlinarith [abs_nonneg (x-y)]
  · rw [hte,abs_mul,abs_of_nonneg hp0]
    nlinarith [abs_nonneg (x-y)]

theorem actual_all_source_parameter_and_state_step_motions_are_at_most_point_zero_six_zero_five
    (gain reference x : ℝ) (hg : gain ∈ Icc (3:ℝ) 8)
    (hr : reference ∈ Icc (0:ℝ) (8/5)) (hx : |x| ≤ (6/5:ℝ)) :
    |actualEuler gain reference x-x| ≤ (121/2000:ℝ) := by
  have hg0 : 0 ≤ gain := by linarith [hg.1]
  have hg1 : 0 ≤ 1+gain := by linarith [hg.1]
  have hforce : 0 ≤ gain*reference+3/5 := by nlinarith [mul_nonneg hg0 hr.1]
  have hforceUpper : gain*reference ≤ (64/5:ℝ) := by
    have h := mul_le_mul hg.2 hr.2 hr.1 (by norm_num : (0:ℝ) ≤ 8)
    norm_num at h
    exact h
  have hfirst : (1+gain)*|x| ≤ (54/5:ℝ) := by
    have h := mul_le_mul (by linarith [hg.2] : 1+gain ≤ 9) hx (abs_nonneg x) (by norm_num : (0:ℝ) ≤ 9)
    norm_num at h
    exact h
  have hb : |-(1+gain)*x+gain*reference+3/5| ≤ (121/5:ℝ) := by
    have h := abs_add_le (-(1+gain)*x) (gain*reference+3/5)
    have he : |-(1+gain)*x+gain*reference+3/5|=|-(1+gain)*x+(gain*reference+3/5)| := by congr 1;ring
    rw [abs_mul,abs_neg,abs_of_nonneg hg1,abs_of_nonneg hforce] at h
    rw [he]
    linarith
  have heq : actualEuler gain reference x-x=(1/400)*(-(1+gain)*x+gain*reference+3/5) := by
    unfold actualEuler
    ring
  rw [heq,abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 1/400)]
  calc
    (1/400)*|-(1+gain)*x+gain*reference+3/5| ≤ (1/400)*(121/5) :=
      mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = 121/2000 := by norm_num

def actualGridStepMotions : Set ℝ := {value | ∃ first second : Fin 25, ∃ x : ℝ,
  |x| ≤ (6/5:ℝ) ∧ value=|actualEuler (actualGain ((second.val:ℝ)/24))
    (actualReference ((first.val:ℝ)/24)) x-x|}

theorem actual_source_grid_has_the_largest_step_motion_point_zero_six_zero_five :
    IsGreatest actualGridStepMotions (121/2000:ℝ) := by
  constructor
  · refine ⟨0,24,-6/5,by norm_num,?_⟩
    norm_num [actualEuler,actualGain,actualReference]
  · rintro value ⟨first,second,x,hx,rfl⟩
    have hs : (second.val:ℝ)/24 ∈ Icc (0:ℝ) 1 := by
      constructor
      · positivity
      · have h : second.val ≤ 24 := by omega
        have hr : (second.val:ℝ) ≤ 24 := by exact_mod_cast h
        linarith
    have ranges := actual_source_parameter_ranges ((first.val:ℝ)/24) ((second.val:ℝ)/24) hs
    exact actual_all_source_parameter_and_state_step_motions_are_at_most_point_zero_six_zero_five _ _ _ ranges.1 ranges.2 hx

theorem actual_source_grid_size_and_simulated_prefix_duration :
    Fintype.card (Fin 25 × Fin 25)=625 ∧ (1200:ℝ)*(1/400)=3 := by norm_num

end SafeLearning.CompleteModulesGoSafeToyBounds
