import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators Topology
namespace SafeLearning.CompleteAppliedTubeConstraints

def errorSet : Set ℝ := Icc (-(1/3)) (1/3)
def disturbanceSet : Set ℝ := Icc (-(1/5)) (1/5)
def actualErrorStep (error disturbance : ℝ) : ℝ := (2/5)*error+disturbance
def errorTrajectory (disturbance : ℕ→ℝ) (initial : ℝ) : ℕ→ℝ
  | 0 => initial
  | n+1 => actualErrorStep (errorTrajectory disturbance initial n) (disturbance n)
def pontryaginDifference (constraint error : Set ℝ) : Set ℝ :=
  {nominal | ∀deviation ∈ error,nominal+deviation∈constraint}

theorem actual_geometric_disturbance_sum_gives_the_source_error_radius :
    HasSum (fun n : ℕ=>(1/5:ℝ)*(2/5:ℝ)^n) (1/3:ℝ) ∧
      (∑'n : ℕ,(1/5:ℝ)*(2/5:ℝ)^n)=(1/3:ℝ) := by
  have h := (hasSum_geometric_of_norm_lt_one (by norm_num : ‖(2/5:ℝ)‖<1)).mul_left (1/5)
  have he : (1/5:ℝ)*(1-(2/5:ℝ))⁻¹=1/3 := by norm_num
  rw [he] at h
  exact ⟨h,h.tsum_eq⟩

theorem actual_every_error_step_keeps_the_source_error_set
    (error disturbance : ℝ) (he : error∈errorSet) (hw : disturbance∈disturbanceSet) :
    actualErrorStep error disturbance∈errorSet := by
  change -(1/3:ℝ)≤error ∧ error≤1/3 at he
  change -(1/5:ℝ)≤disturbance ∧ disturbance≤1/5 at hw
  change -(1/3:ℝ)≤(2/5)*error+disturbance ∧ (2/5)*error+disturbance≤1/3
  constructor <;> linarith [he.1,he.2,hw.1,hw.2]

theorem actual_every_disturbance_sequence_keeps_all_horizon_errors_in_the_tube
    (disturbance : ℕ→ℝ) (hw : ∀n,disturbance n∈disturbanceSet)
    (initial : ℝ) (hi : initial∈errorSet) (n : ℕ) :
    errorTrajectory disturbance initial n∈errorSet := by
  induction n with
  | zero => exact hi
  | succ n ih => exact actual_every_error_step_keeps_the_source_error_set _ _ ih (hw n)

theorem actual_every_symmetric_robust_invariant_radius_is_at_least_one_third
    (radius : ℝ) (hr : 0≤radius) :
    (∀error disturbance : ℝ,|error|≤radius → |disturbance|≤1/5 →
      |actualErrorStep error disturbance|≤radius) ↔ (1/3:ℝ)≤radius := by
  constructor
  · intro h
    have he := h radius (1/5) (by rw [abs_of_nonneg hr]) (by norm_num)
    have hp : 0≤actualErrorStep radius (1/5) := by dsimp [actualErrorStep];positivity
    rw [abs_of_nonneg hp] at he
    dsimp [actualErrorStep] at he
    linarith
  · intro hr3 error disturbance he hw
    have h := abs_add_le ((2/5)*error) disturbance
    norm_num [abs_mul,abs_div] at h
    change |(2/5)*error+disturbance|≤radius
    have hn : (2/5:ℝ)*|error|≤(2/5)*radius := mul_le_mul_of_nonneg_left he (by norm_num)
    linarith

theorem actual_source_radius_is_the_least_symmetric_robust_invariant_radius :
    IsLeast {radius : ℝ | 0≤radius ∧ ∀error disturbance : ℝ,
      |error|≤radius → |disturbance|≤1/5 → |actualErrorStep error disturbance|≤radius} (1/3:ℝ) := by
  constructor
  · exact ⟨by norm_num,(actual_every_symmetric_robust_invariant_radius_is_at_least_one_third
      (1/3) (by norm_num)).mpr (le_refl _)⟩
  · intro radius hr
    exact (actual_every_symmetric_robust_invariant_radius_is_at_least_one_third radius hr.1).mp hr.2

theorem actual_pontryagin_difference_of_symmetric_intervals (c r : ℝ)
    (hr : 0≤r) (hcr : r≤c) :
    pontryaginDifference (Icc (-c) c) (Icc (-r) r)=Icc (-(c-r)) (c-r) := by
  ext nominal
  constructor
  · intro h
    have hp := h r (show r∈Icc (-r) r from ⟨by linarith,le_refl _⟩)
    have hn := h (-r) (show -r∈Icc (-r) r from ⟨le_refl _,by linarith⟩)
    change -c≤nominal+r ∧ nominal+r≤c at hp
    change -c≤nominal-r ∧ nominal-r≤c at hn
    change -(c-r)≤nominal ∧ nominal≤c-r
    constructor <;> linarith
  · intro hn deviation hd
    change -(c-r)≤nominal ∧ nominal≤c-r at hn
    change -r≤deviation ∧ deviation≤r at hd
    change -c≤nominal+deviation ∧ nominal+deviation≤c
    constructor <;> linarith [hn.1,hn.2,hd.1,hd.2]

theorem actual_ancillary_gain_image_is_the_printed_input_error_interval :
    (fun error : ℝ=>(-3/5)*error) '' errorSet=Icc (-(1/5)) (1/5) := by
  ext deviation
  constructor
  · rintro ⟨error,he,rfl⟩
    change -(1/3:ℝ)≤error ∧ error≤1/3 at he
    change -(1/5:ℝ)≤(-3/5)*error ∧ (-3/5)*error≤1/5
    constructor <;> linarith [he.1,he.2]
  · intro hd
    refine ⟨(-5/3)*deviation,?_,?_⟩
    · change -(1/3:ℝ)≤(-5/3)*deviation ∧ (-5/3)*deviation≤1/3
      change -(1/5:ℝ)≤deviation ∧ deviation≤1/5 at hd
      constructor <;> linarith [hd.1,hd.2]
    · ring

theorem actual_source_tightened_state_and_input_constraints :
    pontryaginDifference (Icc (-2) (2:ℝ)) errorSet=Icc (-5/3) (5/3) ∧
    pontryaginDifference (Icc (-1) (1:ℝ)) ((fun error : ℝ=>(-3/5)*error) '' errorSet)=
      Icc (-4/5) (4/5) := by
  constructor
  · convert actual_pontryagin_difference_of_symmetric_intervals
      (2:ℝ) (1/3) (by norm_num) (by norm_num) using 1 <;> norm_num [errorSet]
  · rw [actual_ancillary_gain_image_is_the_printed_input_error_interval]
    convert actual_pontryagin_difference_of_symmetric_intervals (1:ℝ) (1/5)
      (by norm_num) (by norm_num) using 1 <;> norm_num

theorem actual_nominal_plus_error_has_the_true_disturbed_plant_recurrence
    (nominal nominalInput error disturbance : ℝ) :
    (nominal+nominalInput)+actualErrorStep error disturbance=
      (nominal+error)+(nominalInput-(3/5)*error)+disturbance ∧
    (1:ℝ)+1*(-3/5)=2/5 := by
  constructor
  · dsimp [actualErrorStep];ring
  · norm_num

theorem actual_every_tube_trajectory_satisfies_all_original_constraints
    (nominal nominalInput disturbance : ℕ→ℝ) (initial : ℝ)
    (hi : initial∈errorSet) (hw : ∀n,disturbance n∈disturbanceSet)
    (hz : ∀n,nominal n∈Icc (-5/3) (5/3:ℝ))
    (hv : ∀n,nominalInput n∈Icc (-4/5) (4/5:ℝ)) :
    ∀n,(nominal n+errorTrajectory disturbance initial n)∈Icc (-2) (2:ℝ) ∧
      (nominalInput n-(3/5)*errorTrajectory disturbance initial n)∈Icc (-1) (1:ℝ) := by
  intro n
  have he := actual_every_disturbance_sequence_keeps_all_horizon_errors_in_the_tube disturbance hw initial hi n
  change -(1/3:ℝ)≤errorTrajectory disturbance initial n ∧ errorTrajectory disturbance initial n≤1/3 at he
  have hzn := hz n;have hvn := hv n
  simp only [mem_Icc] at hzn
  simp only [mem_Icc] at hvn
  constructor
  · change (-2:ℝ)≤nominal n+errorTrajectory disturbance initial n ∧ nominal n+errorTrajectory disturbance initial n≤2
    constructor <;> linarith [he.1,he.2,hzn.1,hzn.2]
  · change (-1:ℝ)≤nominalInput n-(3/5)*errorTrajectory disturbance initial n ∧
      nominalInput n-(3/5)*errorTrajectory disturbance initial n≤1
    constructor <;> linarith [he.1,he.2,hvn.1,hvn.2]

end SafeLearning.CompleteAppliedTubeConstraints
