import SafeLearning.CompleteModulesTheory

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Set Filter Topology
namespace SafeLearning.CompleteModulesGoSafeToyAffine

def actualEuler (gain reference x : ℝ) : ℝ :=
  x+(1/400)*(-(1+gain)*x+gain*reference+3/5)
def actualRatio (gain : ℝ) : ℝ := 1-(1/400)*(1+gain)
def actualEquilibrium (gain reference : ℝ) : ℝ := (gain*reference+3/5)/(1+gain)
def actualTrajectory (ratio equilibrium initial : ℝ) (n : ℕ) : ℝ :=
  equilibrium+ratio^n*(initial-equilibrium)
def actualMargin (x : ℝ) : ℝ := 1-|x|
def actualTrajectoryInfimum (ratio equilibrium initial : ℝ) : ℝ :=
  sInf (Set.range (fun n : ℕ => actualMargin (actualTrajectory ratio equilibrium initial n)))
def actualGain (a : ℝ) : ℝ := 3+5*a
def actualReference (a : ℝ) : ℝ := (4/5)*(1+Real.cos (4*Real.pi*a))

theorem actual_source_parameter_ranges (a₁ a₂ : ℝ) (h₂ : a₂ ∈ Icc (0:ℝ) 1) :
    actualGain a₂ ∈ Icc (3:ℝ) 8 ∧ actualReference a₁ ∈ Icc (0:ℝ) (8/5) := by
  constructor
  · simp only [actualGain,mem_Icc] at *
    constructor <;> linarith [h₂.1,h₂.2]
  · simp only [actualReference,mem_Icc]
    constructor <;> linarith [Real.neg_one_le_cos (4*Real.pi*a₁),Real.cos_le_one (4*Real.pi*a₁)]

theorem actual_source_euler_ratio_and_positive_equilibrium
    (gain reference : ℝ) (hg : gain ∈ Icc (3:ℝ) 8) (hr : 0 ≤ reference) :
    actualRatio gain ∈ Icc (391/400:ℝ) (99/100) ∧
      0 < actualEquilibrium gain reference := by
  constructor
  · simp only [actualRatio,mem_Icc]
    constructor <;> linarith [hg.1,hg.2]
  · unfold actualEquilibrium
    apply div_pos
    · nlinarith [mul_nonneg (by linarith [hg.1] : 0 ≤ gain) hr]
    · linarith [hg.1]

theorem actual_euler_fixed_point_and_subtracted_error_identity
    (gain reference x : ℝ) (hg : -1 < gain) :
    actualEuler gain reference (actualEquilibrium gain reference)=actualEquilibrium gain reference ∧
      actualEuler gain reference x-actualEquilibrium gain reference=
        actualRatio gain*(x-actualEquilibrium gain reference) := by
  have hd : 1+gain≠0 := by linarith
  unfold actualEuler actualEquilibrium actualRatio
  constructor <;> field_simp <;> ring

theorem actual_closed_form_has_the_true_euler_recurrence
    (gain reference initial : ℝ) (hg : -1 < gain) :
    actualTrajectory (actualRatio gain) (actualEquilibrium gain reference) initial 0=initial ∧
      ∀ n : ℕ, actualTrajectory (actualRatio gain) (actualEquilibrium gain reference) initial (n+1)=
        actualEuler gain reference (actualTrajectory (actualRatio gain) (actualEquilibrium gain reference) initial n) := by
  constructor
  · simp [actualTrajectory]
  · intro n
    have h := (actual_euler_fixed_point_and_subtracted_error_identity gain reference
      (actualTrajectory (actualRatio gain) (actualEquilibrium gain reference) initial n) hg).2
    simp only [actualTrajectory,pow_succ] at h ⊢
    nlinarith

theorem actual_trajectory_converges_to_its_equilibrium
    (ratio equilibrium initial : ℝ) (hq : 0 ≤ ratio) (hq1 : ratio < 1) :
    Tendsto (actualTrajectory ratio equilibrium initial) atTop (𝓝 equilibrium) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1
  change Tendsto (fun n : ℕ => equilibrium+ratio^n*(initial-equilibrium)) atTop (𝓝 equilibrium)
  simpa only [zero_mul,add_zero] using tendsto_const_nhds.add (hp.mul_const (initial-equilibrium))

theorem actual_trajectory_absolute_values_are_bounded_by_the_start_equilibrium_maximum
    (ratio equilibrium initial : ℝ) (hq : 0 ≤ ratio) (hq1 : ratio ≤ 1)
    (he : 0 ≤ equilibrium) (n : ℕ) :
    |actualTrajectory ratio equilibrium initial n| ≤ max |initial| equilibrium := by
  have hp0 := pow_nonneg hq n
  have hp1 : ratio^n ≤ 1 := pow_le_one₀ hq hq1
  have hi := abs_le.mp (le_max_left |initial| equilibrium)
  have hem := le_max_right |initial| equilibrium
  have hm0 : 0 ≤ max |initial| equilibrium := (abs_nonneg initial).trans (le_max_left _ _)
  rw [abs_le]
  unfold actualTrajectory
  constructor <;> nlinarith [mul_nonneg hp0 (by linarith : 0 ≤ max |initial| equilibrium-initial),
    mul_nonneg (by linarith : 0 ≤ 1-ratio^n) (by linarith : 0 ≤ max |initial| equilibrium-equilibrium),
    mul_nonneg hp0 (by linarith : 0 ≤ max |initial| equilibrium+initial),
    mul_nonneg (by linarith : 0 ≤ 1-ratio^n) (by linarith : 0 ≤ max |initial| equilibrium+equilibrium)]

theorem actual_infinite_horizon_trajectory_infimum_is_the_literal_source_formula
    (ratio equilibrium initial : ℝ) (hq : 0 ≤ ratio) (hq1 : ratio < 1)
    (he : 0 ≤ equilibrium) :
    actualTrajectoryInfimum ratio equilibrium initial=1-max |initial| equilibrium := by
  let values := Set.range (fun n : ℕ => actualMargin (actualTrajectory ratio equilibrium initial n))
  have hlower : ∀ value ∈ values, 1-max |initial| equilibrium ≤ value := by
    rintro value ⟨n,rfl⟩
    have hb := actual_trajectory_absolute_values_are_bounded_by_the_start_equilibrium_maximum
      ratio equilibrium initial hq hq1.le he n
    unfold actualMargin
    linarith
  have hnon : values.Nonempty := Set.range_nonempty _
  have hbd : BddBelow values := ⟨1-max |initial| equilibrium,hlower⟩
  have hle : 1-max |initial| equilibrium ≤ sInf values := le_csInf hnon hlower
  change sInf values=1-max |initial| equilibrium
  apply le_antisymm _ hle
  by_cases hi : equilibrium ≤ |initial|
  · have h0 := csInf_le hbd (show actualMargin (actualTrajectory ratio equilibrium initial 0) ∈ values from ⟨0,rfl⟩)
    simpa [actualTrajectory,actualMargin,max_eq_left hi] using h0
  · have ht := actual_trajectory_converges_to_its_equilibrium ratio equilibrium initial hq hq1
    have hm : Tendsto (fun n : ℕ => actualMargin (actualTrajectory ratio equilibrium initial n))
        atTop (𝓝 (1-equilibrium)) := by
      simpa [actualMargin,abs_of_nonneg he] using tendsto_const_nhds.sub ht.abs
    have hu : sInf values ≤ 1-equilibrium := ge_of_tendsto' hm (fun n => csInf_le hbd ⟨n,rfl⟩)
    simpa [max_eq_right (le_of_not_ge hi)] using hu

theorem actual_start_zero_monotone_approach_is_strict_and_never_reaches_positive_equilibrium
    (ratio equilibrium : ℝ) (hq : 0 < ratio) (hq1 : ratio < 1) (he : 0 < equilibrium) :
    StrictMono (actualTrajectory ratio equilibrium 0) ∧
      ∀ n : ℕ, 0 ≤ actualTrajectory ratio equilibrium 0 n ∧
        actualTrajectory ratio equilibrium 0 n < equilibrium := by
  have hp : ∀ n : ℕ, 0 < ratio^n ∧ ratio^n ≤ 1 := fun n => ⟨pow_pos hq n,pow_le_one₀ hq.le hq1.le⟩
  constructor
  · apply strictMono_nat_of_lt_succ
    intro n
    unfold actualTrajectory
    rw [pow_succ]
    have hdec := mul_pos (mul_pos (hp n).1 (sub_pos.mpr hq1)) he
    nlinarith
  · intro n
    unfold actualTrajectory
    constructor <;> nlinarith [(hp n).1,(hp n).2]

theorem actual_initial_equal_to_equilibrium_is_a_fixed_trajectory_exception
    (ratio equilibrium : ℝ) : ∀ n : ℕ, actualTrajectory ratio equilibrium equilibrium n=equilibrium := by
  intro n
  simp [actualTrajectory]

end SafeLearning.CompleteModulesGoSafeToyAffine
