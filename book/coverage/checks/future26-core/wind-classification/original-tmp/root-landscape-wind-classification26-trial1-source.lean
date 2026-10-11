import Mathlib

set_option autoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteModulesLandscapeWindClassification26

/-- An admissible gust obeys the source's pointwise norm-two bound as well as any
model-specific admissibility requirements. Time and wind dimensions are arbitrary. -/
def sourceAdmissibleGusts {Time Wind : Type*} [NormedAddCommGroup Wind]
    (allowed : Set (Time → Wind)) : Set (Time → Wind) :=
  {gust | gust ∈ allowed ∧ ∀ t, ‖gust t‖ ≤ (2 : ℝ)}

/-- The controller is fixed before the gust is quantified. The run family can
represent continuous trajectories, discrete trajectories or history-based policies. -/
def sourceRobustSafety {Time Wind State Controller : Type*} [NormedAddCommGroup Wind]
    (run : State → Controller → (Time → Wind) → Time → State)
    (controller : Controller) (safe : Set State) (allowed : Set (Time → Wind)) : Prop :=
  ∀ initial ∈ safe, ∀ gust ∈ sourceAdmissibleGusts allowed,
    ∀ t, run initial controller gust t ∈ safe

/-- Forward invariance for each allowed gust is a hard all-time constraint,
with the same controller and every covered initial state throughout. -/
theorem actual_source_wind_guarantee_is_same_controller_robust_forward_invariance
    {Time Wind State Controller : Type*} [NormedAddCommGroup Wind]
    (run : State → Controller → (Time → Wind) → Time → State)
    (controller : Controller) (safe : Set State) (allowed : Set (Time → Wind)) :
    sourceRobustSafety run controller safe allowed ↔
      ∀ gust, gust ∈ allowed → (∀ t, ‖gust t‖ ≤ (2 : ℝ)) →
        ∀ initial ∈ safe, ∀ t, run initial controller gust t ∈ safe := by
  constructor
  · intro h gust ha hb initial hi t
    exact h initial hi gust ⟨ha, hb⟩ t
  · intro h initial hi gust hg t
    exact h gust hg.1 hg.2 initial hi t

/-- A deterministic robust certificate directly protects each admissible run.
No probability distribution, average or new controller choice is needed. -/
theorem actual_robust_certificate_protects_each_admissible_initial_gust_and_time
    {Time Wind State Controller : Type*} [NormedAddCommGroup Wind]
    (run : State → Controller → (Time → Wind) → Time → State)
    (controller : Controller) (safe : Set State) (allowed : Set (Time → Wind))
    (certificate : sourceRobustSafety run controller safe allowed)
    (initial : State) (hi : initial ∈ safe) (gust : Time → Wind)
    (ha : gust ∈ allowed) (hb : ∀ t, ‖gust t‖ ≤ (2 : ℝ)) (t : Time) :
    run initial controller gust t ∈ safe :=
  certificate initial hi gust ⟨ha, hb⟩ t

/-- Allowing a different controller after seeing each gust is a weaker condition. -/
theorem actual_fixed_controller_robust_safety_implies_gustwise_controller_existence
    {Time Wind State Controller : Type*} [NormedAddCommGroup Wind]
    (run : State → Controller → (Time → Wind) → Time → State)
    (safe : Set State) (allowed : Set (Time → Wind))
    (h : ∃ controller, sourceRobustSafety run controller safe allowed) :
    ∀ gust ∈ sourceAdmissibleGusts allowed,
      ∃ controller, ∀ initial ∈ safe, ∀ t, run initial controller gust t ∈ safe := by
  obtain ⟨controller, hc⟩ := h
  intro gust hg
  exact ⟨controller, fun initial hi t => hc initial hi gust hg t⟩

/-- The quantifier order matters even for constant one-time gusts: a controller
chosen after observing the gust can cancel it, but a single scalar input cannot
cancel both allowed gusts +2 and -2. This is a mathematical counterexample,
not a model of the source quadrotor. -/
theorem actual_gustwise_recovery_does_not_supply_one_robust_controller :
    (∀ gust : ℝ, |gust| ≤ 2 → ∃ controller : ℝ, controller + gust = 0) ∧
      ¬∃ controller : ℝ, ∀ gust : ℝ, |gust| ≤ 2 → controller + gust = 0 := by
  constructor
  · intro gust _
    exact ⟨-gust, by ring⟩
  · rintro ⟨controller, hc⟩
    have hp := hc 2 (by norm_num)
    have hm := hc (-2) (by norm_num)
    linarith

end SafeLearning.CompleteModulesLandscapeWindClassification26
