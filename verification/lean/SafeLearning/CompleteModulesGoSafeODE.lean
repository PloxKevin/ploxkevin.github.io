import SafeLearning.CompleteModulesGoSafeBackupConsequences

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped NNReal
namespace SafeLearning.CompleteModulesGoSafeODE
open CompleteModulesGoSafeBackupConsequences

/-- Autonomous ODE uniqueness, rather than an assumed restart law, identifies
the restarted solution with the original suffix on every future interval. -/
theorem actual_autonomous_lipschitz_ode_restart_is_the_original_future_solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (field : E→E) (L : ℝ≥0) (hL : LipschitzWith L field)
    (original restarted : ℝ→E) (time : ℝ) (htime : 0 ≤ time)
    (horiginal : ∀ t,0 ≤ t→HasDerivAt original (field (original t)) t)
    (hrestarted : ∀ t,0 ≤ t→HasDerivAt restarted (field (restarted t)) t)
    (hstart : restarted 0=original time) :
    ∀ t,0 ≤ t → restarted t=original (time+t) := by
  intro t ht
  let tail : ℝ→E := fun s=>original (time+s)
  have htail : ∀ s,0 ≤ s→HasDerivAt tail (field (tail s)) s := by
    intro s hs
    exact (horiginal (time+s) (add_nonneg htime hs)).comp_const_add time s
  have hc1 : ContinuousOn restarted (Icc 0 t) :=
    fun s hs=>(hrestarted s hs.1).continuousAt.continuousWithinAt
  have hc2 : ContinuousOn tail (Icc 0 t) :=
    fun s hs=>(htail s hs.1).continuousAt.continuousWithinAt
  have heq : restarted 0=tail 0 := by simpa only [tail,add_zero] using hstart
  have h := ODE_solution_unique (v:=fun _s=>field) (K:=L) (a:=0) (b:=t)
    (fun _s=>hL) hc1
    (fun s hs=>(hrestarted s hs.1).hasDerivWithinAt) hc2
    (fun s hs=>(htail s hs.1).hasDerivWithinAt) heq
  exact h ⟨ht,le_rfl⟩

def actualAutonomousODEClosedLoop
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (field : E→E) (L : ℝ≥0) (hL : LipschitzWith L field)
    (path : ℝ→E→E) (hstart : ∀ x,path 0 x=x)
    (hderiv : ∀ x t,0 ≤ t→HasDerivAt (fun s=>path s x) (field (path t x)) t) :
    ClosedLoop E where
  path := path
  start := hstart
  restart := by
    intro time s x htime hs
    exact actual_autonomous_lipschitz_ode_restart_is_the_original_future_solution
      field L hL (fun t=>path t x) (fun t=>path t (path time x)) time htime
      (hderiv x) (hderiv (path time x)) (hstart (path time x)) s hs

theorem actual_existing_source_trajectory_minima_are_nondecreasing_after_restart
    {X : Type*} (F : ClosedLoop X) (margin : X→ℝ) (initial : X)
    (time wholeMinimum suffixMinimum : ℝ) (htime : 0 ≤ time)
    (hwhole : IsLeast (trajectoryMargins F margin initial) wholeMinimum)
    (hsuffix : IsLeast (trajectoryMargins F margin (F.path time initial)) suffixMinimum) :
    wholeMinimum ≤ suffixMinimum :=
  hwhole.2
    (actual_restarted_trajectory_is_a_suffix_of_the_same_complete_closed_loop
      F margin initial time htime hsuffix.1)

theorem actual_minimum_over_a_union_is_the_smaller_of_the_two_actual_minima
    (firstPart tail : Set ℝ) (prefixMinimum tailMinimum : ℝ)
    (hp : IsLeast firstPart prefixMinimum) (ht : IsLeast tail tailMinimum) :
    IsLeast (firstPart∪tail) (min prefixMinimum tailMinimum) := by
  constructor
  · by_cases h : prefixMinimum ≤ tailMinimum
    · rw [min_eq_left h];exact Or.inl hp.1
    · rw [min_eq_right (le_of_not_ge h)];exact Or.inr ht.1
  · intro value hv
    rcases hv with hv|hv
    · exact (min_le_left _ _).trans (hp.2 hv)
    · exact (min_le_right _ _).trans (ht.2 hv)

theorem actual_two_pointwise_safe_trajectory_parts_have_a_pointwise_safe_union
    (firstPart tail : Set ℝ) (hp : ∀ value∈firstPart,0 ≤ value)
    (ht : ∀ value∈tail,0 ≤ value) : ∀ value∈firstPart∪tail,0 ≤ value := by
  intro value hv
  rcases hv with hv|hv
  · exact hp value hv
  · exact ht value hv

end SafeLearning.CompleteModulesGoSafeODE
