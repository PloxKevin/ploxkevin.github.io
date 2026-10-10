import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace SafeLearning.CompleteAppliedDiscreteLQR

def sourceP : ℝ := (18+Real.sqrt 949)/25
def otherRoot : ℝ := (18-Real.sqrt 949)/25
def sourceK : ℝ := ((6/5)*sourceP)/(1+sourceP)
def sourcePole : ℝ := 6/5-sourceK
def feedbackTrajectory (initial : ℝ) (n : ℕ) : ℝ := sourcePole^n*initial
def feedbackInput (initial : ℝ) (n : ℕ) : ℝ := -sourceK*feedbackTrajectory initial n

theorem actual_sqrt_and_both_source_riccati_roots :
    (Real.sqrt 949)^2=949 ∧
    30 < Real.sqrt 949 ∧ Real.sqrt 949 < 31 ∧
    sourceP^2-(36/25)*sourceP-1=0 ∧
    otherRoot^2-(36/25)*otherRoot-1=0 ∧
    1 < sourceP ∧ otherRoot < 0 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤949)
  have hn := Real.sqrt_nonneg (949:ℝ)
  have hl : 30<Real.sqrt 949 := by nlinarith
  have hu : Real.sqrt 949<31 := by nlinarith
  refine ⟨hs,hl,hu,?_,?_,?_,?_⟩ <;> dsimp [sourceP,otherRoot] <;> nlinarith

theorem actual_source_riccati_polynomial_has_exactly_the_two_roots (p : ℝ) :
    p^2-(36/25)*p-1=0 ↔ p=sourceP ∨ p=otherRoot := by
  have hs := actual_sqrt_and_both_source_riccati_roots.1
  constructor
  · intro hp
    have hf : (p-sourceP)*(p-otherRoot)=0 := by
      dsimp [sourceP,otherRoot]
      nlinarith
    rcases mul_eq_zero.mp hf with h|h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h)
  · rintro (rfl|rfl)
    · exact actual_sqrt_and_both_source_riccati_roots.2.2.2.1
    · exact actual_sqrt_and_both_source_riccati_roots.2.2.2.2.1

theorem actual_source_scalar_DARE_is_the_polynomial (p : ℝ) (hp : p≠-1) :
    (p=1+(36/25)*p-(36/25)*p^2/(1+p)) ↔ p^2-(36/25)*p-1=0 := by
  have hn : 1+p≠0 := by intro h;apply hp;linarith
  constructor
  · intro h
    have he : (36/25)*p^2/(1+p)=1+(36/25)*p-p := by linarith
    have hmul := (div_eq_iff hn).mp he
    nlinarith
  · intro h
    have he : (36/25)*p^2/(1+p)=1+(36/25)*p-p := by
      apply (div_eq_iff hn).mpr
      nlinarith
    linarith

theorem actual_unique_nonnegative_DARE_solution (p : ℝ) (hp : 0≤p) :
    (p=1+(36/25)*p-(36/25)*p^2/(1+p)) ↔ p=sourceP := by
  rw [actual_source_scalar_DARE_is_the_polynomial p (by linarith),
    actual_source_riccati_polynomial_has_exactly_the_two_roots]
  constructor
  · rintro (h|h)
    · exact h
    · rw [h] at hp
      linarith [actual_sqrt_and_both_source_riccati_roots.2.2.2.2.2.2]
  · exact Or.inl

theorem actual_source_root_has_the_literal_radical_formula :
    sourceP=((36/25)+Real.sqrt ((36/25:ℝ)^2+4))/2 := by
  have hs := actual_sqrt_and_both_source_riccati_roots.1
  have hn := Real.sqrt_nonneg (949:ℝ)
  have hd := Real.sq_sqrt (by norm_num : (0:ℝ)≤(36/25:ℝ)^2+4)
  have hdn := Real.sqrt_nonneg ((36/25:ℝ)^2+4)
  have he : Real.sqrt ((36/25:ℝ)^2+4)=2*Real.sqrt 949/25 := by nlinarith
  rw [he]
  dsimp [sourceP]
  ring

theorem actual_gain_and_pole_are_derived_and_stabilizing :
    0<sourceK ∧ sourceK<6/5 ∧
    sourcePole=(6/5)/(1+sourceP) ∧
    0<sourcePole ∧ sourcePole<1 := by
  have hp : 1<sourceP := actual_sqrt_and_both_source_riccati_roots.2.2.2.2.2.1
  have hd : 0<1+sourceP := by linarith
  have hk : 0<sourceK := by unfold sourceK;positivity
  have hu : sourceK<6/5 := by
    unfold sourceK
    apply (div_lt_iff₀ hd).mpr
    nlinarith
  have he : sourcePole=(6/5)/(1+sourceP) := by
    unfold sourcePole sourceK
    field_simp
    ring
  refine ⟨hk,hu,he,?_,?_⟩
  · rw [he];positivity
  · rw [he];apply (div_lt_one hd).mpr;linarith

theorem actual_feedback_trajectory_has_the_initial_and_source_recurrence
    (initial : ℝ) : feedbackTrajectory initial 0=initial ∧
    ∀n,feedbackTrajectory initial (n+1)=
      (6/5)*feedbackTrajectory initial n+feedbackInput initial n := by
  constructor
  · simp [feedbackTrajectory]
  · intro n
    dsimp [feedbackTrajectory,feedbackInput,sourcePole]
    rw [pow_succ]
    ring

theorem actual_every_feedback_recurrence_is_the_constructed_trajectory
    (x : ℕ → ℝ) (initial : ℝ) (h0 : x 0=initial)
    (hnext : ∀n,x (n+1)=(6/5)*x n-sourceK*x n) :
    ∀n,x n=feedbackTrajectory initial n := by
  intro n
  induction n with
  | zero => simp [h0,feedbackTrajectory]
  | succ n ih =>
    rw [hnext,ih]
    dsimp [feedbackTrajectory,sourcePole]
    rw [pow_succ]
    ring

theorem actual_optimal_feedback_all_initial_states_converge (initial : ℝ) :
    Tendsto (feedbackTrajectory initial) atTop (𝓝 0) := by
  have hp := actual_gain_and_pole_are_derived_and_stabilizing
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one hp.2.2.2.1.le hp.2.2.2.2
  change Tendsto (fun n : ℕ => sourcePole^n*initial) atTop (𝓝 0)
  simpa only [zero_mul] using ht.mul_const initial

theorem actual_scaled_gain_stability_region_is_exact (kappa : ℝ) :
    |(6/5)-kappa*sourceK|<1 ↔
      ((1/5)/sourceK<kappa ∧ kappa<(11/5)/sourceK) := by
  have hk := actual_gain_and_pole_are_derived_and_stabilizing.1
  rw [abs_lt,div_lt_iff₀ hk,lt_div_iff₀ hk]
  constructor <;> intro h <;> constructor <;> nlinarith [h.1,h.2]

theorem actual_scaled_gain_all_initial_convergence_iff (kappa : ℝ) :
    (∀initial : ℝ,Tendsto (fun n : ℕ => ((6/5)-kappa*sourceK)^n*initial)
      atTop (𝓝 0)) ↔ ((1/5)/sourceK<kappa ∧ kappa<(11/5)/sourceK) := by
  rw [←actual_scaled_gain_stability_region_is_exact]
  constructor
  · intro h
    have ht : Tendsto (fun n : ℕ => ((6/5)-kappa*sourceK)^n) atTop (𝓝 0) := by
      simpa using h 1
    simpa only [Real.norm_eq_abs] using tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mp ht
  · intro h initial
    have ht := tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mpr
      (show ‖(6/5:ℝ)-kappa*sourceK‖<1 by simpa only [Real.norm_eq_abs] using h)
    simpa using ht.mul_const initial

end SafeLearning.CompleteAppliedDiscreteLQR
