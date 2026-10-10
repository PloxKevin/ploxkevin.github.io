import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology NNReal

namespace SafeLearning.CompleteModulesLandscapeRegularBoundaryDomainCountermodel

def domain : Set ℝ := Iic 0
def barrier (x : ℝ) : ℝ := -x
def field (x : ℝ) : ℝ := Real.sqrt (max x 0)
def controller (_ : ℝ) : ℝ := 0
def alpha (r : ℝ) : ℝ := r
def trajectory (t : ℝ) : ℝ := t ^ 2 / 4

/-- The safe domain is closed and is exactly the superlevel set of a globally
C1 defining function. The zero controller is globally Lipschitz. -/
theorem actual_closed_domain_has_a_globally_C1_barrier_and_Lipschitz_zero_controller :
    IsClosed domain ∧ domain = {x | 0 ≤ barrier x} ∧
      ContDiff ℝ 1 barrier ∧ LipschitzWith 0 controller ∧ Continuous field := by
  refine ⟨isClosed_Iic,?_,?_,?_,?_⟩
  · ext x
    simp [domain,barrier]
  · unfold barrier
    fun_prop
  · unfold controller
    exact LipschitzWith.const (0 : ℝ)
  · unfold field
    fun_prop

/-- The field is identically zero on the closed safe domain, so both global
relative Lipschitzness and relative local Lipschitzness hold with constant zero. -/
theorem actual_field_is_zero_and_Lipschitz_on_the_closed_domain :
    (∀ x ∈ domain, field x = 0) ∧
      LipschitzOnWith 0 field domain ∧ LocallyLipschitzOn domain field := by
  have hz : ∀ x ∈ domain, field x = 0 := by
    intro x hx
    simp only [domain,mem_Iic] at hx
    simp only [field,max_eq_right hx,Real.sqrt_zero]
  have hL : LipschitzOnWith 0 field domain := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simp only [hz x hx,hz y hy,dist_self,NNReal.coe_zero,zero_mul,le_refl]
  refine ⟨hz,hL,?_⟩
  intro x hx
  exact ⟨0,domain,self_mem_nhdsWithin,hL⟩

/-- The actual differential is evaluation by minus one at every real point. -/
theorem actual_barrier_differential (x v : ℝ) : fderiv ℝ barrier x v = -v := by
  unfold barrier
  simp

/-- Every zero is regular, the boundary Lie derivative is zero, and even the
full on-domain barrier inequality with alpha=id holds. -/
theorem actual_regular_boundary_and_full_relative_barrier_inequality_hold :
    (∀ x : ℝ, fderiv ℝ barrier x ≠ 0) ∧
      (∀ x ∈ domain, -alpha (barrier x) ≤ fderiv ℝ barrier x (field x)) ∧
      (∀ x ∈ domain, barrier x = 0 → fderiv ℝ barrier x (field x) = 0) := by
  have hz := actual_field_is_zero_and_Lipschitz_on_the_closed_domain.1
  refine ⟨?_,?_,?_⟩
  · intro x heq
    have heval : fderiv ℝ barrier x 1 = 0 := by rw [heq]; simp
    rw [actual_barrier_differential] at heval
    norm_num at heval
  · intro x hx
    rw [actual_barrier_differential,hz x hx]
    simpa only [alpha,barrier,neg_neg,neg_zero,domain,mem_Iic] using hx
  · intro x hx _
    rw [actual_barrier_differential,hz x hx,neg_zero]

/-- The actual polynomial path solves x'=sqrt(max x 0) at every nonnegative
time, including time zero. Its derivative is proved, not postulated. -/
theorem actual_moving_path_solves_the_ODE_at_every_nonnegative_time
    (t : ℝ) (ht : 0 ≤ t) : HasDerivAt trajectory (field (trajectory t)) t := by
  have hsq : trajectory t = (t / 2) ^ 2 := by unfold trajectory; ring
  have hfield : field (trajectory t) = t / 2 := by
    rw [hsq]
    simp only [field,max_eq_left (sq_nonneg (t / 2))]
    exact Real.sqrt_sq (div_nonneg ht (by norm_num))
  rw [hfield]
  unfold trajectory
  convert ((hasDerivAt_id t).pow 2).div_const 4 using 1
  · rfl
  · simp only [id_eq]
    ring

/-- Relative Lipschitz data on a closed safe domain and a regular C1 boundary
do not force every true solution of the globally defined field to remain safe.
The path has a genuine within derivative on the entire forward time domain. -/
theorem actual_closed_domain_relative_Lipschitz_regular_barrier_has_an_escaping_true_solution :
    IsClosed domain ∧ domain = {x | 0 ≤ barrier x} ∧
      ContDiff ℝ 1 barrier ∧ LipschitzWith 0 controller ∧
      LipschitzOnWith 0 field domain ∧ LocallyLipschitzOn domain field ∧
      (∀ x ∈ domain, -alpha (barrier x) ≤ fderiv ℝ barrier x (field x)) ∧
      (∀ x ∈ domain, barrier x = 0 →
        fderiv ℝ barrier x ≠ 0 ∧ 0 ≤ fderiv ℝ barrier x (field x)) ∧
      trajectory 0 = 0 ∧ (0 : ℝ) ∈ domain ∧
      (∀ t ∈ Ici 0, HasDerivWithinAt trajectory (field (trajectory t)) (Ici 0) t) ∧
      ∃ t > (0 : ℝ), trajectory t ∉ domain ∧ barrier (trajectory t) < 0 := by
  obtain ⟨hclosed,hsafe,hC1,hcontroller,_⟩ :=
    actual_closed_domain_has_a_globally_C1_barrier_and_Lipschitz_zero_controller
  obtain ⟨_,hLip,hlocal⟩ := actual_field_is_zero_and_Lipschitz_on_the_closed_domain
  obtain ⟨hregular,hbarrier,hzero⟩ := actual_regular_boundary_and_full_relative_barrier_inequality_hold
  refine ⟨hclosed,hsafe,hC1,hcontroller,hLip,hlocal,hbarrier,?_,?_,?_,?_,?_⟩
  · intro x hx hz
    exact ⟨hregular x,by rw [hzero x hx hz]⟩
  · norm_num [trajectory]
  · change (0 : ℝ) ≤ 0
    exact le_rfl
  · intro t ht
    exact (actual_moving_path_solves_the_ODE_at_every_nonnegative_time t ht).hasDerivWithinAt
  · refine ⟨1,by norm_num,?_,?_⟩ <;> norm_num [trajectory,domain,barrier]

end SafeLearning.CompleteModulesLandscapeRegularBoundaryDomainCountermodel
