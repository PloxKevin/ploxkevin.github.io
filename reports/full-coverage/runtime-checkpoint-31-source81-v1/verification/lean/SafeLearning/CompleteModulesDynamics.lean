import SafeLearning.Modules
import SafeLearning.BookApplications

set_option autoImplicit false
noncomputable section
open Set Filter
namespace SafeLearning.CompleteModulesDynamics

def thermalGain : ℝ := (13+Real.sqrt 5)/20
def thermalFirst (x y : ℝ) : ℝ := (3/5)*x+(1/10)*y
def thermalSecond (x y : ℝ) : ℝ := (1/10)*x+(7/10)*y

theorem thermal_gain_positive_lt_one : 0 < thermalGain ∧ thermalGain < 1 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  have hn := Real.sqrt_nonneg (5:ℝ)
  unfold thermalGain
  constructor <;> nlinarith

theorem thermal_norm_residual_square (x y : ℝ) :
    thermalGain^2*(x^2+y^2)-(thermalFirst x y)^2-(thermalSecond x y)^2=
      (13*(Real.sqrt 5-1)/200)*(y-((1+Real.sqrt 5)/2)*x)^2 := by
  have hs : (Real.sqrt (5:ℝ))^2=5 := Real.sq_sqrt (by norm_num)
  have hc : (Real.sqrt (5:ℝ))^3=5*Real.sqrt 5 := by rw [pow_succ,hs]
  unfold thermalGain thermalFirst thermalSecond
  ring_nf
  rw [hs,hc]
  ring

theorem thermal_exact_squared_norm_bound (x y : ℝ) :
    (thermalFirst x y)^2+(thermalSecond x y)^2 ≤ thermalGain^2*(x^2+y^2) := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  have hn := Real.sqrt_nonneg (5:ℝ)
  have hm : 0 ≤ 13*(Real.sqrt 5-1)/200 := by nlinarith
  have h := mul_nonneg hm (sq_nonneg (y-((1+Real.sqrt 5)/2)*x))
  rw [← thermal_norm_residual_square] at h
  linarith

theorem thermal_gain_eigenvector :
    thermalFirst 1 ((1+Real.sqrt 5)/2)=thermalGain ∧
    thermalSecond 1 ((1+Real.sqrt 5)/2)=thermalGain*((1+Real.sqrt 5)/2) := by
  have hs : (Real.sqrt (5:ℝ))^2=5 := Real.sq_sqrt (by norm_num)
  unfold thermalFirst thermalSecond thermalGain
  constructor
  · ring
  · nlinarith

theorem thermal_radius_gain (x y r : ℝ) (hr : 0 ≤ r) (h : x^2+y^2 ≤ r^2) :
    Real.sqrt ((thermalFirst x y)^2+(thermalSecond x y)^2) ≤ thermalGain*r := by
  have hq := thermal_gain_positive_lt_one.1
  have hsq := thermal_exact_squared_norm_bound x y
  have hm := mul_le_mul_of_nonneg_left h (sq_nonneg thermalGain)
  have hn : 0 ≤ thermalGain*r := mul_nonneg (le_of_lt hq) hr
  apply (Real.sqrt_le_iff).mpr
  exact ⟨hn,by nlinarith⟩

theorem thermal_unit_disk_with_disturbance_budget : thermalGain+1/20 ≤ 1 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  have hn := Real.sqrt_nonneg (5:ℝ)
  unfold thermalGain
  nlinarith

def l2 (x y : ℝ) : ℝ := Real.sqrt (x^2+y^2)

theorem l2_triangle (x y w v : ℝ) : l2 (x+w) (y+v) ≤ l2 x y+l2 w v := by
  have hsx : (l2 x y)^2=x^2+y^2 := Real.sq_sqrt (by positivity)
  have hsw : (l2 w v)^2=w^2+v^2 := Real.sq_sqrt (by positivity)
  have hx0 : 0 ≤ l2 x y := Real.sqrt_nonneg _
  have hw0 : 0 ≤ l2 w v := Real.sqrt_nonneg _
  have hc : (x*w+y*v)^2+(x*v-y*w)^2=(x^2+y^2)*(w^2+v^2) := by ring
  have hprod : (l2 x y*l2 w v)^2=(x^2+y^2)*(w^2+v^2) := by rw [mul_pow,hsx,hsw]
  have hbound : x*w+y*v ≤ l2 x y*l2 w v := by
    exact le_of_sq_le_sq (by nlinarith [sq_nonneg (x*v-y*w)]) (mul_nonneg hx0 hw0)
  apply (Real.sqrt_le_iff).mpr
  exact ⟨add_nonneg hx0 hw0,by nlinarith⟩

theorem thermal_l2_gain (x y : ℝ) :
    l2 (thermalFirst x y) (thermalSecond x y) ≤ thermalGain*l2 x y := by
  apply thermal_radius_gain x y (l2 x y) (Real.sqrt_nonneg _)
  unfold l2
  rw [Real.sq_sqrt (by positivity)]

theorem thermal_disturbed_step (x y w v : ℝ) :
    l2 (thermalFirst x y+w) (thermalSecond x y+v) ≤ thermalGain*l2 x y+l2 w v := by
  exact (l2_triangle (thermalFirst x y) (thermalSecond x y) w v).trans
    (add_le_add (thermal_l2_gain x y) le_rfl)

theorem thermal_disturbed_unit_disk (x y w v : ℝ)
    (hx : l2 x y ≤ 1) (hw : l2 w v ≤ 1/20) :
    l2 (thermalFirst x y+w) (thermalSecond x y+v) ≤ 1 := by
  have h := thermal_disturbed_step x y w v
  have hq := thermal_gain_positive_lt_one.1
  have hb := thermal_unit_disk_with_disturbance_budget
  nlinarith [mul_le_mul_of_nonneg_left hx (le_of_lt hq)]

theorem thermal_constant_forcing_equilibrium :
    thermalFirst (3/22) (1/22)+1/20=3/22 ∧
    thermalSecond (3/22) (1/22)=1/22 ∧
    l2 (1/20) 0=1/20 := by
  norm_num [thermalFirst,thermalSecond,l2]

theorem thermal_forced_trajectory_not_zero :
    ¬ Tendsto (fun _n : ℕ => (3/22:ℝ)) atTop (nhds 0) := by
  intro h
  have hc : Tendsto (fun _n : ℕ => (3/22:ℝ)) atTop (nhds (3/22:ℝ)) := tendsto_const_nhds
  have he := tendsto_nhds_unique hc h
  norm_num at he

-- Stability of the actual delayed two-state linear recurrence, via an exact
-- Lyapunov solution instead of decimal complex-eigenvalue approximations.
def delayStorage (x y : ℝ) : ℝ := (325/77)*x^2-(135/77)*x*y+(425/308)*y^2

theorem delayed_storage_bounds (x y : ℝ) :
    (1/2)*(x^2+y^2) ≤ delayStorage x y ∧ delayStorage x y ≤ 6*(x^2+y^2) := by
  unfold delayStorage
  constructor
  · nlinarith [sq_nonneg (x-y),sq_nonneg x,sq_nonneg y]
  · nlinarith [sq_nonneg (x+y),sq_nonneg x,sq_nonneg y]

theorem delayed_storage_exact_decrease (x y : ℝ) :
    delayStorage ((9/10)*x-(3/10)*y) x-delayStorage x y= -(x^2+y^2) := by
  unfold delayStorage
  ring

theorem delayed_storage_contraction (x y : ℝ) :
    delayStorage ((9/10)*x-(3/10)*y) x ≤ (5/6)*delayStorage x y := by
  have hi := delayed_storage_exact_decrease x y
  have hb := (delayed_storage_bounds x y).2
  linarith

theorem delayed_trajectory_energy (x y : ℕ → ℝ)
    (hx : ∀ n, x (n+1)=(9/10)*x n-(3/10)*y n)
    (hy : ∀ n, y (n+1)=x n) :
    ∀ n, x n^2+y n^2 ≤ 2*(5/6)^n*delayStorage (x 0) (y 0) := by
  have hs : ∀ n, delayStorage (x n) (y n) ≤ (5/6)^n*delayStorage (x 0) (y 0) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [hx,hy,pow_succ]
      have hm := mul_le_mul_of_nonneg_left ih (by norm_num : (0:ℝ) ≤ 5/6)
      have hc := delayed_storage_contraction (x n) (y n)
      nlinarith
  intro n
  have hlo := (delayed_storage_bounds (x n) (y n)).1
  nlinarith [hs n]

theorem delayed_trajectory_energy_tends_zero (x y : ℕ → ℝ)
    (hx : ∀ n, x (n+1)=(9/10)*x n-(3/10)*y n)
    (hy : ∀ n, y (n+1)=x n) :
    Tendsto (fun n => x n^2+y n^2) atTop (nhds 0) := by
  have hp : Tendsto (fun n : ℕ => (5/6:ℝ)^n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hb : Tendsto (fun n : ℕ => 2*(5/6:ℝ)^n*delayStorage (x 0) (y 0)) atTop (nhds 0) := by
    simpa using (hp.const_mul 2).mul_const (delayStorage (x 0) (y 0))
  exact squeeze_zero (fun n => add_nonneg (sq_nonneg _) (sq_nonneg _))
    (delayed_trajectory_energy x y hx hy) hb

end SafeLearning.CompleteModulesDynamics
