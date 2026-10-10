import Mathlib
open Set
noncomputable section
example (v L : ℝ) (hv : 0 < v) (hL : 0 < L) :
    L / Real.sqrt (2*L/v) + Real.sqrt (2*L/v)*v/2 = Real.sqrt (2*v*L) := by
  have hx : 0 < Real.sqrt (2*L/v) := Real.sqrt_pos.2 (by positivity)
  have hsq : Real.sqrt (2*L/v)^2=2*L/v := Real.sq_sqrt (by positivity)
  have hsqv : Real.sqrt (2*L/v)^2*v=2*L := by
    rw [hsq]; field_simp
  have hratio : L / Real.sqrt (2*L/v)=Real.sqrt (2*L/v)*v/2 := by
    apply (div_eq_iff hx.ne').2
    nlinarith [hsqv]
  rw [hratio]
  have he : Real.sqrt (2*L/v)*v=Real.sqrt (2*v*L) := by
    apply (Real.sqrt_eq_iff (by positivity) (by positivity)).2
    nlinarith [hsqv]
  nlinarith
