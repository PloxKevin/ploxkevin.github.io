import Mathlib

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology
namespace SafeLearning.CompleteBarrierFilippovHalfspaces

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual essential closed convex velocity construction. A solution of the
resulting differential inclusion is a separate existence question. -/
def velocities [MeasurableSpace E] (mu : Measure E) (F : E → E) (x : E) : Set E :=
  ⋂ (r : ℝ) (_ : 0 < r) (N : Set E) (_ : mu N = 0),
    closure (convexHull ℝ (F '' (ball x r \ N)))

theorem genuine_closed_halfspace (p : E →L[ℝ] ℝ) (c : ℝ) :
    IsClosed {v : E | c ≤ p v} := isClosed_le continuous_const p.continuous

theorem genuine_convex_halfspace (p : E →L[ℝ] ℝ) (c : ℝ) :
    Convex ℝ {v : E | c ≤ p v} := by
  intro v hv w hw a b ha hb hab
  change c ≤ p (a • v + b • w)
  simp only [map_add, map_smul, smul_eq_mul]
  change c ≤ p v at hv
  change c ≤ p w at hw
  calc
    c = a * c + b * c := by rw [← add_mul, hab, one_mul]
    _ ≤ a * p v + b * p w := add_le_add
      (mul_le_mul_of_nonneg_left hv ha) (mul_le_mul_of_nonneg_left hw hb)

/-- Local boundedness of the actual velocities makes changes in the gradient
uniformly small. This is the step needed before taking convex combinations. -/
theorem genuine_nearby_approximate_inequality (F : E → E) (p : E → E →L[ℝ] ℝ)
    (q : E → ℝ) (x : E) (M : ℝ) (hp : ContinuousAt p x) (hq : ContinuousAt q x)
    (hb : ∀ᶠ z in 𝓝 x, ‖F z‖ ≤ M) (hi : ∀ᶠ z in 𝓝 x, q z ≤ p z (F z))
    (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ z in 𝓝 x, q x - eps ≤ p x (F z) := by
  let gap : E → ℝ := fun z => ‖p x - p z‖ * M + |q z - q x|
  have hgap : ContinuousAt gap x := by
    dsimp [gap]
    fun_prop
  have hsmall : ∀ᶠ z in 𝓝 x, gap z < eps := by
    apply hgap.eventually_lt_const
    simpa [gap] using heps
  filter_upwards [hb, hi, hsmall] with z hb hi hs
  have hn := (p x - p z).le_opNorm (F z)
  have hn' : ‖(p x - p z) (F z)‖ ≤ ‖p x - p z‖ * M :=
    hn.trans (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
  have hl := neg_abs_le ((p x - p z) (F z))
  have hq' := neg_abs_le (q z - q x)
  simp only [sub_apply, Real.norm_eq_abs] at hn' hl
  dsimp [gap] at hs
  linarith

/-- The affine barrier inequality survives the genuine essential convexified
velocity construction. No differential-inclusion existence is assumed here. -/
theorem genuine_filippov_inequality_preservation [MeasurableSpace E]
    (mu : Measure E) (F : E → E) (p : E → E →L[ℝ] ℝ) (q : E → ℝ)
    (x : E) (M : ℝ) (hp : ContinuousAt p x) (hq : ContinuousAt q x)
    (hb : ∀ᶠ z in 𝓝 x, ‖F z‖ ≤ M) (hi : ∀ᶠ z in 𝓝 x, q z ≤ p z (F z))
    (v : E) (hv : v ∈ velocities mu F x) : q x ≤ p x v := by
  apply le_of_forall_pos_le_add
  intro eps heps
  have hnear := genuine_nearby_approximate_inequality F p q x M hp hq hb hi eps heps
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hnear
  have hv' : v ∈ closure (convexHull ℝ (F '' ball x r)) := by
    have h := mem_iInter.mp (mem_iInter.mp (mem_iInter.mp
      (mem_iInter.mp hv r) hr) ∅) (by simp)
    simpa using h
  have hs : F '' ball x r ⊆ {w : E | q x - eps ≤ p x w} := by
    rintro w ⟨z, hz, rfl⟩
    exact hball (mem_ball.mp hz)
  have hclosure := closure_minimal
    (convexHull_min hs (genuine_convex_halfspace (p x) (q x - eps)))
    (genuine_closed_halfspace (p x) (q x - eps))
  have hh := hclosure hv'
  change q x - eps ≤ p x v at hh
  linarith

end SafeLearning.CompleteBarrierFilippovHalfspaces
