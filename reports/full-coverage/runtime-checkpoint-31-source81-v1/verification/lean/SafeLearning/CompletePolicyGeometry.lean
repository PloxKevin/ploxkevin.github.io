import Mathlib

set_option autoImplicit false
noncomputable section
open Set
open scoped Matrix BigOperators

namespace SafeLearning.CompletePolicyGeometry

abbrev Plane := EuclideanSpace ℝ (Fin 2)
def vector (first second : ℝ) : Plane := WithLp.toLp 2 ![first, second]
def curvature : Matrix (Fin 2) (Fin 2) ℝ := !![4, 0; 0, 1]
def quadratic (x : Plane) : ℝ := dotProduct (WithLp.ofLp x)
  (curvature *ᵥ WithLp.ofLp x)
def trustCost (x : Plane) : ℝ := (1 / 2) * quadratic x

theorem genuine_matrix_quadratic (x : Plane) :
    quadratic x = 4 * x 0 ^ 2 + x 1 ^ 2 := by
  simp [quadratic, curvature, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

theorem actual_ellipse_iff (x : Plane) :
    trustCost x ≤ 1 / 2 ↔ 4 * x 0 ^ 2 + x 1 ^ 2 ≤ 1 := by
  rw [trustCost, genuine_matrix_quadratic]
  constructor <;> intro h <;> linarith

theorem actual_axis_intercepts (t : ℝ) :
    (trustCost (vector t 0) ≤ 1 / 2 ↔ |t| ≤ 1 / 2) ∧
      (trustCost (vector 0 t) ≤ 1 / 2 ↔ |t| ≤ 1) := by
  simp only [actual_ellipse_iff, vector,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  norm_num only [zero_pow, mul_zero, add_zero, zero_add]
  constructor
  · rw [abs_le]
    constructor
    · intro h
      constructor <;> nlinarith [sq_nonneg (t - 1 / 2), sq_nonneg (t + 1 / 2)]
    · rintro ⟨hl, hu⟩
      nlinarith [mul_nonneg (by linarith : 0 ≤ t + 1 / 2)
        (by linarith : 0 ≤ 1 / 2 - t)]
  · rw [abs_le]
    constructor
    · intro h
      constructor <;> nlinarith [sq_nonneg (t - 1), sq_nonneg (t + 1)]
    · rintro ⟨hl, hu⟩
      nlinarith [mul_nonneg (by linarith : 0 ≤ t + 1)
        (by linarith : 0 ≤ 1 - t)]

theorem actual_first_axis_boundary :
    quadratic (vector (1 / 2) 0) = 1 ∧
      trustCost (vector (1 / 2) 0) = 1 / 2 := by
  norm_num [genuine_matrix_quadratic, trustCost, vector]

def target : Plane := vector (3 / 5) (1 / 5)
def projection : Plane := vector (1 / 10) (1 / 5)
def distanceObjective (x : Plane) : ℝ := (1 / 2) * ‖x - target‖ ^ 2

theorem actual_squared_distance (x : Plane) :
    ‖x - target‖ ^ 2 = (x 0 - 3 / 5) ^ 2 + (x 1 - 1 / 5) ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, target, vector]

theorem source_projection_displacement :
    projection - target = vector (-1 / 2) 0 := by
  ext i
  fin_cases i <;> norm_num [projection, target, vector]

theorem actual_projection_distance_and_objective :
    ‖projection - target‖ = 1 / 2 ∧ distanceObjective projection = 1 / 8 := by
  have hs : ‖projection - target‖ ^ 2 = 1 / 4 := by
    norm_num [actual_squared_distance, projection, vector]
  constructor
  · nlinarith [norm_nonneg (projection - target)]
  · unfold distanceObjective
    rw [hs]
    norm_num

theorem genuine_unique_euclidean_projection (x : Plane) (hx : x 0 ≤ 1 / 10) :
    projection 0 ≤ 1 / 10 ∧ distanceObjective projection ≤ distanceObjective x ∧
      (distanceObjective x = distanceObjective projection ↔ x = projection) := by
  have hfirst : 1 / 4 ≤ (x 0 - 3 / 5) ^ 2 := by
    nlinarith [sq_nonneg (x 0 - 1 / 10)]
  have hsecond := sq_nonneg (x 1 - 1 / 5)
  have hp := actual_projection_distance_and_objective.2
  have he : distanceObjective x =
      (1 / 2) * ((x 0 - 3 / 5) ^ 2 + (x 1 - 1 / 5) ^ 2) := by
    rw [distanceObjective, actual_squared_distance]
  refine ⟨by norm_num [projection, vector], by nlinarith, ?_⟩
  constructor
  · intro h
    have h0 : x 0 = 1 / 10 := by nlinarith [sq_nonneg (x 0 - 1 / 10)]
    have h1 : x 1 = 1 / 5 := by nlinarith
    ext i
    fin_cases i
    · simpa [projection, vector] using h0
    · simpa [projection, vector] using h1
  · rintro rfl
    rfl

end SafeLearning.CompletePolicyGeometry
