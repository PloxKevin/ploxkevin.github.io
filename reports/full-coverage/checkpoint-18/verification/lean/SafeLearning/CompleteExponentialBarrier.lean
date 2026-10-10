import SafeLearning.CompleteCoreControl

set_option autoImplicit false
noncomputable section
open Set Matrix Polynomial
open scoped BigOperators

namespace SafeLearning.CompleteExponentialBarrier

def barrier (p : ℝ) : ℝ := 1 - p
def eta (p v : ℝ) : Fin 2 → ℝ := ![barrier p, -v]
def companion : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]
def inputVector : Fin 2 → ℝ := ![0, 1]
def closedMatrix (k1 k2 : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -k1, -k2]
def auxiliary (pole p v : ℝ) : ℝ := -v + pole * barrier p
def auxiliaryRate (pole v u : ℝ) : ℝ := -u - pole * v

theorem genuine_double_integrator_barrier_derivatives (p v : ℝ → ℝ) (u t : ℝ)
    (hp : HasDerivAt p (v t) t) (hv : HasDerivAt v u t) :
    HasDerivAt (fun s => barrier (p s)) (-v t) t ∧
      HasDerivAt (fun s => -v s) (-u) t := by
  constructor
  · convert (hasDerivAt_const t (1 : ℝ)).sub hp using 1 <;>
      first | (ext s; simp [barrier, Pi.sub_apply]) | simp
  · exact hv.neg

theorem actual_companion_dynamics (p v u : ℝ) :
    companion *ᵥ eta p v + (-u) • inputVector = (![ -v, -u] : Fin 2 → ℝ) := by
  ext i
  fin_cases i <;> simp [companion, eta, inputVector, mulVec, dotProduct, Fin.sum_univ_two]

theorem exact_affine_ECBF_constraint (p v u k1 k2 : ℝ) :
    -u ≥ -(k1 * barrier p + k2 * (-v)) ↔ u ≤ k1 * (1 - p) - k2 * v := by
  unfold barrier
  constructor <;> intro h <;> linarith

theorem actual_closed_loop_characteristic_polynomial (k1 k2 : ℝ) :
    (closedMatrix k1 k2).charpoly = X ^ 2 + C k2 * X + C k1 := by
  rw [Matrix.charpoly_fin_two]
  simp [closedMatrix, Matrix.trace, Matrix.diag, Matrix.det_fin_two, Fin.sum_univ_two]

theorem actual_real_pole_factorization (p1 p2 lambda : ℝ) :
    (closedMatrix (p1 * p2) (p1 + p2)).charpoly.eval lambda =
      (lambda + p1) * (lambda + p2) := by
  rw [actual_closed_loop_characteristic_polynomial]
  simp
  ring

theorem actual_real_roots_and_discriminant (p1 p2 : ℝ) (h1 : 0 < p1) (h2 : 0 < p2) :
    (∀ lambda : ℝ, (closedMatrix (p1 * p2) (p1 + p2)).charpoly.eval lambda = 0 ↔
      lambda = -p1 ∨ lambda = -p2) ∧
      (-p1 < 0 ∧ -p2 < 0) ∧ 4 * (p1 * p2) ≤ (p1 + p2) ^ 2 := by
  refine ⟨?_, ⟨by linarith, by linarith⟩, ?_⟩
  · intro lambda
    rw [actual_real_pole_factorization, mul_eq_zero]
    constructor <;> rintro (h | h)
    · left; linarith
    · right; linarith
    · left; linarith
    · right; linarith
  · nlinarith [sq_nonneg (p1 - p2)]

theorem genuine_auxiliary_derivative (p v : ℝ → ℝ) (pole u t : ℝ)
    (hp : HasDerivAt p (v t) t) (hv : HasDerivAt v u t) :
    HasDerivAt (fun s => auxiliary pole (p s) (v s)) (auxiliaryRate pole (v t) u) t := by
  convert hv.neg.add (((hasDerivAt_const t (1 : ℝ)).sub hp).const_mul pole) using 1 <;>
    first | (ext s; simp [auxiliary, barrier]) | (simp [auxiliaryRate]; ring)

theorem actual_initial_auxiliary_condition (p1 : ℝ) :
    barrier 0 = 1 ∧ auxiliary p1 0 1 = -1 + p1 ∧
      (0 ≤ auxiliary p1 0 1 ↔ 1 ≤ p1) := by
  simp [barrier, auxiliary]

theorem correct_positive_margin_ratio (margin rate pole : ℝ) (hm : 0 < margin) :
    0 ≤ rate + pole * margin ↔ -rate / margin ≤ pole := by
  rw [div_le_iff₀ hm]
  constructor <;> intro h <;> linarith

theorem zero_margin_initial_condition (rate pole : ℝ) :
    0 ≤ rate + pole * (0 : ℝ) ↔ 0 ≤ rate := by simp

theorem actual_second_initial_condition (p1 p2 u : ℝ) :
    0 ≤ auxiliaryRate p1 1 u + p2 * auxiliary p1 0 1 ↔
      u ≤ p1 * p2 - (p1 + p2) := by
  unfold auxiliaryRate auxiliary barrier
  constructor <;> intro h <;> nlinarith

theorem literal_negative_eigenvalue_condition_is_impossible (lambda : ℝ)
    (hnegative : lambda < 0) : ¬ 1 ≤ lambda := by linarith

theorem actual_admissible_source_choice (p v u : ℝ) :
    auxiliary 2 0 1 = 1 ∧
      (closedMatrix 4 4).charpoly.eval (-2) = 0 ∧
      (-u ≥ -(4 * barrier p + 4 * (-v)) ↔ u ≤ 4 * (1 - p) - 4 * v) ∧
      (0 ≤ auxiliaryRate 2 1 u + 2 * auxiliary 2 0 1 ↔ u ≤ 0) := by
  refine ⟨by norm_num [auxiliary, barrier], ?_, exact_affine_ECBF_constraint _ _ _ _ _, ?_⟩
  · rw [actual_closed_loop_characteristic_polynomial]
    norm_num
  · norm_num [actual_second_initial_condition]

end SafeLearning.CompleteExponentialBarrier
