import SafeLearning.CompleteFoundationsAlgorithms
import SafeLearning.CompleteFoundationsLogic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped BigOperators Topology NNReal

namespace SafeLearning.CompleteFoundationsQuadraticExercises

def gradientStep (eta x : ℝ) : ℝ := x-eta*(4*x)
def gradientIteration (eta : ℝ) (n : ℕ) : ℝ := (gradientStep eta)^[n] 2

theorem actual_scalar_derivative (x : ℝ) :
    HasDerivAt (fun z : ℝ => 2*z^2) (4*x) x := by
  convert ((hasDerivAt_id x).fun_pow 2).const_mul 2 using 1 <;> simp <;> ring

theorem actual_scalar_second_derivative (x : ℝ) :
    HasDerivAt (fun z : ℝ => 4*z) 4 x := by
  simpa using (hasDerivAt_id x).const_mul 4

theorem scalar_gradient_smooth : LipschitzWith 4 (fun x : ℝ => 4*x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq,Real.dist_eq,← mul_sub,abs_mul]
  norm_num

theorem gradient_closed_form (eta : ℝ) (n : ℕ) :
    gradientIteration eta n=(1-4*eta)^n*2 := by
  have heq : gradientStep eta=(fun x : ℝ => (1-4*eta)*x) := by
    ext x
    unfold gradientStep
    ring
  rw [gradientIteration,heq,SafeLearning.CompleteFoundationsAlgorithms.scaling_iteration]

theorem gradient_recurrence (eta : ℝ) (n : ℕ) :
    gradientIteration eta (n+1)=(1-4*eta)*gradientIteration eta n := by
  simp only [gradient_closed_form,pow_succ]
  ring

theorem source_initial_iterates :
    gradientIteration (2/5) 0=2 ∧ gradientIteration (2/5) 1= -6/5 ∧
    gradientIteration (2/5) 2=18/25 ∧ gradientIteration (3/5) 1= -14/5 ∧
    gradientIteration (3/5) 2=98/25 := by norm_num [gradient_closed_form]

theorem source_alternating_signs (n : ℕ) :
    0<gradientIteration (2/5) (2*n) ∧ gradientIteration (2/5) (2*n+1)<0 := by
  have heven : gradientIteration (2/5) (2*n)=2*(9/25 : ℝ)^n := by
    rw [gradient_closed_form,pow_mul]
    norm_num
    ring
  have hodd : gradientIteration (2/5) (2*n+1)= -(6/5)*(9/25 : ℝ)^n := by
    rw [gradient_closed_form,pow_add,pow_mul]
    norm_num
    ring
  rw [heven,hodd]
  constructor
  · positivity
  · have hp := pow_pos (by norm_num : (0 : ℝ)<9/25) n
    nlinarith

theorem source_magnitude_strictly_decreases (n : ℕ) :
    |gradientIteration (2/5) (n+1)|=(3/5 : ℝ)*|gradientIteration (2/5) n| ∧
    |gradientIteration (2/5) (n+1)| < |gradientIteration (2/5) n| := by
  have heq : |gradientIteration (2/5) (n+1)|=(3/5 : ℝ)*|gradientIteration (2/5) n| := by
    rw [gradient_recurrence,abs_mul]
    norm_num
  have hne : gradientIteration (2/5) n≠0 := by
    rw [gradient_closed_form]
    norm_num
  refine ⟨heq,?_⟩
  rw [heq]
  nlinarith [abs_pos.mpr hne]

theorem source_coordinate_not_monotone :
    ¬ Monotone (gradientIteration (2/5)) ∧ ¬ Antitone (gradientIteration (2/5)) := by
  constructor
  · intro h
    have hh := h (show (0 : ℕ)≤1 by norm_num)
    norm_num [gradient_closed_form] at hh
  · intro h
    have hh := h (show (1 : ℕ)≤2 by norm_num)
    norm_num [gradient_closed_form] at hh

theorem quarter_step_reaches_minimum (n : ℕ) (hn : 1≤n) : gradientIteration (1/4) n=0 := by
  rw [gradient_closed_form]
  norm_num [zero_pow (by omega : n≠0)]

theorem scalar_unique_global_minimum (x : ℝ) :
    0≤2*x^2 ∧ (2*x^2=0 ↔ x=0) := by
  constructor
  · positivity
  · constructor
    · intro h
      nlinarith [sq_nonneg x]
    · rintro rfl
      norm_num

theorem half_step_forever_alternates (n : ℕ) : gradientIteration (1/2) n=2*(-1 : ℝ)^n := by
  rw [gradient_closed_form]
  norm_num
  ring

theorem half_step_has_no_limit : ¬ ∃ l : ℝ,Tendsto (gradientIteration (1/2)) atTop (𝓝 l) := by
  rintro ⟨l,hl⟩
  have hh := hl.mul_const (1/2 : ℝ)
  have heq : (fun n : ℕ => gradientIteration (1/2) n*(1/2))=(fun n => (-1 : ℝ)^n) := by
    ext n
    rw [half_step_forever_alternates]
    ring
  rw [heq] at hh
  exact SafeLearning.CompleteFoundationsLogic.alternating_unit_sequence_not_convergent ⟨l*(1/2),hh⟩

theorem generic_oversized_gradient_diverges (L eta x₀ : ℝ)
    (hL : 0<L) (heta : 2/L<eta) (hx : x₀≠0) :
    Tendsto (fun n : ℕ => |(fun x : ℝ => x-eta*(L*x))^[n] x₀|) atTop atTop := by
  have hprod : 2<eta*L := (div_lt_iff₀ hL).mp heta
  have hq : 1 < |1-eta*L| := lt_of_lt_of_le (by linarith : (1 : ℝ)< -(1-eta*L)) (neg_le_abs _)
  have heq : (fun x : ℝ => x-eta*(L*x))=(fun x => (1-eta*L)*x) := by
    ext x
    ring
  rw [heq]
  exact SafeLearning.CompleteFoundationsAlgorithms.expanding_scaling_norm _ _ hq hx

theorem source_large_step_diverges : Tendsto (fun n => |gradientIteration (3/5) n|) atTop atTop := by
  exact generic_oversized_gradient_diverges 4 (3/5) 2 (by norm_num) (by norm_num) (by norm_num)

theorem source_objective_decreases (n : ℕ) :
    2*(gradientIteration (2/5) (n+1))^2≤2*(gradientIteration (2/5) n)^2 := by
  have hh := SafeLearning.CompleteFoundationsAlgorithms.scalar_gradient_objective_decreases (2/5)
    (gradientIteration (2/5) n) (by norm_num) (by norm_num)
  rw [gradient_recurrence]
  convert hh using 1 <;> ring

end SafeLearning.CompleteFoundationsQuadraticExercises
