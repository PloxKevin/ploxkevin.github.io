import SafeLearning.CompletePolicyQuadraticDual

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Matrix
namespace SafeLearning.CompletePolicyCPOExample
open SafeLearning.CompletePolicyQuadraticDual

def H : Matrix (Fin 2) (Fin 2) ℝ := !![2,1/2;1/2,1]
def g : Fin 2 → ℝ := ![1,2/5]
def b : Fin 2 → ℝ := ![3/5,4/5]
def c : ℝ := -1/10
def δ : ℝ := 1/20
def root : ℝ := Real.sqrt 985
def lam : ℝ := 56 / root
def nu : ℝ := 18/29 - 35 * lam / 232
def candidate : Fin 2 → ℝ := ![(2 * root + 5) / 290,(65 - 3 * root) / 580]

theorem actual_metric_positive_definite : H.PosDef := by
  have hh : H.IsHermitian := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [H, Matrix.conjTranspose]
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hh
  intro x hx
  have he : star x ⬝ᵥ (H *ᵥ x) = 2 * x 0 ^ 2 + x 0 * x 1 + x 1 ^ 2 := by
    simp [H, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  rw [he]
  by_cases h0 : x 0 = 0
  · have h1 : x 1 ≠ 0 := by
      intro h1
      apply hx
      ext i
      fin_cases i <;> simp [h0,h1]
    have hp := sq_pos_of_ne_zero h1
    simp only [h0,zero_pow (by norm_num : (2 : ℕ) ≠ 0),mul_zero,zero_mul,zero_add]
    exact hp
  · have hp := sq_pos_of_ne_zero h0
    nlinarith [sq_nonneg (x 1 + x 0 / 2)]

theorem actual_exact_metric_inverse : H⁻¹ = !![4/7,-2/7;-2/7,8/7] := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [H, Matrix.mul_apply, Fin.sum_univ_two]

theorem actual_inverse_gradient_and_cost_vectors :
    H⁻¹ *ᵥ g = ![16/35,6/35] ∧ H⁻¹ *ᵥ b = ![4/35,26/35] := by
  constructor <;> rw [actual_exact_metric_inverse] <;> ext i <;> fin_cases i <;>
    norm_num [g,b,Matrix.mulVec,dotProduct,Fin.sum_univ_two]

theorem actual_exact_q_r_s_and_reduced_radicands :
    g ⬝ᵥ (H⁻¹ *ᵥ g) = 92/175 ∧ g ⬝ᵥ (H⁻¹ *ᵥ b) = 72/175 ∧
    b ⬝ᵥ (H⁻¹ *ᵥ b) = 116/175 ∧
    (92 : ℝ)/175 - (72/175)^2 / (116/175) = 196/725 ∧
    (2 : ℝ) * δ - c^2 / (116/175) = 197/2320 ∧
    (196 : ℝ)/725 / (197/2320) = 3136/985 := by
  rw [actual_inverse_gradient_and_cost_vectors.1,actual_inverse_gradient_and_cost_vectors.2]
  norm_num [g,b,c,δ,dotProduct,Fin.sum_univ_two]

theorem actual_root_enclosure : (31.3847 : ℝ) < root ∧ root < 31.3848 ∧ root ^ 2 = 985 := by
  have hs : root ^ 2 = 985 := Real.sq_sqrt (by norm_num)
  have hn : 0 ≤ root := Real.sqrt_nonneg _
  constructor
  · nlinarith
  constructor
  · nlinarith
  · exact hs

theorem actual_multipliers_and_candidate_are_the_actual_inverse_optimizer :
    0 < lam ∧ 0 < nu ∧ optimizer H g b lam nu = candidate := by
  have hp : 0 < root := lt_trans (by norm_num) actual_root_enclosure.1
  have hl : 0 < lam := div_pos (by norm_num) hp
  have hlu : lam < 2 := (div_lt_iff₀ hp).mpr (by nlinarith [actual_root_enclosure.1])
  refine ⟨hl,?_,?_⟩
  · unfold nu
    linarith
  · simp only [optimizer,mulVec_sub,mulVec_smul,actual_inverse_gradient_and_cost_vectors.1,
      actual_inverse_gradient_and_cost_vectors.2]
    ext i
    fin_cases i <;> simp [candidate,nu,lam,Pi.smul_apply] <;>
      field_simp [ne_of_gt hp] <;> ring

theorem actual_candidate_has_both_original_constraints_active :
    c + b ⬝ᵥ candidate = 0 ∧ (candidate ⬝ᵥ (H *ᵥ candidate)) / 2 = δ := by
  have hs := actual_root_enclosure.2.2
  simp [c,b,candidate,H,δ,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  constructor <;> nlinarith

theorem actual_candidate_has_zero_true_primal_dual_gap :
    actualDual H g b c δ (lam,nu) = g ⬝ᵥ candidate := by
  obtain ⟨hl,hn,he⟩ := actual_multipliers_and_candidate_are_the_actual_inverse_optimizer
  rw [actual_true_supremum_equals_closed_dual H actual_metric_positive_definite g b c δ lam nu hl,
    ← actual_attained_closed_dual_value H actual_metric_positive_definite g b c δ lam nu hl, he]
  rw [lagrangian,actual_candidate_has_both_original_constraints_active.1,
    actual_candidate_has_both_original_constraints_active.2]
  ring

theorem actual_candidate_is_globally_primal_optimal (x : Fin 2 → ℝ)
    (hc : c + b ⬝ᵥ x ≤ 0) (ht : (x ⬝ᵥ (H *ᵥ x)) / 2 ≤ δ) :
    g ⬝ᵥ x ≤ g ⬝ᵥ candidate := by
  rw [← actual_candidate_has_zero_true_primal_dual_gap]
  exact actual_weak_duality H actual_metric_positive_definite g b c δ lam nu
    actual_multipliers_and_candidate_are_the_actual_inverse_optimizer.1
    actual_multipliers_and_candidate_are_the_actual_inverse_optimizer.2.1.le x hc ht

theorem actual_candidate_prices_are_globally_dual_optimal (price weight : ℝ)
    (hp : 0 < price) (hw : 0 ≤ weight) :
    actualDual H g b c δ (lam,nu) ≤ actualDual H g b c δ (price,weight) := by
  rw [actual_candidate_has_zero_true_primal_dual_gap]
  exact actual_weak_duality H actual_metric_positive_definite g b c δ price weight hp hw candidate
    actual_candidate_has_both_original_constraints_active.1.le
    actual_candidate_has_both_original_constraints_active.2.le

theorem actual_printed_three_decimal_numbers_are_certified_roundings :
    (1.7835 : ℝ) < lam ∧ lam < 1.7845 ∧ (0.3515 : ℝ) < nu ∧ nu < 0.3525 ∧
    (0.2335 : ℝ) < candidate 0 ∧ candidate 0 < 0.2345 ∧
    (-0.0505 : ℝ) < candidate 1 ∧ candidate 1 < -0.0495 ∧
    (0.2135 : ℝ) < g ⬝ᵥ candidate ∧ g ⬝ᵥ candidate < 0.2145 := by
  obtain ⟨hlo,hhi,hs⟩ := actual_root_enclosure
  have hp : 0 < root := by linarith
  have hl : (1.78430 : ℝ) < lam := (lt_div_iff₀ hp).mpr (by nlinarith)
  have hu : lam < (1.78432 : ℝ) := (div_lt_iff₀ hp).mpr (by nlinarith)
  simp only [candidate,g,dotProduct,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  dsimp [nu]
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

end SafeLearning.CompletePolicyCPOExample
