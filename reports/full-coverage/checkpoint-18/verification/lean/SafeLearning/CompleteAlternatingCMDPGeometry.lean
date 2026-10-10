import Mathlib
import SafeLearning.CompleteAlternatingCMDP

set_option autoImplicit false
noncomputable section
open Set Matrix

namespace SafeLearning.CompleteAlternatingCMDPGeometry
open SafeLearning.CompleteAlternatingCMDP

theorem actual_binary_linear_maximum (c p : ℝ) (hp : p ∈ Icc 0 1) :
    c * p ≤ max 0 c := by
  by_cases hc : 0 ≤ c
  · rw [max_eq_right hc]
    nlinarith [hp.2]
  · rw [max_eq_left (le_of_not_ge hc)]
    exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hc) hp.1

def greedy (c : ℝ) : ℝ := if 0 ≤ c then 1 else 0

theorem actual_binary_maximum_attainment (c : ℝ) :
    greedy c ∈ Icc 0 1 ∧ c * greedy c = max 0 c := by
  by_cases h : 0 ≤ c
  · simp [greedy, h]
  · simp [greedy, h, max_eq_left (le_of_not_ge h)]

theorem genuine_policy_lagrangian_bound (p1 p2 price : ℝ)
    (h1 : p1 ∈ Icc 0 1) (h2 : p2 ∈ Icc 0 1) :
    lagrangian p1 p2 price ≤ dual price := by
  rw [actual_lagrangian_decomposition]
  unfold dual
  have h := actual_binary_linear_maximum (1 - price) p1 h1
  have hh := actual_binary_linear_maximum (1 - 2 * price) p2 h2
  nlinarith

theorem genuine_policy_dual_attainer (price : ℝ) :
    lagrangian (greedy (1 - price)) (greedy (1 - 2 * price)) price = dual price := by
  rw [actual_lagrangian_decomposition]
  unfold dual
  have h := (actual_binary_maximum_attainment (1 - price)).2
  have hh := (actual_binary_maximum_attainment (1 - 2 * price)).2
  nlinarith

theorem genuine_policy_dual_supremum (price : ℝ) :
    sSup {v : ℝ | ∃ p1 ∈ Icc (0 : ℝ) 1, ∃ p2 ∈ Icc (0 : ℝ) 1,
      lagrangian p1 p2 price = v} = dual price := by
  have hm : dual price ∈ {v : ℝ | ∃ p1 ∈ Icc (0 : ℝ) 1,
      ∃ p2 ∈ Icc (0 : ℝ) 1, lagrangian p1 p2 price = v} :=
    ⟨_, (actual_binary_maximum_attainment _).1, _,
      (actual_binary_maximum_attainment _).1, genuine_policy_dual_attainer price⟩
  have hb : ∀ v ∈ {v : ℝ | ∃ p1 ∈ Icc (0 : ℝ) 1,
      ∃ p2 ∈ Icc (0 : ℝ) 1, lagrangian p1 p2 price = v}, v ≤ dual price := by
    rintro v ⟨p1, h1, p2, h2, rfl⟩
    exact genuine_policy_lagrangian_bound p1 p2 price h1 h2
  exact le_antisymm (csSup_le ⟨_, hm⟩ hb) (le_csSup ⟨_, hb⟩ hm)

theorem actual_dual_prices_and_indifference :
    dual 1 = reward (9 / 10) 0 ∧
      1 - (1 : ℝ) = 0 ∧ 1 - 2 * (1 : ℝ) < 0 ∧
      (∀ p ∈ Icc (0 : ℝ) 1, lagrangian p 0 1 = 6 / 5) := by
  norm_num [dual, reward, lagrangian, cost]

theorem genuine_dual_slopes :
    StrictAntiOn dual (Icc (0 : ℝ) (1 / 2)) ∧
      StrictAntiOn dual (Icc (1 / 2 : ℝ) 1) ∧
      StrictMonoOn dual (Ici (1 : ℝ)) := by
  constructor
  · intro a ha b hb hab
    rw [(actual_dual_piecewise a).1 ha.2, (actual_dual_piecewise b).1 hb.2]
    linarith
  constructor
  · intro a ha b hb hab
    rw [(actual_dual_piecewise a).2.1 ha, (actual_dual_piecewise b).2.1 hb]
    linarith
  · intro a ha b hb hab
    rw [(actual_dual_piecewise a).2.2 ha, (actual_dual_piecewise b).2.2 hb]
    linarith

def flowBudgetMatrix : Matrix (Fin 3) (Fin 4) ℝ :=
  !![1, 1, -(1 / 2), -(1 / 2); -(1 / 2), -(1 / 2), 1, 1; 2, 0, 4, 0]
def weights (p1 p2 : ℝ) : Fin 4 → ℝ :=
  ![(2 / 3) * p1, (2 / 3) * (1 - p1), (1 / 3) * p2, (1 / 3) * (1 - p2)]
def support (x : Fin 4 → ℝ) : Finset (Fin 4) := Finset.univ.filter (fun j => x j ≠ 0)
def basic (x : Fin 4 → ℝ) : Prop :=
  LinearIndependent ℝ (fun j : support x => flowBudgetMatrix.col j)

theorem actual_occupancy_LP_constraint_matrix (p1 p2 : ℝ) :
    flowBudgetMatrix *ᵥ weights p1 p2 = ![1 / 2, 0, cost p1 p2] := by
  ext i
  fin_cases i <;> simp [flowBudgetMatrix, weights, mulVec, dotProduct,
    Fin.sum_univ_succ, cost] <;> ring

theorem genuine_basic_support_bound (x : Fin 4 → ℝ) (hx : basic x) :
    (support x).card ≤ 3 := by
  have h := hx.fintype_card_le_finrank
  simpa [Module.finrank_pi] using h

theorem genuine_two_state_randomization_bound (p1 p2 : ℝ)
    (hb : basic (weights p1 p2)) :
    ¬(p1 ∈ Ioo (0 : ℝ) 1 ∧ p2 ∈ Ioo (0 : ℝ) 1) := by
  rintro ⟨h1, h2⟩
  have hu : support (weights p1 p2) = Finset.univ := by
    ext i
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
    fin_cases i <;> simp [weights] <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
  have h := genuine_basic_support_bound _ hb
  rw [hu] at h
  norm_num at h

theorem actual_optimal_support_and_randomization :
    weights (9 / 10) 0 = ![3 / 5, 1 / 15, 0, 1 / 3] ∧
      support (weights (9 / 10) 0) = {0, 1, 3} ∧
      (9 / 10 : ℝ) ∈ Ioo 0 1 ∧ (0 : ℝ) ∉ Ioo 0 1 := by
  constructor
  · ext i
    fin_cases i <;> norm_num [weights]
  constructor
  · ext i
    fin_cases i <;> norm_num [support, weights]
  norm_num

def basisColumns : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 1, -(1 / 2); -(1 / 2), -(1 / 2), 1; 2, 0, 0]

theorem actual_basic_column_certificate :
    basisColumns.det = 3 / 2 ∧ LinearIndependent ℝ basisColumns.col ∧
      ∀ j : Fin 3, basisColumns.col j = flowBudgetMatrix.col (![0, 1, 3] j) := by
  have hd : basisColumns.det = 3 / 2 := by norm_num [basisColumns, det_fin_three]
  refine ⟨hd, linearIndependent_cols_of_det_ne_zero (by rw [hd]; norm_num), ?_⟩
  intro j
  ext i
  fin_cases j <;> fin_cases i <;> norm_num [basisColumns, flowBudgetMatrix, col]

theorem genuine_source_edge_objective_changes :
    (![4 / 3, 2 / 3] : Fin 2 → ℝ) ⬝ᵥ ![1, 0] = 4 / 3 ∧
      (![4 / 3, 2 / 3] : Fin 2 → ℝ) ⬝ᵥ ![0, 1] = 2 / 3 ∧
      (![4 / 3, 2 / 3] : Fin 2 → ℝ) ⬝ᵥ ![1, -1] = 2 / 3 := by
  norm_num [dotProduct, Fin.sum_univ_two]

theorem genuine_optimal_occupancy_is_basic : basic (weights (9 / 10) 0) := by
  let index : support (weights (9 / 10) 0) → Fin 3 :=
    fun j => if j.val = 0 then 0 else if j.val = 1 then 1 else 2
  have hm : ∀ j : support (weights (9 / 10) 0),
      (![0, 1, 3] : Fin 3 → Fin 4) (index j) = j.val := by
    intro j
    have hj := j.property
    have hj' : j.val ∈ ({0, 1, 3} : Finset (Fin 4)) := by
      simpa only [actual_optimal_support_and_randomization.2.1] using hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj'
    rcases hj' with h | h | h <;> simp [index, h]
  have hi : Function.Injective index := by
    intro j k h
    apply Subtype.ext
    rw [← hm j, ← hm k, h]
  have hl := actual_basic_column_certificate.2.1.comp index hi
  unfold basic
  convert hl using 1
  funext j
  change flowBudgetMatrix.col j.val = basisColumns.col (index j)
  rw [actual_basic_column_certificate.2.2, hm j]

end SafeLearning.CompleteAlternatingCMDPGeometry
