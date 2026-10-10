import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Matrix
open scoped BigOperators Topology
namespace SafeLearning.CompleteAppliedTinyNetwork

abbrev E := EuclideanSpace ℝ (Fin 2)
def point (a b : ℝ) : E := WithLp.toLp 2 ![a,b]
def firstWeight : Matrix (Fin 2) (Fin 2) ℝ := !![1,1;1,-1]
def firstBias : Fin 2 → ℝ := ![-1,0]
def secondWeight : Fin 2 → ℝ := ![1,-2]
def preactivation (x : E) : Fin 2 → ℝ := firstWeight*ᵥ(x:Fin 2→ℝ)+firstBias
def hidden (x : E) : Fin 2 → ℝ := fun i=>max (preactivation x i) 0
def network (x : E) : ℝ := secondWeight ⬝ᵥ hidden x-1

theorem actual_network_is_the_literal_two_two_one_ReLU_composition (x : E) :
    preactivation x=![x 0+x 1-1,x 0-x 1] ∧
    network x=max (x 0+x 1-1) 0-2*max (x 0-x 1) 0-1 := by
  constructor
  · ext i;fin_cases i <;> simp [preactivation,firstWeight,firstBias,dotProduct,Fin.sum_univ_two,sub_eq_add_neg]
  · simp [network,hidden,preactivation,firstWeight,firstBias,secondWeight,dotProduct,Fin.sum_univ_two,sub_eq_add_neg]

theorem actual_input_displacement_is_the_ordinary_Euclidean_norm (x y : E) :
    ‖x-y‖^2=(x 0-y 0)^2+(x 1-y 1)^2 := by
  simpa [Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq (x-y)

theorem actual_relu_increment_square_is_bounded_by_the_input_increment_square (u v : ℝ) :
    (max u 0-max v 0)^2≤(u-v)^2 := by
  by_cases hu : 0≤u <;> by_cases hv : 0≤v
  · simp [max_eq_left hu,max_eq_left hv]
  · rw [max_eq_left hu,max_eq_right (le_of_not_ge hv)]
    nlinarith [sq_nonneg v]
  · rw [max_eq_right (le_of_not_ge hu),max_eq_left hv]
    nlinarith [sq_nonneg u]
  · rw [max_eq_right (le_of_not_ge hu),max_eq_right (le_of_not_ge hv)]
    norm_num
    positivity

theorem actual_network_global_Euclidean_gain_is_at_most_sqrt_ten (x y : E) :
    |network x-network y|≤Real.sqrt 10*‖x-y‖ := by
  have h1 := actual_relu_increment_square_is_bounded_by_the_input_increment_square
    (x 0+x 1-1) (y 0+y 1-1)
  have h2 := actual_relu_increment_square_is_bounded_by_the_input_increment_square
    (x 0-x 1) (y 0-y 1)
  let d1 := max (x 0+x 1-1) 0-max (y 0+y 1-1) 0
  let d2 := max (x 0-x 1) 0-max (y 0-y 1) 0
  have hd : network x-network y=d1-2*d2 := by
    rw [(actual_network_is_the_literal_two_two_one_ReLU_composition x).2,
      (actual_network_is_the_literal_two_two_one_ReLU_composition y).2]
    dsimp [d1,d2];ring
  have hb : (d1-2*d2)^2≤10*‖x-y‖^2 := by
    rw [actual_input_displacement_is_the_ordinary_Euclidean_norm]
    dsimp [d1,d2] at *
    nlinarith [sq_nonneg (2*d1+d2)]
  have hs : (Real.sqrt 10)^2=10 := Real.sq_sqrt (by norm_num)
  rw [hd]
  apply abs_le_of_sq_le_sq _ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
  rw [mul_pow,hs]
  exact hb

theorem actual_question_input_hidden_vector_output_and_margin :
    preactivation (point (-2) 0)=![-3,-2] ∧
    hidden (point (-2) 0)=![0,0] ∧ network (point (-2) 0)=-1 ∧
    |network (point (-2) 0)|=1 := by
  refine ⟨?_,?_,?_,?_⟩
  · ext i;fin_cases i <;> norm_num [preactivation,firstWeight,firstBias,point,dotProduct,Fin.sum_univ_two]
  · ext i;fin_cases i <;> norm_num [hidden,preactivation,firstWeight,firstBias,point,dotProduct,Fin.sum_univ_two]
  · norm_num [network,hidden,preactivation,firstWeight,firstBias,secondWeight,point,dotProduct,Fin.sum_univ_two]
  · norm_num [network,hidden,preactivation,firstWeight,firstBias,secondWeight,point,dotProduct,Fin.sum_univ_two]

theorem actual_global_radius_certifies_every_strictly_inside_perturbation (x : E)
    (hx : ‖x-point (-2) 0‖<1/Real.sqrt 10) : network x<0 := by
  have hs : (0:ℝ)<Real.sqrt 10 := Real.sqrt_pos.mpr (by norm_num)
  have hdist : Real.sqrt 10*‖x-point (-2) 0‖<1 := by
    have h := (lt_div_iff₀ hs).mp hx
    nlinarith
  have h := actual_network_global_Euclidean_gain_is_at_most_sqrt_ten x (point (-2) 0)
  rw [actual_question_input_hidden_vector_output_and_margin.2.2.1] at h
  have hu := (abs_le.mp h).2
  linarith

theorem actual_zero_boundary_has_exactly_the_two_literal_branches (x : E) :
    network x=0 ↔
      ((x 0+x 1=2 ∧ x 0≤x 1) ∨ (-x 0+3*x 1=2 ∧ x 1≤x 0)) := by
  rw [(actual_network_is_the_literal_two_two_one_ReLU_composition x).2]
  by_cases h1 : 0≤x 0+x 1-1
  · rw [max_eq_left h1]
    by_cases h2 : 0≤x 0-x 1
    · rw [max_eq_left h2]
      constructor
      · intro h;right;constructor <;> linarith
      · rintro (⟨h,hx⟩|⟨h,hx⟩) <;> linarith
    · rw [max_eq_right (le_of_not_ge h2)]
      constructor
      · intro h;left;constructor <;> linarith
      · rintro (⟨h,hx⟩|⟨h,hx⟩) <;> linarith
  · rw [max_eq_right (le_of_not_ge h1)]
    by_cases h2 : 0≤x 0-x 1
    · rw [max_eq_left h2]
      constructor
      · intro h;exfalso;linarith
      · rintro (⟨h,hx⟩|⟨h,hx⟩) <;> linarith
    · rw [max_eq_right (le_of_not_ge h2)]
      constructor
      · intro h;exfalso;linarith
      · rintro (⟨h,hx⟩|⟨h,hx⟩) <;> linarith

end SafeLearning.CompleteAppliedTinyNetwork
