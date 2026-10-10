import SafeLearning.CompleteAppliedTinyNetwork

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators
namespace SafeLearning.CompleteAppliedTinyNetworkGeometry
open SafeLearning.CompleteAppliedTinyNetwork

def boundaryDistances : Set ℝ := {r | ∃x:E,network x=0 ∧ r=‖x-point (-2) 0‖}

theorem actual_question_point_to_literal_nearest_boundary_squared_distance :
    network (point 0 2)=0 ∧ ‖point 0 2-point (-2) 0‖^2=8 := by
  constructor
  · rw [(actual_network_is_the_literal_two_two_one_ReLU_composition (point 0 2)).2]
    norm_num [point]
  · rw [actual_input_displacement_is_the_ordinary_Euclidean_norm]
    norm_num [point]

theorem actual_every_first_branch_boundary_distance_has_lower_bound_and_unique_attainer
    (x : E) (he : x 0+x 1=2) :
    8≤‖x-point (-2) 0‖^2 ∧
    (‖x-point (-2) 0‖^2=8 ↔ x=point 0 2) := by
  rw [actual_input_displacement_is_the_ordinary_Euclidean_norm]
  simp only [point,Matrix.cons_val_zero,Matrix.cons_val_one]
  constructor
  · nlinarith [sq_nonneg (x 0+2-x 1)]
  · constructor
    · intro h
      have hx : x 0=0 := by nlinarith [sq_nonneg (x 0)]
      have hy : x 1=2 := by linarith
      ext i
      fin_cases i <;> simp [hx,hy]
    · intro h
      rw [h]
      norm_num [point]

theorem actual_other_boundary_branch_is_farther (x : E)
    (he : -x 0+3*x 1=2) (hh : x 1≤x 0) :
    10≤‖x-point (-2) 0‖^2 := by
  rw [actual_input_displacement_is_the_ordinary_Euclidean_norm]
  simp only [point,Matrix.cons_val_zero,Matrix.cons_val_one]
  have hy : 1≤x 1 := by linarith
  nlinarith [sq_nonneg (x 1-1)]

theorem actual_nearest_boundary_distance_is_a_true_attained_minimum :
    IsLeast boundaryDistances (2*Real.sqrt 2) := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn := Real.sqrt_nonneg (2:ℝ)
  have hat := actual_question_point_to_literal_nearest_boundary_squared_distance
  have hdist : ‖point 0 2-point (-2) 0‖=2*Real.sqrt 2 := by nlinarith [norm_nonneg (point 0 2-point (-2) 0)]
  refine ⟨⟨point 0 2,hat.1,hdist.symm⟩,?_⟩
  rintro r ⟨x,hx,rfl⟩
  have hl : 8≤‖x-point (-2) 0‖^2 := by
    rcases (actual_zero_boundary_has_exactly_the_two_literal_branches x).mp hx with h|h
    · exact (actual_every_first_branch_boundary_distance_has_lower_bound_and_unique_attainer x h.1).1
    · have hfar := actual_other_boundary_branch_is_farther x h.1 h.2
      linarith
  nlinarith [norm_nonneg (x-point (-2) 0)]

theorem actual_box_interval_bounds_propagate_to_both_off_neurons (x : E)
    (hx : (-3:ℝ)≤x 0 ∧ x 0≤-1) (hy : (-1:ℝ)≤x 1 ∧ x 1≤1) :
    ((-5:ℝ)≤preactivation x 0 ∧ preactivation x 0≤-1) ∧
    ((-4:ℝ)≤preactivation x 1 ∧ preactivation x 1≤0) ∧
    hidden x=![0,0] ∧ network x=-1 := by
  have he := (actual_network_is_the_literal_two_two_one_ReLU_composition x).1
  have hp0 : preactivation x 0=x 0+x 1-1 := by rw [he];simp
  have hp1 : preactivation x 1=x 0-x 1 := by rw [he];simp
  have h0 : preactivation x 0≤0 := by rw [hp0];linarith
  have h1 : preactivation x 1≤0 := by rw [hp1];linarith
  refine ⟨⟨?_,?_⟩,⟨?_,h1⟩,?_,?_⟩
  · rw [hp0];linarith
  · rw [hp0];linarith
  · rw [hp1];linarith
  · ext i;fin_cases i <;> simp [CompleteAppliedTinyNetwork.hidden,max_eq_right h0,max_eq_right h1]
  · simp [network,CompleteAppliedTinyNetwork.hidden,secondWeight,Fin.sum_univ_two,dotProduct,max_eq_right h0,max_eq_right h1]

theorem actual_closed_unit_Euclidean_ball_is_in_that_box_and_negative (x : E)
    (hx : ‖x-point (-2) 0‖≤1) :
    ((-3:ℝ)≤x 0 ∧ x 0≤-1) ∧ ((-1:ℝ)≤x 1 ∧ x 1≤1) ∧ network x=-1 := by
  have hs := actual_input_displacement_is_the_ordinary_Euclidean_norm x (point (-2) 0)
  have hn := norm_nonneg (x-point (-2) 0)
  have hb : (x 0+2)^2+(x 1)^2≤1 := by
    simp only [point,Matrix.cons_val_zero,Matrix.cons_val_one,sub_neg_eq_add,sub_zero] at hs
    change ‖x-point (-2) 0‖^2=(x 0+2)^2+(x 1)^2 at hs
    have hnorm : ‖x-point (-2) 0‖^2≤1 := by nlinarith
    linarith
  have h0 : |x 0+2|≤1 := abs_le_of_sq_le_sq (by nlinarith [sq_nonneg (x 1)]) (by norm_num)
  have h1 : |x 1|≤1 := abs_le_of_sq_le_sq (by nlinarith [sq_nonneg (x 0+2)]) (by norm_num)
  have xb : (-3:ℝ)≤x 0 ∧ x 0≤-1 := by rw [abs_le] at h0;constructor <;> linarith [h0.1,h0.2]
  have yb : (-1:ℝ)≤x 1 ∧ x 1≤1 := abs_le.mp h1
  exact ⟨xb,yb,(actual_box_interval_bounds_propagate_to_both_off_neurons x xb yb).2.2.2⟩

theorem actual_pixel_normalization_doubles_distances_and_composite_gain (x y : E) :
    ‖(2:ℝ)•x-(2:ℝ)•y‖=2*‖x-y‖ ∧
    |network ((2:ℝ)•x)-network ((2:ℝ)•y)|≤(2*Real.sqrt 10)*‖x-y‖ := by
  have he : (2:ℝ)•x-(2:ℝ)•y=(2:ℝ)•(x-y) := by rw [smul_sub]
  have hn : ‖(2:ℝ)•x-(2:ℝ)•y‖=2*‖x-y‖ := by rw [he,norm_smul];norm_num
  refine ⟨hn,?_⟩
  have h := actual_network_global_Euclidean_gain_is_at_most_sqrt_ten ((2:ℝ)•x) ((2:ℝ)•y)
  rw [hn] at h
  nlinarith

end SafeLearning.CompleteAppliedTinyNetworkGeometry
