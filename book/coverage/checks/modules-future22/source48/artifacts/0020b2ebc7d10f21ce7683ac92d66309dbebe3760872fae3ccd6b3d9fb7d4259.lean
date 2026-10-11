import SafeLearning.CompleteModulesEllipsoidRow

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
open Matrix Set
open scoped BigOperators
open SafeLearning.CompleteModulesEllipsoidRow

namespace SafeLearning.CompleteModulesNNGeometryPractices22

def storage : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![4,1]
def row : Fin 2 → ℝ := ![2,1]
def energy (x : Fin 2 → ℝ) : ℝ := x ⬝ᵥ (storage *ᵥ x)
def output (x : Fin 2 → ℝ) : ℝ := row ⬝ᵥ x
def ellipsoid : Set (Fin 2 → ℝ) := {x | energy x ≤ 1}
def attainer : Fin 2 → ℝ := ![1/(2*Real.sqrt 2),1/Real.sqrt 2]

theorem actual_storage_positive_and_actual_inverse :
    storage.PosDef ∧ storage⁻¹=Matrix.diagonal ![1/4,1] := by
  constructor
  · rw [storage,Matrix.posDef_diagonal_iff]
    intro i
    fin_cases i <;> norm_num
  · apply Matrix.inv_eq_right_inv
    rw [storage,Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.one_apply]

theorem actual_source_quadratic_output_and_inverse_metric (x : Fin 2 → ℝ) :
    energy x=4*(x 0)^2+(x 1)^2 ∧ output x=2*x 0+x 1 ∧
      actualRowEnergy storage row=2 := by
  have hi := actual_storage_positive_and_actual_inverse.2
  refine ⟨?_,?_,?_⟩
  · simp [energy,storage,Matrix.mulVec,dotProduct,Fin.sum_univ_two]; ring
  · simp [output,row,dotProduct,Fin.sum_univ_two]
  · rw [actualRowEnergy,hi]
    norm_num [row,Matrix.mulVec,dotProduct,Fin.sum_univ_two]

theorem actual_source_axis_sections (t : ℝ) :
    (![t,0] : Fin 2 → ℝ) ∈ ellipsoid ↔ |t| ≤ 1/2 := by
  rw [Set.mem_setOf_eq,(actual_source_quadratic_output_and_inverse_metric _).1]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,zero_pow,
    mul_zero,add_zero]
  constructor
  · intro h
    nlinarith [sq_abs t,abs_nonneg t]
  · intro h
    nlinarith [sq_abs t,abs_nonneg t]

theorem actual_source_second_axis_section (t : ℝ) :
    (![0,t] : Fin 2 → ℝ) ∈ ellipsoid ↔ |t| ≤ 1 := by
  rw [Set.mem_setOf_eq,(actual_source_quadratic_output_and_inverse_metric _).1]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,zero_pow,
    mul_zero,zero_add]
  constructor
  · intro h; nlinarith [sq_abs t,abs_nonneg t]
  · intro h; nlinarith [sq_abs t,abs_nonneg t]

theorem actual_every_point_has_the_sharp_sqrt_two_bound (x : Fin 2 → ℝ)
    (hx : x ∈ ellipsoid) : |output x| ≤ Real.sqrt 2 := by
  have h := (actual_row_interval_containment_iff_the_exact_inverse_metric_bound
    storage actual_storage_positive_and_actual_inverse.1 row (Real.sqrt 2)
    (Real.sqrt_nonneg _)).2
  have hb : actualRowEnergy storage row ≤ (Real.sqrt 2)^2 := by
    rw [(actual_source_quadratic_output_and_inverse_metric x).2.2,
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  exact h hb x hx

theorem actual_printed_attainer_is_the_inverse_metric_direction :
    attainer=actualRowAttainer storage row := by
  rw [actualRowAttainer,(actual_source_quadratic_output_and_inverse_metric attainer).2.2,
    actual_storage_positive_and_actual_inverse.2]
  ext i
  fin_cases i <;> norm_num [attainer,row,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  all_goals ring

theorem actual_printed_attainer_has_energy_one_and_output_sqrt_two :
    energy attainer=1 ∧ output attainer=Real.sqrt 2 := by
  have hn : row ≠ 0 := by
    intro h
    have he := congrFun h 0
    norm_num [row] at he
  have h := actual_nonzero_row_attainer_has_energy_one_and_attains_the_support
    storage actual_storage_positive_and_actual_inverse.1 row hn
  rw [← actual_printed_attainer_is_the_inverse_metric_direction,
    (actual_source_quadratic_output_and_inverse_metric attainer).2.2] at h
  exact h

theorem actual_sqrt_two_is_the_attained_maximum_absolute_preactivation :
    IsGreatest (output '' ellipsoid |> fun s => abs '' s) (Real.sqrt 2) := by
  constructor
  · refine ⟨output attainer,⟨attainer,?_,rfl⟩,?_⟩
    · exact actual_printed_attainer_has_energy_one_and_output_sqrt_two.1.le
    · rw [actual_printed_attainer_has_energy_one_and_output_sqrt_two.2,
        abs_of_nonneg (Real.sqrt_nonneg _)]
  · rintro y ⟨v,⟨x,hx,rfl⟩,rfl⟩
    exact actual_every_point_has_the_sharp_sqrt_two_bound x hx

theorem actual_unit_interval_fails_and_every_valid_half_width_is_at_least_sqrt_two :
    output attainer ∉ Icc (-1:ℝ) 1 ∧
      ∀ radius : ℝ, (∀ x ∈ ellipsoid, |output x| ≤ radius) → Real.sqrt 2 ≤ radius := by
  constructor
  · rw [actual_printed_attainer_has_energy_one_and_output_sqrt_two.2]
    have hs : 1 < Real.sqrt (2:ℝ) := by
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),Real.sqrt_nonneg (2:ℝ)]
    exact fun h => (not_le_of_gt hs) h.2
  · intro radius h
    have hb := h attainer actual_printed_attainer_has_energy_one_and_output_sqrt_two.1.le
    simpa only [actual_printed_attainer_has_energy_one_and_output_sqrt_two.2,
      abs_of_nonneg (Real.sqrt_nonneg _)] using hb

def box : Set (Fin 2 → ℝ) := {w | |w 0-1| ≤ 1/5 ∧ |w 1+1| ≤ 1/2}
def affine (w : Fin 2 → ℝ) : ℝ := 2*w 0-3*w 1+1
def upperCorner : Fin 2 → ℝ := ![6/5,-3/2]
def lowerCorner : Fin 2 → ℝ := ![4/5,-1/2]

theorem actual_signed_box_centre_radius_and_every_point_interval
    (w : Fin 2 → ℝ) (hw : w ∈ box) :
    affine (![1,-1])=6 ∧ 2*(1/5:ℝ)+3*(1/2)=19/10 ∧
      affine w ∈ Icc (41/10:ℝ) (79/10) := by
  have h0 := (abs_le.mp hw.1)
  have h1 := (abs_le.mp hw.2)
  refine ⟨by norm_num [affine],by norm_num,?_⟩
  constructor <;> dsimp [affine] <;> linarith

theorem actual_signed_corners_attain_both_interval_endpoints :
    upperCorner ∈ box ∧ affine upperCorner=79/10 ∧
      lowerCorner ∈ box ∧ affine lowerCorner=41/10 := by
  norm_num [box,upperCorner,lowerCorner,affine]

theorem actual_box_endpoints_are_true_greatest_and_least :
    IsGreatest (affine '' box) (79/10) ∧ IsLeast (affine '' box) (41/10) := by
  obtain ⟨hu,huv,hl,hlv⟩ := actual_signed_corners_attain_both_interval_endpoints
  constructor
  · refine ⟨⟨upperCorner,hu,huv⟩,?_⟩
    rintro v ⟨w,hw,rfl⟩
    exact (actual_signed_box_centre_radius_and_every_point_interval w hw).2.2.2
  · refine ⟨⟨lowerCorner,hl,hlv⟩,?_⟩
    rintro v ⟨w,hw,rfl⟩
    exact (actual_signed_box_centre_radius_and_every_point_interval w hw).2.2.1

theorem actual_correlated_subsets_remain_sound_but_can_miss_the_corner
    (hidden : Set (Fin 2 → ℝ)) (hhidden : hidden ⊆ box) :
    (∀ w ∈ hidden, affine w ∈ Icc (41/10:ℝ) (79/10)) ∧
      (![1,-1] : Fin 2 → ℝ) ∈ box ∧
      upperCorner ∉ ({![1,-1]} : Set (Fin 2 → ℝ)) := by
  refine ⟨fun w hw => (actual_signed_box_centre_radius_and_every_point_interval w
    (hhidden hw)).2.2,?_,?_⟩
  · norm_num [box]
  · simp only [Set.mem_singleton_iff]
    intro h
    have he := congrFun h 0
    norm_num [upperCorner] at he

end SafeLearning.CompleteModulesNNGeometryPractices22
