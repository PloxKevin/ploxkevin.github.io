import SafeLearning.CompleteModulesPooling

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace SafeLearning.CompleteModulesPoolingCorollaries
open CompleteModulesPooling
variable {I : Type*} [Fintype I] [Nonempty I]

theorem actual_average_row_norm_equals_source_sqrt_over_length :
    ‖WithLp.toLp 2 (fun _ : I => 1/(Fintype.card I : ℝ))‖=
      Real.sqrt (Fintype.card I : ℝ)/(Fintype.card I : ℝ) := by
  rw [actual_average_row_euclidean_norm]
  have hn : 0 < (Fintype.card I : ℝ) := by exact_mod_cast Fintype.card_pos
  apply (div_eq_div_iff (Real.sqrt_pos.mpr hn).ne' hn.ne').mpr
  simpa only [one_mul,pow_two] using (Real.sq_sqrt hn.le).symm

theorem actual_maximum_increment_is_bounded_by_maximum_absolute_increment
    (first second : I → ℝ) :
    |actualMaximumWindow first-actualMaximumWindow second| ≤
      actualMaximumWindow (fun coordinate => |first coordinate-second coordinate|) := by
  have hcoord (coordinate : I) : |first coordinate-second coordinate| ≤
      actualMaximumWindow (fun coordinate => |first coordinate-second coordinate|) := by
    unfold actualMaximumWindow
    exact Finset.le_max' (Finset.univ.image (fun coordinate : I => |first coordinate-second coordinate|)) _
      (Finset.mem_image.mpr ⟨coordinate,Finset.mem_univ _,rfl⟩)
  have hupper : actualMaximumWindow first-actualMaximumWindow second ≤
      actualMaximumWindow (fun coordinate => |first coordinate-second coordinate|) := by
    obtain ⟨coordinate,_,he⟩ := Finset.mem_image.mp
      (Finset.max'_mem (Finset.univ.image first) (Finset.univ_nonempty.image _))
    have hb : second coordinate ≤ actualMaximumWindow second :=
      Finset.le_max' _ _ (Finset.mem_image.mpr ⟨coordinate,Finset.mem_univ _,rfl⟩)
    change first coordinate=actualMaximumWindow first at he
    rw [← he]
    linarith [le_abs_self (first coordinate-second coordinate),hcoord coordinate]
  have hlower : -(actualMaximumWindow first-actualMaximumWindow second) ≤
      actualMaximumWindow (fun coordinate => |first coordinate-second coordinate|) := by
    obtain ⟨coordinate,_,he⟩ := Finset.mem_image.mp
      (Finset.max'_mem (Finset.univ.image second) (Finset.univ_nonempty.image _))
    have hb : first coordinate ≤ actualMaximumWindow first :=
      Finset.le_max' _ _ (Finset.mem_image.mpr ⟨coordinate,Finset.mem_univ _,rfl⟩)
    change second coordinate=actualMaximumWindow second at he
    rw [← he]
    linarith [neg_le_abs (first coordinate-second coordinate),hcoord coordinate]
  exact abs_le.mpr ⟨by linarith,hupper⟩

theorem actual_maximum_absolute_increment_is_bounded_by_euclidean_increment
    (first second : I → ℝ) :
    actualMaximumWindow (fun coordinate => |first coordinate-second coordinate|) ≤
      ‖WithLp.toLp 2 (first-second)‖ := by
  unfold actualMaximumWindow
  apply Finset.max'_le
  intro value hvalue
  obtain ⟨coordinate,_,he⟩ := Finset.mem_image.mp hvalue
  rw [← he]
  simpa only [Real.norm_eq_abs,WithLp.ofLp_toLp,Pi.sub_apply] using
    (PiLp.norm_apply_le (WithLp.toLp 2 (first-second)) coordinate)

end SafeLearning.CompleteModulesPoolingCorollaries
