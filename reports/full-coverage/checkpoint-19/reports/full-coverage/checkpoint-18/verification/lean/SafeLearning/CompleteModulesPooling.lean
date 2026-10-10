import SafeLearning.CompleteModulesLipSDPProduct

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace SafeLearning.CompleteModulesPooling
open CompleteModulesLipSDP
variable {I W : Type*} [Fintype I] [Nonempty I]
  [Fintype W]

def actualAverageWindow (input : I → ℝ) : ℝ :=
  (∑ coordinate,input coordinate)/(Fintype.card I : ℝ)

def actualDisjointAveragePool (input : W × I → ℝ) : W → ℝ :=
  fun window => actualAverageWindow (fun coordinate => input (window,coordinate))

def actualMaximumWindow (input : I → ℝ) : ℝ :=
  (Finset.univ.image input).max' (Finset.univ_nonempty.image _)

def actualDisjointMaximumPool (input : W × I → ℝ) : W → ℝ :=
  fun window => actualMaximumWindow (fun coordinate => input (window,coordinate))

theorem actual_average_window_squared_increment_bound (first second : I → ℝ) :
    (actualAverageWindow first-actualAverageWindow second)^2 ≤
      (1/(Fintype.card I : ℝ))*(∑ coordinate,(first coordinate-second coordinate)^2) := by
  have hn : 0 < (Fintype.card I : ℝ) := by exact_mod_cast Fintype.card_pos
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset I)
    (fun _ => (1:ℝ)) (fun coordinate => first coordinate-second coordinate)
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hc
  have he : (actualAverageWindow first-actualAverageWindow second)*(Fintype.card I : ℝ)=
      ∑ coordinate,(first coordinate-second coordinate) := by
    unfold actualAverageWindow
    rw [← sub_div,← Finset.sum_sub_distrib,div_mul_cancel₀ _ hn.ne']
  rw [← he] at hc
  have hb : (actualAverageWindow first-actualAverageWindow second)^2*(Fintype.card I : ℝ) ≤
      ∑ coordinate,(first coordinate-second coordinate)^2 := by
    apply (mul_le_mul_iff_left₀ hn).mp
    nlinarith
  simpa only [one_div,div_eq_mul_inv,mul_comm,mul_one,one_mul] using (le_div_iff₀ hn).mpr hb

theorem actual_disjoint_average_pool_lipschitz (first second : W × I → ℝ) :
    ‖WithLp.toLp 2 (actualDisjointAveragePool first-actualDisjointAveragePool second)‖ ≤
      (1/Real.sqrt (Fintype.card I : ℝ))*‖WithLp.toLp 2 (first-second)‖ := by
  have hn : 0 < (Fintype.card I : ℝ) := by exact_mod_cast Fintype.card_pos
  have hs := Finset.sum_le_sum (fun (window : W) (_ : window ∈ Finset.univ) =>
    actual_average_window_squared_increment_bound
      (fun coordinate => first (window,coordinate)) (fun coordinate => second (window,coordinate)))
  simp only [← Finset.mul_sum] at hs
  have he : (∑ window : W,∑ coordinate : I,(first (window,coordinate)-second (window,coordinate))^2)=
      ∑ pair : W × I,(first pair-second pair)^2 := by rw [Fintype.sum_prod_type]
  rw [he] at hs
  change (∑ window : W,((actualDisjointAveragePool first-actualDisjointAveragePool second) window)^2) ≤ _ at hs
  rw [← squared_norm_of_coordinates,← squared_norm_of_coordinates] at hs
  change ‖WithLp.toLp 2 (actualDisjointAveragePool first-actualDisjointAveragePool second)‖^2 ≤
    (1/(Fintype.card I : ℝ))*‖WithLp.toLp 2 (first-second)‖^2 at hs
  have hg : (1/Real.sqrt (Fintype.card I : ℝ))^2=1/(Fintype.card I : ℝ) := by
    rw [div_pow,one_pow,Real.sq_sqrt hn.le]
  nlinarith [norm_nonneg (WithLp.toLp 2 (actualDisjointAveragePool first-actualDisjointAveragePool second)),
    norm_nonneg (WithLp.toLp 2 (first-second)),
    mul_nonneg (show 0 ≤ 1/Real.sqrt (Fintype.card I : ℝ) by positivity)
      (norm_nonneg (WithLp.toLp 2 (first-second)))]

theorem actual_average_row_euclidean_norm :
    ‖WithLp.toLp 2 (fun _ : I => 1/(Fintype.card I : ℝ))‖=
      1/Real.sqrt (Fintype.card I : ℝ) := by
  have hn : 0 < (Fintype.card I : ℝ) := by exact_mod_cast Fintype.card_pos
  have he : ‖WithLp.toLp 2 (fun _ : I => 1/(Fintype.card I : ℝ))‖^2=1/(Fintype.card I : ℝ) := by
    rw [squared_norm_of_coordinates]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    field_simp
  have hg : (1/Real.sqrt (Fintype.card I : ℝ))^2=1/(Fintype.card I : ℝ) := by
    rw [div_pow,one_pow,Real.sq_sqrt hn.le]
  nlinarith [norm_nonneg (WithLp.toLp 2 (fun _ : I => 1/(Fintype.card I : ℝ))),
    (show 0 ≤ 1/Real.sqrt (Fintype.card I : ℝ) by positivity)]

theorem actual_maximum_window_squared_increment_bound (first second : I → ℝ) :
    (actualMaximumWindow first-actualMaximumWindow second)^2 ≤
      ∑ coordinate,(first coordinate-second coordinate)^2 := by
  have hcoord (coordinate : I) : |first coordinate-second coordinate| ≤
      ‖WithLp.toLp 2 (first-second)‖ := by
    simpa only [Real.norm_eq_abs,WithLp.ofLp_toLp,Pi.sub_apply] using
      (PiLp.norm_apply_le (WithLp.toLp 2 (first-second)) coordinate)
  have hupper : actualMaximumWindow first-actualMaximumWindow second ≤
      ‖WithLp.toLp 2 (first-second)‖ := by
    obtain ⟨coordinate,_,he⟩ := Finset.mem_image.mp
      (Finset.max'_mem (Finset.univ.image first) (Finset.univ_nonempty.image _))
    have hb : second coordinate ≤ actualMaximumWindow second :=
      Finset.le_max' _ _ (Finset.mem_image.mpr ⟨coordinate,Finset.mem_univ _,rfl⟩)
    have ha := le_abs_self (first coordinate-second coordinate)
    unfold actualMaximumWindow at hb ⊢
    rw [← he]
    linarith [hcoord coordinate]
  have hlower : -(actualMaximumWindow first-actualMaximumWindow second) ≤
      ‖WithLp.toLp 2 (first-second)‖ := by
    obtain ⟨coordinate,_,he⟩ := Finset.mem_image.mp
      (Finset.max'_mem (Finset.univ.image second) (Finset.univ_nonempty.image _))
    have hb : first coordinate ≤ actualMaximumWindow first :=
      Finset.le_max' _ _ (Finset.mem_image.mpr ⟨coordinate,Finset.mem_univ _,rfl⟩)
    have ha := neg_le_abs (first coordinate-second coordinate)
    unfold actualMaximumWindow at hb ⊢
    rw [← he]
    linarith [hcoord coordinate]
  have ha := abs_le.mpr ⟨by linarith, hupper⟩
  have hs : (actualMaximumWindow first-actualMaximumWindow second)^2 ≤
      ‖WithLp.toLp 2 (first-second)‖^2 := by
    nlinarith [sq_abs (actualMaximumWindow first-actualMaximumWindow second),abs_nonneg (actualMaximumWindow first-actualMaximumWindow second),
      norm_nonneg (WithLp.toLp 2 (first-second))]
  simpa only [squared_norm_of_coordinates,Pi.sub_apply] using hs

theorem actual_maximum_window_lipschitz (first second : I → ℝ) :
    |actualMaximumWindow first-actualMaximumWindow second| ≤
      ‖WithLp.toLp 2 (first-second)‖ := by
  have hs := actual_maximum_window_squared_increment_bound first second
  rw [← squared_norm_of_coordinates] at hs
  change (actualMaximumWindow first-actualMaximumWindow second)^2 ≤ ‖WithLp.toLp 2 (first-second)‖^2 at hs
  nlinarith [sq_abs (actualMaximumWindow first-actualMaximumWindow second),
    abs_nonneg (actualMaximumWindow first-actualMaximumWindow second),
    norm_nonneg (WithLp.toLp 2 (first-second))]

theorem actual_disjoint_maximum_pool_nonexpansive (first second : W × I → ℝ) :
    ‖WithLp.toLp 2 (actualDisjointMaximumPool first-actualDisjointMaximumPool second)‖ ≤
      ‖WithLp.toLp 2 (first-second)‖ := by
  have hs := Finset.sum_le_sum (fun (window : W) (_ : window ∈ Finset.univ) =>
    actual_maximum_window_squared_increment_bound
      (fun coordinate => first (window,coordinate)) (fun coordinate => second (window,coordinate)))
  have he : (∑ window : W,∑ coordinate : I,(first (window,coordinate)-second (window,coordinate))^2)=
      ∑ pair : W × I,(first pair-second pair)^2 := by rw [Fintype.sum_prod_type]
  rw [he] at hs
  change (∑ window : W,((actualDisjointMaximumPool first-actualDisjointMaximumPool second) window)^2) ≤ _ at hs
  rw [← squared_norm_of_coordinates,← squared_norm_of_coordinates] at hs
  change ‖WithLp.toLp 2 (actualDisjointMaximumPool first-actualDisjointMaximumPool second)‖^2 ≤
    ‖WithLp.toLp 2 (first-second)‖^2 at hs
  nlinarith [norm_nonneg (WithLp.toLp 2 (actualDisjointMaximumPool first-actualDisjointMaximumPool second)),
    norm_nonneg (WithLp.toLp 2 (first-second))]

end SafeLearning.CompleteModulesPooling
