import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SafeLearning.CompleteFoundationsConvexSets
open Set
open scoped BigOperators
abbrev E := EuclideanSpace ℝ (Fin 2)
def sourceInterval : Set ℝ := Icc (-1) 2
def sourceTwoPoints : Set ℝ := {-1,1}
def sourceDisc : Set E := {u | u 0^2+u 1^2≤1}

theorem actual_interval_combination (a b theta : ℝ)
    (ha : a∈sourceInterval) (hb : b∈sourceInterval) (ht : theta∈Icc (0:ℝ) 1) :
    theta*a+(1-theta)*b∈sourceInterval := by
  rcases ha with ⟨hal,hau⟩
  rcases hb with ⟨hbl,hbu⟩
  rcases ht with ⟨htl,htu⟩
  constructor
  · have h1 := mul_nonneg htl (by linarith : 0≤a+1)
    have h2 := mul_nonneg (by linarith : 0≤1-theta) (by linarith : 0≤b+1)
    nlinarith
  · have h1 := mul_nonneg htl (by linarith : 0≤2-a)
    have h2 := mul_nonneg (by linarith : 0≤1-theta) (by linarith : 0≤2-b)
    nlinarith

theorem actual_source_interval_convex : Convex ℝ sourceInterval := convex_Icc _ _

theorem actual_failed_midpoint :
    (-1:ℝ)∈sourceTwoPoints ∧ (1:ℝ)∈sourceTwoPoints ∧
    (1/2:ℝ)*(-1)+(1/2)*1=0 ∧ (0:ℝ)∉sourceTwoPoints := by
  norm_num [sourceTwoPoints]

theorem actual_source_two_points_not_convex : ¬Convex ℝ sourceTwoPoints := by
  intro hc
  have h := hc actual_failed_midpoint.1 actual_failed_midpoint.2.1
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)+1/2=1)
  norm_num [sourceTwoPoints] at h

theorem actual_euclidean_two_coordinate_norm_squared (u : E) : ‖u‖^2=u 0^2+u 1^2 := by
  simpa [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq u

theorem actual_disc_is_actual_euclidean_unit_ball :
    sourceDisc={u : E | ‖u‖≤1} := by
  ext u
  simp only [sourceDisc,mem_setOf_eq]
  rw [←actual_euclidean_two_coordinate_norm_squared]
  constructor <;> intro h <;> nlinarith [norm_nonneg u]

theorem actual_generic_norm_combination {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (u v : V) (theta : ℝ) (ht : theta∈Icc (0:ℝ) 1) :
    ‖theta • u+(1-theta) • v‖≤theta*‖u‖+(1-theta)*‖v‖ := by
  have h := norm_add_le (theta • u) ((1-theta) • v)
  simpa [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1,
    abs_of_nonneg (by linarith [ht.2] : 0≤1-theta)] using h

theorem actual_disc_combination (u v : E) (hu : u∈sourceDisc) (hv : v∈sourceDisc)
    (theta : ℝ) (ht : theta∈Icc (0:ℝ) 1) :
    ‖theta • u+(1-theta) • v‖≤theta*‖u‖+(1-theta)*‖v‖ ∧
    theta*‖u‖+(1-theta)*‖v‖≤1 ∧ theta • u+(1-theta) • v∈sourceDisc := by
  rw [actual_disc_is_actual_euclidean_unit_ball] at hu hv ⊢
  have h1 := actual_generic_norm_combination u v theta ht
  have h2 : theta*‖u‖+(1-theta)*‖v‖≤1 := by
    have h3 := mul_le_mul_of_nonneg_left hu ht.1
    have h4 := mul_le_mul_of_nonneg_left hv (by linarith [ht.2] : 0≤1-theta)
    nlinarith
  exact ⟨h1,h2,h1.trans h2⟩

theorem actual_source_disc_convex : Convex ℝ sourceDisc := by
  intro u hu v hv a b ha hb hab
  have hb' : b=1-a := by linarith
  rw [hb']
  exact (actual_disc_combination u v hu hv a ⟨ha,by linarith⟩).2.2
end SafeLearning.CompleteFoundationsConvexSets
