import SafeLearning.CompleteMonitoringFaceClassification23
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteMonitoringExposedInterior23
open SafeLearning.CompleteMonitoringGeometry21 SafeLearning.CompleteMonitoringFaceClassification23

def mixture (t : ℝ) (u v : Fractions) : Fractions :=
  ⟨t*u.v0+(1-t)*v.v0,t*u.v1+(1-t)*v.v1,t*u.v2+(1-t)*v.v2⟩
def IsExposedFraction (z : Fractions) : Prop :=
  ∃ l1 l2 : ℝ, IsMaximizer l1 l2 z ∧ ∀ w, IsMaximizer l1 l2 w → w=z
def IsExtremeFraction (z : Fractions) : Prop :=
  AchievablePolytope z ∧ ∀ u v t, AchievablePolytope u → AchievablePolytope v →
    0<t → t<1 → mixture t u v=z → u=z ∧ v=z

theorem actual_lagrangian_affine_for_every_fraction_mixture (l1 l2 t : ℝ)
    (u v : Fractions) : lagrangian l1 l2 (mixture t u v)=
      t*lagrangian l1 l2 u+(1-t)*lagrangian l1 l2 v := by
  dsimp [lagrangian,mixture];ring

theorem actual_fraction_polytope_is_convex_under_the_coordinate_mixture
    (u v : Fractions) (hu : AchievablePolytope u) (hv : AchievablePolytope v)
    (t : ℝ) (ht : 0≤t) (ht1 : t≤1) : AchievablePolytope (mixture t u v) := by
  obtain ⟨ua,ub,uc,us,uh⟩ := hu
  obtain ⟨va,vb,vc,vs,vh⟩ := hv
  have ht' : 0≤1-t := by linarith
  refine ⟨add_nonneg (mul_nonneg ht ua) (mul_nonneg ht' va),
    add_nonneg (mul_nonneg ht ub) (mul_nonneg ht' vb),
    add_nonneg (mul_nonneg ht uc) (mul_nonneg ht' vc),?_,?_⟩
  · dsimp [mixture]
    nlinarith [congrArg (fun x : ℝ=>t*x) us,congrArg (fun x : ℝ=>(1-t)*x) vs]
  · dsimp [mixture]
    have a := mul_nonneg ht (sub_nonneg.mpr uh)
    have b := mul_nonneg ht' (sub_nonneg.mpr vh)
    nlinarith

theorem actual_unique_exposed_fraction_is_an_extreme_point (z : Fractions)
    (hz : IsExposedFraction z) : IsExtremeFraction z := by
  obtain ⟨l1,l2,hm,hunique⟩ := hz
  refine ⟨hm.1,?_⟩
  intro u v t hu hv ht ht1 hmix
  have huL := hm.2 u hu
  have hvL := hm.2 v hv
  have he := congrArg (lagrangian l1 l2) hmix
  rw [actual_lagrangian_affine_for_every_fraction_mixture] at he
  have hp := mul_nonneg ht.le (sub_nonneg.mpr huL)
  have hq := mul_nonneg (sub_pos.mpr ht1).le (sub_nonneg.mpr hvL)
  have hu0 : t*(lagrangian l1 l2 z-lagrangian l1 l2 u)=0 := by nlinarith
  have hv0 : (1-t)*(lagrangian l1 l2 z-lagrangian l1 l2 v)=0 := by nlinarith
  have huEq : lagrangian l1 l2 u=lagrangian l1 l2 z := by
    linarith [(mul_eq_zero.mp hu0).resolve_left (ne_of_gt ht)]
  have hvEq : lagrangian l1 l2 v=lagrangian l1 l2 z := by
    linarith [(mul_eq_zero.mp hv0).resolve_left (ne_of_gt (sub_pos.mpr ht1))]
  exact ⟨hunique u ⟨hu,fun w hw=>by rw [huEq];exact hm.2 w hw⟩,
    hunique v ⟨hv,fun w hw=>by rw [hvEq];exact hm.2 w hw⟩⟩

theorem actual_four_printed_vertices_are_all_exposed :
    IsExposedFraction vertex1 ∧ IsExposedFraction vertex2 ∧
    IsExposedFraction vertex3 ∧ IsExposedFraction vertex4 := by
  refine ⟨?_,?_,?_,?_⟩
  · refine ⟨2,0,?_,?_⟩
    · exact (actual_first_strictly_largest_above_one_unique 2 0 (by norm_num) (by norm_num) vertex1).mpr rfl
    · intro w hw;exact (actual_first_strictly_largest_above_one_unique 2 0 (by norm_num) (by norm_num) w).mp hw
  · refine ⟨0,2,?_,?_⟩
    · exact (actual_second_strictly_largest_above_one_unique 0 2 (by norm_num) (by norm_num) vertex2).mpr rfl
    · intro w hw;exact (actual_second_strictly_largest_above_one_unique 0 2 (by norm_num) (by norm_num) w).mp hw
  · refine ⟨1/2,0,?_,?_⟩
    · exact (actual_first_strictly_largest_below_one_unique (1/2) 0 (by norm_num) (by norm_num) vertex3).mpr rfl
    · intro w hw;exact (actual_first_strictly_largest_below_one_unique (1/2) 0 (by norm_num) (by norm_num) w).mp hw
  · refine ⟨0,1/2,?_,?_⟩
    · exact (actual_second_strictly_largest_below_one_unique 0 (1/2) (by norm_num) (by norm_num) vertex4).mpr rfl
    · intro w hw;exact (actual_second_strictly_largest_below_one_unique 0 (1/2) (by norm_num) (by norm_num) w).mp hw

theorem actual_four_printed_vertices_are_all_extreme :
    IsExtremeFraction vertex1 ∧ IsExtremeFraction vertex2 ∧
    IsExtremeFraction vertex3 ∧ IsExtremeFraction vertex4 := by
  obtain ⟨h1,h2,h3,h4⟩ := actual_four_printed_vertices_are_all_exposed
  exact ⟨actual_unique_exposed_fraction_is_an_extreme_point vertex1 h1,
    actual_unique_exposed_fraction_is_an_extreme_point vertex2 h2,
    actual_unique_exposed_fraction_is_an_extreme_point vertex3 h3,
    actual_unique_exposed_fraction_is_an_extreme_point vertex4 h4⟩

theorem actual_primal_optimum_has_a_relative_plane_neighborhood (v : Fractions)
    (hs : v.v0+v.v1+v.v2=1)
    (h0 : |v.v0-1/3|<1/12) (h1 : |v.v1-1/3|<1/12)
    (h2 : |v.v2-1/3|<1/12) : AchievablePolytope v := by
  obtain ⟨h0a,h0b⟩ := abs_lt.mp h0
  obtain ⟨h1a,h1b⟩ := abs_lt.mp h1
  obtain ⟨h2a,h2b⟩ := abs_lt.mp h2
  exact ⟨by linarith,by linarith,by linarith,hs,by linarith⟩
end SafeLearning.CompleteMonitoringExposedInterior23
