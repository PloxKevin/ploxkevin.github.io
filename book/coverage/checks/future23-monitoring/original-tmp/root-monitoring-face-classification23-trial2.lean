import SafeLearning.CompleteMonitoringFaces22
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteMonitoringFaceClassification23
open SafeLearning.CompleteMonitoringGeometry21 SafeLearning.CompleteMonitoringFaces22

theorem actual_first_strictly_largest_above_one_unique (l1 l2 : ℝ)
    (h12 : l2 < l1) (h1 : 1 < l1) (v : Fractions) :
    IsMaximizer l1 l2 v ↔ v = vertex1 := by
  constructor
  · intro hm
    have hz := actual_larger_first_price_forces_zero_second_region l1 l2 h12 v hm
    have hb := hm.2 vertex1 actual_four_vertices_and_primal_optimum_in_the_polytope.1
    obtain ⟨ha,hc,hd,hs,hh⟩ := hm.1
    dsimp [lagrangian,vertex1] at hb
    have he := congrArg (fun x : ℝ => l1*x) hs
    have hzero : (l1-1)*v.v0=0 := by nlinarith
    have h0 := (mul_eq_zero.mp hzero).resolve_left (ne_of_gt (sub_pos.mpr h1))
    have hfirst : v.v1=1 := by linarith
    cases v; simp_all [vertex1]
  · rintro rfl
    refine ⟨actual_four_vertices_and_primal_optimum_in_the_polytope.1, ?_⟩
    intro w hw
    exact actual_larger_first_price_above_one_vertex_bound l1 l2 h12 h1.le w hw

theorem actual_first_strictly_largest_below_one_unique (l1 l2 : ℝ)
    (h12 : l2 < l1) (h1 : l1 < 1) (v : Fractions) :
    IsMaximizer l1 l2 v ↔ v = vertex3 := by
  constructor
  · intro hm
    have hz := actual_larger_first_price_forces_zero_second_region l1 l2 h12 v hm
    have hb := hm.2 vertex3 actual_four_vertices_and_primal_optimum_in_the_polytope.2.2.1
    obtain ⟨ha,hc,hd,hs,hh⟩ := hm.1
    dsimp [lagrangian,vertex3] at hb
    have he := congrArg (fun x : ℝ => l1*x) hs
    have hzero : (1-l1)*(1/2-v.v0)=0 := by nlinarith
    have h0 := (sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left (ne_of_gt (sub_pos.mpr h1)))).symm
    have hfirst : v.v1=1/2 := by linarith
    cases v; simp_all [vertex3]
  · rintro rfl
    refine ⟨actual_four_vertices_and_primal_optimum_in_the_polytope.2.2.1, ?_⟩
    intro w hw
    exact actual_larger_first_price_below_one_vertex_bound l1 l2 h12 h1.le w hw

theorem actual_first_threshold_one_has_full_tied_edge (l2 : ℝ)
    (h2 : l2 < 1) (v : Fractions) (hv : AchievablePolytope v) :
    IsMaximizer 1 l2 v ↔ v.v2=0 := by
  constructor
  · intro hm
    exact actual_larger_first_price_forces_zero_second_region 1 l2 h2 v hm
  · intro hz
    refine ⟨hv,?_⟩
    intro w hw
    have hb := actual_larger_first_price_above_one_vertex_bound 1 l2 h2 (le_refl _) w hw
    obtain ⟨ha,hc,hd,hs,hh⟩ := hv
    dsimp [lagrangian,vertex1] at hb ⊢
    simp only [hz, mul_zero, mul_one, zero_add, add_zero] at hs hb ⊢
    linarith

theorem actual_second_strictly_largest_above_one_unique (l1 l2 : ℝ)
    (h12 : l1 < l2) (h2 : 1 < l2) (v : Fractions) :
    IsMaximizer l1 l2 v ↔ v = vertex2 := by
  constructor
  · intro hm
    have hz := actual_larger_second_price_forces_zero_first_region l1 l2 h12 v hm
    have hb := hm.2 vertex2 actual_four_vertices_and_primal_optimum_in_the_polytope.2.1
    obtain ⟨ha,hc,hd,hs,hh⟩ := hm.1
    dsimp [lagrangian,vertex2] at hb
    have he := congrArg (fun x : ℝ => l2*x) hs
    have hzero : (l2-1)*v.v0=0 := by nlinarith
    have h0 := (mul_eq_zero.mp hzero).resolve_left (ne_of_gt (sub_pos.mpr h2))
    have hsecond : v.v2=1 := by linarith
    cases v; simp_all [vertex2]
  · rintro rfl
    refine ⟨actual_four_vertices_and_primal_optimum_in_the_polytope.2.1, ?_⟩
    intro w hw
    exact actual_larger_second_price_above_one_vertex_bound l1 l2 h12 h2.le w hw

theorem actual_second_strictly_largest_below_one_unique (l1 l2 : ℝ)
    (h12 : l1 < l2) (h2 : l2 < 1) (v : Fractions) :
    IsMaximizer l1 l2 v ↔ v = vertex4 := by
  constructor
  · intro hm
    have hz := actual_larger_second_price_forces_zero_first_region l1 l2 h12 v hm
    have hb := hm.2 vertex4 actual_four_vertices_and_primal_optimum_in_the_polytope.2.2.2.1
    obtain ⟨ha,hc,hd,hs,hh⟩ := hm.1
    dsimp [lagrangian,vertex4] at hb
    have he := congrArg (fun x : ℝ => l2*x) hs
    have hzero : (1-l2)*(1/2-v.v0)=0 := by nlinarith
    have h0 := (sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left (ne_of_gt (sub_pos.mpr h2)))).symm
    have hsecond : v.v2=1/2 := by linarith
    cases v; simp_all [vertex4]
  · rintro rfl
    refine ⟨actual_four_vertices_and_primal_optimum_in_the_polytope.2.2.2.1, ?_⟩
    intro w hw
    exact actual_larger_second_price_below_one_vertex_bound l1 l2 h12 h2.le w hw

theorem actual_second_threshold_one_has_full_tied_edge (l1 : ℝ)
    (h1 : l1 < 1) (v : Fractions) (hv : AchievablePolytope v) :
    IsMaximizer l1 1 v ↔ v.v1=0 := by
  constructor
  · intro hm
    exact actual_larger_second_price_forces_zero_first_region l1 1 h1 v hm
  · intro hz
    refine ⟨hv,?_⟩
    intro w hw
    have hb := actual_larger_second_price_above_one_vertex_bound l1 1 h1 (le_refl _) w hw
    obtain ⟨ha,hc,hd,hs,hh⟩ := hv
    dsimp [lagrangian,vertex2] at hb ⊢
    simp only [hz, mul_zero, mul_one, zero_add, add_zero] at hs hb ⊢
    linarith

theorem actual_zero_second_region_is_exact_first_edge (v : Fractions) :
    (AchievablePolytope v ∧ v.v2=0) ↔
      ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ v=⟨t/2,1-t/2,0⟩ := by
  constructor
  · rintro ⟨⟨ha,hb,hc,hs,hh⟩,hz⟩
    refine ⟨2*v.v0,by linarith,by linarith,?_⟩
    have hfirst : v.v1=1-v.v0 := by linarith
    cases v; simp_all
  · rintro ⟨t,ht,ht1,rfl⟩
    dsimp [AchievablePolytope]
    constructor
    · exact ⟨by linarith, by linarith, by norm_num, by ring, by linarith⟩
    · rfl

theorem actual_zero_first_region_is_exact_second_edge (v : Fractions) :
    (AchievablePolytope v ∧ v.v1=0) ↔
      ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ v=⟨t/2,0,1-t/2⟩ := by
  constructor
  · rintro ⟨⟨ha,hb,hc,hs,hh⟩,hz⟩
    refine ⟨2*v.v0,by linarith,by linarith,?_⟩
    have hsecond : v.v2=1-v.v0 := by linarith
    cases v; simp_all
  · rintro ⟨t,ht,ht1,rfl⟩
    dsimp [AchievablePolytope]
    constructor
    · exact ⟨by linarith, by norm_num, by linarith, by ring, by linarith⟩
    · rfl
end SafeLearning.CompleteMonitoringFaceClassification23
