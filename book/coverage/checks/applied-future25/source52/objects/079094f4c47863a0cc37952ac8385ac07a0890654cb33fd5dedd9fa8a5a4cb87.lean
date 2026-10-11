import SafeLearning.CompleteMonitoringGeometry21
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteMonitoringFaces22
open SafeLearning.CompleteMonitoringGeometry21

theorem actual_source_polytope_is_exactly_the_four_vertex_convex_hull (v : Fractions) :
    AchievablePolytope v ↔ ∃ a b c d : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧
      a+b+c+d=1 ∧ v.v0=(c+d)/2 ∧ v.v1=a+c/2 ∧ v.v2=b+d/2 := by
  constructor
  · intro hv
    obtain ⟨h0,h1,h2,hs,hh⟩:=hv
    have hd : 0 < 1-v.v0 := by linarith
    let q := v.v1/(1-v.v0)
    have hq : 0 ≤ q := div_nonneg h1 hd.le
    have hq1 : q ≤ 1 := (div_le_one hd).mpr (by linarith)
    have hu : 0 ≤ 1-2*v.v0 := by linarith
    refine ⟨q*(1-2*v.v0),(1-q)*(1-2*v.v0),2*v.v0*q,2*v.v0*(1-q),
      mul_nonneg hq hu,mul_nonneg (by linarith) hu,
      mul_nonneg (by linarith) hq,mul_nonneg (by linarith) (by linarith),?_,?_,?_,?_⟩
    · ring
    · ring
    · dsimp [q];field_simp [ne_of_gt hd];ring
    · dsimp [q];field_simp [ne_of_gt hd];nlinarith
  · rintro ⟨a,b,c,d,ha,hb,hc,hd,hs,h0,h1,h2⟩
    refine ⟨?_,?_,?_,?_,?_⟩ <;> nlinarith

theorem actual_larger_second_price_above_one_vertex_bound
    (l1 l2 : ℝ) (h12 : l1 < l2) (h2 : 1 ≤ l2) (v : Fractions)
    (hv : AchievablePolytope v) : lagrangian l1 l2 v ≤ lagrangian l1 l2 vertex2 := by
  rcases hv with ⟨ha,hb,hc,hs,hh⟩;dsimp [lagrangian,vertex2]
  have hp:=mul_nonneg (sub_nonneg.mpr h2) ha
  have hq:=mul_nonneg (sub_pos.mpr h12).le hb
  nlinarith [congrArg (fun x : ℝ=>l2*x) hs]

theorem actual_larger_second_price_below_one_vertex_bound
    (l1 l2 : ℝ) (h12 : l1 < l2) (h2 : l2 ≤ 1) (v : Fractions)
    (hv : AchievablePolytope v) : lagrangian l1 l2 v ≤ lagrangian l1 l2 vertex4 := by
  rcases hv with ⟨ha,hb,hc,hs,hh⟩;dsimp [lagrangian,vertex4]
  have hp:=mul_nonneg (sub_nonneg.mpr h2) (sub_nonneg.mpr hh)
  have hq:=mul_nonneg (sub_pos.mpr h12).le hb
  nlinarith [congrArg (fun x : ℝ=>l2*x) hs]

theorem actual_larger_second_price_forces_zero_first_region
    (l1 l2 : ℝ) (h12 : l1 < l2) (v : Fractions)
    (hmax : IsMaximizer l1 l2 v) : v.v1 = 0 := by
  obtain ⟨hvert1,hvert2,hvert3,hvert4,hopt⟩:=actual_four_vertices_and_primal_optimum_in_the_polytope
  obtain ⟨ha,hb,hc,hs,hh⟩:=hmax.1
  have hmul:=congrArg (fun x : ℝ=>l2*x) hs
  by_cases h2 : 1 ≤ l2
  · have hbound:=hmax.2 vertex2 hvert2
    dsimp [lagrangian,vertex2] at hbound
    have hp:=mul_nonneg (sub_nonneg.mpr h2) ha
    have hz : (l2-l1)*v.v1=0 := by nlinarith
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt (sub_pos.mpr h12))
  · have hbound:=hmax.2 vertex4 hvert4
    dsimp [lagrangian,vertex4] at hbound
    have hp:=mul_nonneg (sub_pos.mpr (lt_of_not_ge h2)).le (sub_nonneg.mpr hh)
    have hz : (l2-l1)*v.v1=0 := by nlinarith
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt (sub_pos.mpr h12))
end SafeLearning.CompleteMonitoringFaces22
