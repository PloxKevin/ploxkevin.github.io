import Mathlib

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteMonitoringGeometry21

structure Fractions where
  v0 : ℝ
  v1 : ℝ
  v2 : ℝ

def AchievablePolytope (v : Fractions) : Prop :=
  0 ≤ v.v0 ∧ 0 ≤ v.v1 ∧ 0 ≤ v.v2 ∧ v.v0 + v.v1 + v.v2 = 1 ∧ v.v0 ≤ 1/2

def Feasible (v : Fractions) : Prop := AchievablePolytope v ∧ 1/3 ≤ v.v1 ∧ 1/3 ≤ v.v2

def lagrangian (l1 l2 : ℝ) (v : Fractions) : ℝ :=
  v.v0 + l1 * v.v1 + l2 * v.v2 - (l1+l2)/3

def vertex1 : Fractions := ⟨0,1,0⟩
def vertex2 : Fractions := ⟨0,0,1⟩
def vertex3 : Fractions := ⟨1/2,1/2,0⟩
def vertex4 : Fractions := ⟨1/2,0,1/2⟩
def optimum : Fractions := ⟨1/3,1/3,1/3⟩

def IsMaximizer (l1 l2 : ℝ) (v : Fractions) : Prop :=
  AchievablePolytope v ∧ ∀ w, AchievablePolytope w → lagrangian l1 l2 w ≤ lagrangian l1 l2 v

theorem actual_four_vertices_and_primal_optimum_in_the_polytope :
    AchievablePolytope vertex1 ∧ AchievablePolytope vertex2 ∧
    AchievablePolytope vertex3 ∧ AchievablePolytope vertex4 ∧ Feasible optimum := by
  norm_num [AchievablePolytope,Feasible,vertex1,vertex2,vertex3,vertex4,optimum]

theorem actual_every_feasible_fraction_has_reward_at_most_one_third
    (v : Fractions) (hv : Feasible v) : v.v0 ≤ 1/3 := by
  rcases hv with ⟨⟨ha,hb,hc,hs,hh⟩,hb',hc'⟩; linarith

theorem actual_primal_reward_optimum_has_unique_fractions
    (v : Fractions) (hv : Feasible v) (h : v.v0 = 1/3) : v = optimum := by
  rcases hv with ⟨⟨ha,hb,hc,hs,hh⟩,hb',hc'⟩
  have hb'' : v.v1 = 1/3 := by linarith
  have hc'' : v.v2 = 1/3 := by linarith
  cases v; simp_all [optimum]

theorem actual_lagrangian_is_constant_at_the_dual_prices
    (v : Fractions) (hv : AchievablePolytope v) : lagrangian 1 1 v = 1/3 := by
  rcases hv with ⟨ha,hb,hc,hs,hh⟩; dsimp [lagrangian]; linarith

theorem actual_every_polytope_fraction_maximizes_at_dual_prices
    (v : Fractions) (hv : AchievablePolytope v) : IsMaximizer 1 1 v := by
  refine ⟨hv,?_⟩; intro w hw
  rw [actual_lagrangian_is_constant_at_the_dual_prices w hw,
      actual_lagrangian_is_constant_at_the_dual_prices v hv]

theorem actual_optimum_lagrangian_value_for_any_prices (l1 l2 : ℝ) :
    lagrangian l1 l2 optimum = 1/3 := by dsimp [lagrangian,optimum]; ring

theorem actual_vertex_lagrangian_values (l1 l2 : ℝ) :
    lagrangian l1 l2 vertex1 = l1-(l1+l2)/3 ∧
    lagrangian l1 l2 vertex2 = l2-(l1+l2)/3 ∧
    lagrangian l1 l2 vertex3 = (1+l1)/2-(l1+l2)/3 ∧
    lagrangian l1 l2 vertex4 = (1+l2)/2-(l1+l2)/3 := by
  dsimp [lagrangian,vertex1,vertex2,vertex3,vertex4]; constructor; ring
  constructor; ring
  constructor <;> ring

theorem actual_primal_optimum_maximizes_only_at_exact_dual_prices
    (l1 l2 : ℝ) (h : IsMaximizer l1 l2 optimum) : l1 = 1 ∧ l2 = 1 := by
  obtain ⟨h1,h2,h3,h4,hopt⟩ := actual_four_vertices_and_primal_optimum_in_the_polytope
  have a:=h.2 vertex1 h1;have b:=h.2 vertex2 h2;have c:=h.2 vertex3 h3;have d:=h.2 vertex4 h4
  rw [actual_optimum_lagrangian_value_for_any_prices] at a b c d
  dsimp [lagrangian,vertex1,vertex2,vertex3,vertex4] at a b c d
  constructor <;> linarith

theorem actual_no_other_prices_recover_an_optimal_feasible_maximizer
    (l1 l2 : ℝ) (hprices : l1 ≠ 1 ∨ l2 ≠ 1) (v : Fractions)
    (hmax : IsMaximizer l1 l2 v) (hfeas : Feasible v) : v.v0 ≠ 1/3 := by
  intro hreward
  have hv:=actual_primal_reward_optimum_has_unique_fractions v hfeas hreward
  rw [hv] at hmax
  obtain ⟨h1,h2⟩:=actual_primal_optimum_maximizes_only_at_exact_dual_prices l1 l2 hmax
  rcases hprices with h|h; exact h h1; exact h h2

theorem actual_larger_first_price_above_one_vertex_bound
    (l1 l2 : ℝ) (h12 : l2 < l1) (h1 : 1 ≤ l1) (v : Fractions)
    (hv : AchievablePolytope v) : lagrangian l1 l2 v ≤ lagrangian l1 l2 vertex1 := by
  rcases hv with ⟨ha,hb,hc,hs,hh⟩; dsimp [lagrangian,vertex1]
  have hp:=mul_nonneg (sub_nonneg.mpr h1) ha
  have hq:=mul_nonneg (sub_pos.mpr h12).le hc
  nlinarith [congrArg (fun x : ℝ=> l1*x) hs]

theorem actual_larger_first_price_below_one_vertex_bound
    (l1 l2 : ℝ) (h12 : l2 < l1) (h1 : l1 ≤ 1) (v : Fractions)
    (hv : AchievablePolytope v) : lagrangian l1 l2 v ≤ lagrangian l1 l2 vertex3 := by
  rcases hv with ⟨ha,hb,hc,hs,hh⟩; dsimp [lagrangian,vertex3]
  have hp:=mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr hh)
  have hq:=mul_nonneg (sub_pos.mpr h12).le hc
  nlinarith [congrArg (fun x : ℝ=> l1*x) hs]

theorem actual_larger_first_price_forces_zero_second_region
    (l1 l2 : ℝ) (h12 : l2 < l1) (v : Fractions)
    (hmax : IsMaximizer l1 l2 v) : v.v2 = 0 := by
  obtain ⟨hvert1,hvert2,hvert3,hvert4,hopt⟩ := actual_four_vertices_and_primal_optimum_in_the_polytope
  obtain ⟨ha,hb,hc,hs,hh⟩:=hmax.1
  have hmul:=congrArg (fun x : ℝ=>l1*x) hs
  by_cases h1 : 1 ≤ l1
  · have hbound:=hmax.2 vertex1 hvert1
    dsimp [lagrangian,vertex1] at hbound
    have hp:=mul_nonneg (sub_nonneg.mpr h1) ha
    have hz : (l1-l2)*v.v2 = 0 := by nlinarith
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt (sub_pos.mpr h12))
  · have hbound:=hmax.2 vertex3 hvert3
    dsimp [lagrangian,vertex3] at hbound
    have hp:=mul_nonneg (sub_pos.mpr (lt_of_not_ge h1)).le (sub_nonneg.mpr hh)
    have hz : (l1-l2)*v.v2 = 0 := by nlinarith
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt (sub_pos.mpr h12))

theorem actual_equal_prices_below_one_have_exact_returning_edge
    (l : ℝ) (hl : l < 1) (v : Fractions) (hv : AchievablePolytope v) :
    IsMaximizer l l v ↔ v.v0 = 1/2 := by
  obtain ⟨h1,h2,h3,h4,hopt⟩:=actual_four_vertices_and_primal_optimum_in_the_polytope
  obtain ⟨ha,hb,hc,hs,hh⟩:=hv
  constructor
  · intro hm
    have h:=hm.2 vertex3 h3; dsimp [lagrangian,vertex3] at h
    have he:=congrArg (fun x : ℝ=>l*x) hs
    have hz : (1-l)*(1/2-v.v0)=0 := by nlinarith
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (ne_of_gt (sub_pos.mpr hl)))).symm
  · intro h0
    refine ⟨hv,?_⟩;intro w hw
    obtain ⟨wa,wb,wc,ws,wh⟩:=hw
    have wp:=mul_nonneg (sub_pos.mpr hl).le (sub_nonneg.mpr wh)
    dsimp [lagrangian]; rw [h0]
    nlinarith [congrArg (fun x : ℝ=>l*x) hs,congrArg (fun x : ℝ=>l*x) ws]

theorem actual_equal_prices_above_one_have_exact_zero_reward_edge
    (l : ℝ) (hl : 1 < l) (v : Fractions) (hv : AchievablePolytope v) :
    IsMaximizer l l v ↔ v.v0 = 0 := by
  obtain ⟨h1,h2,h3,h4,hopt⟩:=actual_four_vertices_and_primal_optimum_in_the_polytope
  obtain ⟨ha,hb,hc,hs,hh⟩:=hv
  constructor
  · intro hm
    have h:=hm.2 vertex1 h1; dsimp [lagrangian,vertex1] at h
    have he:=congrArg (fun x : ℝ=>l*x) hs
    have hz : (l-1)*v.v0=0 := by nlinarith
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt (sub_pos.mpr hl))
  · intro h0
    refine ⟨hv,?_⟩;intro w hw
    obtain ⟨wa,wb,wc,ws,wh⟩:=hw
    have wp:=mul_nonneg (sub_pos.mpr hl).le wa
    dsimp [lagrangian]; rw [h0]
    nlinarith [congrArg (fun x : ℝ=>l*x) hs,congrArg (fun x : ℝ=>l*x) ws]

end SafeLearning.CompleteMonitoringGeometry21
