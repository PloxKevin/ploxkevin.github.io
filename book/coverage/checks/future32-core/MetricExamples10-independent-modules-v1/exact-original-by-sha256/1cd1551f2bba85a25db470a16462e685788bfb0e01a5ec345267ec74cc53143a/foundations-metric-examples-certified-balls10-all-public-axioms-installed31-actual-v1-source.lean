import SafeLearning.CompleteFoundationsGeometry
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators NNReal
namespace SafeLearning.CompleteFoundationsMetricExamplesAndCertifiedBalls32

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem actual_all_input_coordinate_halfspace_distance
    (i : I) (x : EuclideanSpace ℝ I) :
    Metric.infDist x {y : EuclideanSpace ℝ I | y i ≤ 0}=max (x i) 0 := by
  have hne : ({y : EuclideanSpace ℝ I | y i ≤ 0} : Set _).Nonempty := ⟨0,by simp⟩
  apply le_antisymm
  · let y:=x-PiLp.single 2 i (max (x i) 0)
    have hy : y i ≤ 0 := by
      dsimp only [y]
      simp only [PiLp.sub_apply,PiLp.single_apply,ite_true]
      exact sub_nonpos.mpr (le_max_left _ _)
    have he : dist x y=max (x i) 0 := by
      rw [dist_eq_norm]
      dsimp only [y]
      rw [sub_sub_cancel,PiLp.norm_single,Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _)]
    exact (Metric.infDist_le_dist_of_mem (x:=x) (s:={y : EuclideanSpace ℝ I | y i ≤ 0}) (y:=y) hy).trans_eq he
  · apply (Metric.le_infDist hne).mpr
    intro y hy
    have hy0 : y i ≤ 0 := hy
    apply max_le
    · have hc:=PiLp.norm_apply_le (x-y) i
      rw [PiLp.sub_apply,Real.norm_eq_abs] at hc
      have h:=le_abs_self (x i-y i)
      rw [dist_eq_norm]
      linarith
    · exact dist_nonneg

theorem actual_every_real_normed_unit_ball_has_the_printed_all_input_distance
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (x : V) :
    Metric.infDist x (Metric.closedBall (0:V) 1)=max (‖x‖-1) 0 := by
  have hne : (Metric.closedBall (0:V) 1).Nonempty := ⟨0,by simp⟩
  apply le_antisymm
  · by_cases hx : ‖x‖ ≤ 1
    · have hm : x∈Metric.closedBall (0:V) 1 := by simpa using hx
      rw [Metric.infDist_zero_of_mem hm,max_eq_right (by linarith)]
    · have hp : 0 < ‖x‖ := by linarith
      let y:=‖x‖⁻¹ • x
      have hy : ‖y‖=1 := by
        dsimp only [y]
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (le_of_lt (inv_pos.mpr hp))]
        exact inv_mul_cancel₀ (ne_of_gt hp)
      have hm : y∈Metric.closedBall (0:V) 1 := by simpa using le_of_eq hy
      have hc : 0 ≤ 1-‖x‖⁻¹ := by
        have hi : ‖x‖⁻¹ ≤ 1 := (inv_le_one₀ hp).mpr (by linarith)
        linarith
      have he : dist x y=‖x‖-1 := by
        rw [dist_eq_norm]
        have hs : x-y=(1-‖x‖⁻¹) • x := by simp [y,sub_smul]
        rw [hs,norm_smul,Real.norm_eq_abs,abs_of_nonneg hc]
        field_simp
      exact (Metric.infDist_le_dist_of_mem hm).trans (he.trans_le (le_max_left _ _))
  · apply (Metric.le_infDist hne).mpr
    intro y hy
    have hnorm : ‖y‖ ≤ 1 := by simpa using hy
    apply max_le
    · have hn:=norm_sub_norm_le x y
      rw [dist_eq_norm]
      linarith
    · exact dist_nonneg

theorem actual_all_real_radii_infinity_balls_are_coordinate_boxes
    [Nonempty I] (x x0 : I → ℝ) (epsilon : ℝ) :
    ‖x-x0‖ ≤ epsilon ↔ ∀ i,|x i-x0 i| ≤ epsilon := by
  by_cases he : 0 ≤ epsilon
  · rw [pi_norm_le_iff_of_nonneg he]
    simp only [Pi.sub_apply,Real.norm_eq_abs]
  · constructor
    · intro h
      exact False.elim (he ((norm_nonneg (x-x0)).trans h))
    · intro h
      obtain ⟨i⟩:=‹Nonempty I›
      exact False.elim (he ((abs_nonneg _).trans (h i)))

def rectangularGrid (r c : ℕ) : SimpleGraph (Fin (r+1) × Fin (c+1)) :=
  SimpleGraph.pathGraph (r+1) □ SimpleGraph.pathGraph (c+1)

theorem actual_rectangular_grid_edges_are_exactly_horizontal_or_vertical_unit_steps
    (r c : ℕ) (u v : Fin (r+1) × Fin (c+1)) :
    (rectangularGrid r c).Adj u v ↔
    ((u.1.val+1=v.1.val ∨ v.1.val+1=u.1.val) ∧ u.2=v.2) ∨
    ((u.2.val+1=v.2.val ∨ v.2.val+1=u.2.val) ∧ u.1=v.1) := by
  simp [rectangularGrid,SimpleGraph.boxProd_adj,SimpleGraph.pathGraph_adj]

theorem actual_rectangular_grid_is_connected (r c : ℕ) :
    (rectangularGrid r c).Connected := by
  exact (SimpleGraph.pathGraph_connected r).boxProd (SimpleGraph.pathGraph_connected c)

theorem actual_rectangular_grid_shortest_path_length_is_a_real_metric
    (r c : ℕ) (u v w : Fin (r+1) × Fin (c+1)) :
    (0 ≤ ((rectangularGrid r c).dist u v : ℝ)) ∧
    (((rectangularGrid r c).dist u v : ℝ)=0 ↔ u=v) ∧
    ((rectangularGrid r c).dist u v : ℝ)=((rectangularGrid r c).dist v u : ℝ) ∧
    ((rectangularGrid r c).dist u w : ℝ) ≤
      ((rectangularGrid r c).dist u v : ℝ)+((rectangularGrid r c).dist v w : ℝ) ∧
    ∃ p : (rectangularGrid r c).Walk u v,
      p.length=(rectangularGrid r c).dist u v ∧
      ∀ q : (rectangularGrid r c).Walk u v,p.length ≤ q.length := by
  have hc:=actual_rectangular_grid_is_connected r c
  refine ⟨by positivity,?_,?_,?_,?_⟩
  · exact Nat.cast_eq_zero.trans hc.dist_eq_zero_iff
  · exact congrArg Nat.cast (SimpleGraph.dist_comm)
  · exact_mod_cast hc.dist_triangle
  · obtain ⟨p,hp⟩:=hc.exists_walk_length_eq_dist u v
    exact ⟨p,hp,fun q => hp.trans_le (SimpleGraph.dist_le q)⟩

theorem actual_Lipschitz_values_have_the_printed_lower_margin
    {X : Type*} [PseudoMetricSpace X] (g : X → ℝ) (L : ℝ≥0)
    (hg : LipschitzWith L g) (y z : X) : g z-(L:ℝ)*dist y z ≤ g y := by
  have h:=hg.dist_le_mul y z
  rw [Real.dist_eq] at h
  linarith [(abs_le.mp h).1]

theorem actual_union_of_all_positive_value_Lipschitz_balls_is_certified
    {X : Type*} [PseudoMetricSpace X] (g : X → ℝ) (L : ℝ≥0)
    (hg : LipschitzWith L g) (hL : 0 < (L:ℝ)) :
    ∀ y∈{y | ∃ z,0 < g z ∧ y∈Metric.closedBall z (g z/L)},0 ≤ g y := by
  intro y hy
  obtain ⟨z,hz,hy⟩:=hy
  exact CompleteFoundationsGeometry.positive_lipschitz_certified_ball
    g L hg hL z (g z) hz rfl y hy

theorem actual_zero_Lipschitz_constant_certifies_the_entire_domain_without_division
    {X : Type*} [PseudoMetricSpace X] (g : X → ℝ) (hg : LipschitzWith 0 g)
    (z : X) (hz : 0 < g z) : ∀ y, g y=g z ∧ 0 < g y := by
  intro y
  have hd:=hg.dist_le_mul y z
  have he : g y=g z := by
    apply dist_le_zero.mp
    simpa using hd
  exact ⟨he,he.symm ▸ hz⟩

end SafeLearning.CompleteFoundationsMetricExamplesAndCertifiedBalls32

namespace SafeLearning.CompleteFoundationsMetricExamplesAndCertifiedBalls32

theorem actual_every_connected_grid_or_other_graph_has_an_attained_shortest_path_metric
    {X : Type*} (G : SimpleGraph X) (hG : G.Connected) (u v w : X) :
    ((G.dist u v : ℝ)=0 ↔ u=v) ∧
    (G.dist u v : ℝ)=(G.dist v u : ℝ) ∧
    (G.dist u w : ℝ) ≤ (G.dist u v : ℝ)+(G.dist v w : ℝ) ∧
    ∃ p : G.Walk u v,p.length=G.dist u v ∧ ∀ q : G.Walk u v,p.length ≤ q.length := by
  refine ⟨Nat.cast_eq_zero.trans hG.dist_eq_zero_iff,congrArg Nat.cast SimpleGraph.dist_comm,?_,?_⟩
  · exact_mod_cast hG.dist_triangle
  · obtain ⟨p,hp⟩:=hG.exists_walk_length_eq_dist u v
    exact ⟨p,hp,fun q => hp.trans_le (SimpleGraph.dist_le q)⟩

end SafeLearning.CompleteFoundationsMetricExamplesAndCertifiedBalls32

#print axioms SafeLearning.CompleteFoundationsMetricExamplesAndCertifiedBalls32.actual_all_input_coordinate_halfspace_distance
#print axioms SafeLearning.CompleteFoundationsMetricExamplesAndCertifiedBalls32.actual_every_real_normed_unit_ball_has_the_printed_all_input_distance
#print axioms SafeLearning.CompleteFoundationsMetricExamplesAndCertifiedBalls32.actual_all_real_radii_infinity_balls_are_coordinate_boxes
#print axioms SafeLearning.CompleteFoundationsMetricExamplesAndCertifiedBalls32.actual_rectangular_grid_edges_are_exactly_horizontal_or_vertical_unit_steps
#print axioms SafeLearning.CompleteFoundationsMetricExamplesAndCertifiedBalls32.actual_rectangular_grid_is_connected
#print axioms SafeLearning.CompleteFoundationsMetricExamplesAndCertifiedBalls32.actual_rectangular_grid_shortest_path_length_is_a_real_metric
#print axioms SafeLearning.CompleteFoundationsMetricExamplesAndCertifiedBalls32.actual_Lipschitz_values_have_the_printed_lower_margin
#print axioms SafeLearning.CompleteFoundationsMetricExamplesAndCertifiedBalls32.actual_union_of_all_positive_value_Lipschitz_balls_is_certified
#print axioms SafeLearning.CompleteFoundationsMetricExamplesAndCertifiedBalls32.actual_zero_Lipschitz_constant_certifies_the_entire_domain_without_division
#print axioms SafeLearning.CompleteFoundationsMetricExamplesAndCertifiedBalls32.actual_every_connected_grid_or_other_graph_has_an_attained_shortest_path_metric
