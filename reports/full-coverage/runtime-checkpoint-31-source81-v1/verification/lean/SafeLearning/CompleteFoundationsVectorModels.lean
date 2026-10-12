import SafeLearning.PrimersFoundations

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators RealInnerProductSpace NNReal

namespace SafeLearning.CompleteFoundationsVectorModels

def vector2 (a b : ℝ) : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![a,b]
def vector3 (a b c : ℝ) : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ![a,b,c]

theorem vector_two_norm (a b : ℝ) : ‖vector2 a b‖=Real.sqrt (a^2+b^2) := by
  simp [vector2,EuclideanSpace.norm_eq,Fin.sum_univ_succ,Real.norm_eq_abs,sq_abs]

theorem vector_two_inner (a b c d : ℝ) : ⟪vector2 a b,vector2 c d⟫=a*c+b*d := by
  simp [vector2,PiLp.inner_apply,Fin.sum_univ_succ]
  ring

theorem source_three_lengths :
    ‖(WithLp.toLp 1 ![(2 : ℝ),-1,2] : PiLp 1 (fun _ : Fin 3 => ℝ))‖=5 ∧
    ‖vector3 2 (-1) 2‖=3 ∧ ‖(![(2 : ℝ),-1,2] : Fin 3 → ℝ)‖=2 := by
  constructor
  · norm_num [PiLp.norm_eq_of_L1,Fin.sum_univ_succ]
  constructor
  · norm_num [vector3,EuclideanSpace.norm_eq,Fin.sum_univ_succ,Real.norm_eq_abs]
  · apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ)≤2)).mpr
      intro i
      fin_cases i <;> norm_num
    · simpa using norm_le_pi_norm (![(2 : ℝ),-1,2] : Fin 3 → ℝ) (0 : Fin 3)

theorem source_three_perpendicular :
    ⟪vector3 2 (-1) 2,vector3 1 2 0⟫=0 ∧
    vector3 2 (-1) 2≠0 ∧ vector3 1 2 0≠0 := by
  constructor
  · norm_num [vector3,PiLp.inner_apply,Fin.sum_univ_succ]
  constructor
  · intro h
    have hh := congrArg (fun x : EuclideanSpace ℝ (Fin 3) => x 0) h
    norm_num [vector3] at hh
  · intro h
    have hh := congrArg (fun x : EuclideanSpace ℝ (Fin 3) => x 0) h
    norm_num [vector3] at hh

theorem source_three_length_comparison :
    (2 : ℝ)≤3 ∧ (3 : ℝ)≤5 ∧ (5 : ℝ)≤3*Real.sqrt 3 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ)≤3)
  have hp := Real.sqrt_nonneg (3 : ℝ)
  constructor
  · norm_num
  constructor
  · norm_num
  · nlinarith

theorem box_objective_upper (x : Fin 2 → ℝ) (hx : ‖x‖≤1/5) :
    3*x 0-4*x 1≤7/5 := by
  have hb := (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ)≤1/5)).mp hx
  have h₀ := hb 0
  have h₁ := hb 1
  rw [Real.norm_eq_abs] at h₀ h₁
  linarith [le_abs_self (x 0),neg_le_abs (x 1)]

theorem box_objective_equals_dot (x : Fin 2 → ℝ) :
    (![(3 : ℝ),-4] : Fin 2 → ℝ) ⬝ᵥ x=3*x 0-4*x 1 := by
  simp [dotProduct,Fin.sum_univ_succ]
  ring

theorem euclidean_ball_inside_box (x : EuclideanSpace ℝ (Fin 2)) (hx : ‖x‖≤1/5) :
    ‖(x : Fin 2 → ℝ)‖≤1/5 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ)≤1/5)).mpr
  intro i
  exact (PiLp.norm_apply_le x i).trans hx

theorem box_maximum :
    IsGreatest ((fun x : Fin 2 → ℝ => 3*x 0-4*x 1) '' {x | ‖x‖≤1/5}) (7/5) := by
  constructor
  · refine ⟨![(1/5 : ℝ),-1/5],?_,?_⟩
    · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ)≤1/5)).mpr
      intro i
      fin_cases i <;> norm_num
    · norm_num
  · rintro y ⟨x,hx,rfl⟩
    exact box_objective_upper x hx

theorem euclidean_objective_upper (x : EuclideanSpace ℝ (Fin 2)) (hx : ‖x‖≤1/5) :
    ⟪vector2 3 (-4),x⟫≤1 := by
  have hw : ‖vector2 3 (-4)‖=5 := by norm_num [vector_two_norm]
  have hh := (le_abs_self ⟪vector2 3 (-4),x⟫).trans (abs_real_inner_le_norm _ _)
  rw [hw] at hh
  linarith

theorem euclidean_maximum :
    IsGreatest ((fun x : EuclideanSpace ℝ (Fin 2) => ⟪vector2 3 (-4),x⟫) ''
      {x | ‖x‖≤1/5}) 1 := by
  constructor
  · refine ⟨vector2 (3/25) (-4/25),?_,?_⟩
    · norm_num [vector_two_norm,Real.sqrt_div]
    · norm_num [vector_two_inner]
  · rintro y ⟨x,hx,rfl⟩
    exact euclidean_objective_upper x hx

theorem source_box_corner_outside_euclidean_ball :
    ‖vector2 (1/5) (-1/5)‖>1/5 := by
  have hs : ‖vector2 (1/5) (-1/5)‖^2=2/25 := by
    rw [vector_two_norm,Real.sq_sqrt (by positivity)]
    norm_num
  have hp := norm_nonneg (vector2 (1/5) (-1/5))
  nlinarith

theorem distance_to_any_set_lipschitz {E : Type*} [NormedAddCommGroup E]
    (C : Set E) (x y : E) : |Metric.infDist x C-Metric.infDist y C|≤‖x-y‖ := by
  simpa only [Real.dist_eq,dist_eq_norm,Real.norm_eq_abs,NNReal.coe_one,one_mul] using
    (Metric.lipschitz_infDist_pt C).dist_le_mul x y

theorem nearest_point_exists {E : Type*} [MetricSpace E] [ProperSpace E]
    (C : Set E) (hclosed : IsClosed C) (hne : C.Nonempty) (y : E) :
    ∃ c ∈ C,Metric.infDist y C=dist y c := hclosed.exists_infDist_eq_dist hne y

theorem distance_one_direction_via_nearest {E : Type*} [MetricSpace E] [ProperSpace E]
    (C : Set E) (hclosed : IsClosed C) (hne : C.Nonempty) (x y : E) :
    ∃ c ∈ C,Metric.infDist y C=dist y c ∧
      Metric.infDist x C≤dist x y+Metric.infDist y C := by
  rcases nearest_point_exists C hclosed hne y with ⟨c,hc,heq⟩
  refine ⟨c,hc,heq,?_⟩
  rw [heq]
  exact (Metric.infDist_le_dist_of_mem hc).trans (dist_triangle x y c)

def unitDisc : Set (EuclideanSpace ℝ (Fin 2)) := Metric.closedBall 0 1

theorem source_radial_point_attains :
    vector2 (3/5) (4/5) ∈ unitDisc ∧
      dist (vector2 3 4) (vector2 (3/5) (4/5))=4 := by
  constructor
  · rw [unitDisc,Metric.mem_closedBall,dist_zero_right]
    norm_num [vector_two_norm,Real.sqrt_div]
  · rw [dist_eq_norm]
    have hsub : vector2 3 4-vector2 (3/5) (4/5)=vector2 (12/5) (16/5) := by
      ext i
      fin_cases i <;> norm_num [vector2]
    rw [hsub]
    norm_num [vector_two_norm,Real.sqrt_div]

theorem source_disc_distance : Metric.infDist (vector2 3 4) unitDisc=4 := by
  apply le_antisymm
  · simpa only [source_radial_point_attains.2] using
      Metric.infDist_le_dist_of_mem (x := vector2 3 4) source_radial_point_attains.1
  · apply (Metric.le_infDist ⟨vector2 (3/5) (4/5),source_radial_point_attains.1⟩).mpr
    intro c hc
    have hc₁ : ‖c‖≤1 := by simpa only [unitDisc,Metric.mem_closedBall,dist_zero_right] using hc
    have hn : ‖vector2 3 4‖=5 := by norm_num [vector_two_norm]
    have hh := norm_sub_norm_le (vector2 3 4) c
    rw [hn,← dist_eq_norm] at hh
    linarith

theorem source_disc_perturbation (u : EuclideanSpace ℝ (Fin 2)) (hu : ‖u‖≤1/10) :
    Metric.infDist (vector2 3 4+u) unitDisc ∈ Icc (39/10 : ℝ) (41/10) := by
  have hh := distance_to_any_set_lipschitz unitDisc (vector2 3 4+u) (vector2 3 4)
  rw [source_disc_distance,add_sub_cancel_left] at hh
  have hb := abs_le.mp (hh.trans hu)
  constructor <;> linarith [hb.1,hb.2]

end SafeLearning.CompleteFoundationsVectorModels
