import SafeLearning.CompleteFoundationsNormDuality
import SafeLearning.CompleteFoundationsCenteredCubeNetsWhole30
import SafeLearning.CompleteFoundationsQuadraticTwentyNet24
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators NNReal
namespace SafeLearning.CompleteFoundationsCubeRadiusAndNetMargin32
open CompleteFoundationsNormDuality
open CompleteFoundationsCenteredCubeNetsWhole30
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem actual_arbitrary_side_centered_cube_lies_in_its_half_diagonal_Euclidean_ball
    (s : ℝ) (hs : 0 ≤ s) (c x : EuclideanSpace ℝ I)
    (hx : ∀ i,|x i-c i| ≤ s/2) :
    dist x c ≤ s*Real.sqrt (Fintype.card I)/2 := by
  have hInf : ‖(fun i => x i-c i : I → ℝ)‖ ≤ s/2 := by
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ s/2)).mpr
    intro i
    simpa only [Real.norm_eq_abs] using hx i
  calc
    dist x c=l2Norm (fun i => x i-c i) := by
      rw [dist_eq_norm]
      congr 1
    _ ≤ Real.sqrt (Fintype.card I)*(s/2) :=
      actual_infinity_ball_in_euclidean_ball _ _ (by positivity) hInf
    _=s*Real.sqrt (Fintype.card I)/2 := by ring

theorem actual_cube_corner_attains_the_half_diagonal_radius
    (s : ℝ) (hs : 0 ≤ s) (c : EuclideanSpace ℝ I) :
    dist (c+WithLp.toLp 2 (fun _ : I => s/2)) c=s*Real.sqrt (Fintype.card I)/2 := by
  calc
    _=l2Norm (fun _ : I => s/2) := by
      rw [dist_eq_norm,add_sub_cancel_left]
      rfl
    _=Real.sqrt (Fintype.card I)*(s/2) :=
      actual_constant_vector_attains_dimension_conversion _ (by positivity)
    _=s*Real.sqrt (Fintype.card I)/2 := by ring

theorem actual_isometric_cube_image_has_the_same_half_diagonal_ball
    (s : ℝ) (hs : 0 ≤ s) (c x : EuclideanSpace ℝ I)
    (hx : ∀ i,|x i-c i| ≤ s/2)
    (e : EuclideanSpace ℝ I → EuclideanSpace ℝ I) (he : Isometry e) :
    dist (e x) (e c) ≤ s*Real.sqrt (Fintype.card I)/2 := by
  rw [he.dist_eq]
  exact actual_arbitrary_side_centered_cube_lies_in_its_half_diagonal_Euclidean_ball s hs c x hx

theorem actual_general_finite_net_transfers_every_sampled_lower_margin
    {E : Type*} [PseudoMetricSpace E] (D : Set E) (Z : Finset E)
    (L : ℝ≥0) (tau m0 : ℝ) (f : E → ℝ)
    (hf : LipschitzOnWith L f D) (hnet : IsFiniteNet D Z tau)
    (hm : ∀ z∈Z,m0 ≤ f z) :
    ∀ x∈D,m0-(L:ℝ)*tau ≤ f x := by
  exact CompleteFoundationsQuadraticTwentyNet24.actual_net_margin_certificate
    f D L tau m0 hf (Z : Set E) hnet.1 hnet.2 hm

theorem actual_printed_ceiling_grid_cardinality_coverage_and_full_margin_compose
    (d : ℕ) (hd : 0 < d) (tau : ℝ) (ht : 0 < tau) :
    let N:=Nat.ceil (Real.sqrt d/(2*tau))
    IsFiniteNet (unitCube d) (centeredGrid d N) tau ∧
      (centeredGrid d N).card=N^d ∧
      ∀ (f : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ≥0) (m0 : ℝ),
        LipschitzOnWith L f (unitCube d) →
        (∀ z∈centeredGrid d N,m0 ≤ f z) →
        ∀ x∈unitCube d,m0-(L:ℝ)*tau ≤ f x := by
  dsimp only
  have hN:=actual_ceiling_grid_radius d hd tau ht
  have hGrid:=actual_centered_grid_covers d _ hN.1
  have hnet : IsFiniteNet (unitCube d)
      (centeredGrid d (Nat.ceil (Real.sqrt d/(2*tau)))) tau := by
    refine ⟨hGrid.1,?_⟩
    intro x hx
    obtain ⟨z,hz,he⟩:=hGrid.2 x hx
    exact ⟨z,hz,he.trans hN.2⟩
  refine ⟨hnet,actual_centered_grid_cardinality d _ hN.1,?_⟩
  intro f L m0 hf hm
  exact actual_general_finite_net_transfers_every_sampled_lower_margin _ _ _ _ _ _ hf hnet hm

end SafeLearning.CompleteFoundationsCubeRadiusAndNetMargin32


namespace SafeLearning.CompleteFoundationsCubeRadiusAndNetMargin32
open CompleteFoundationsCenteredCubeNetsWhole30

def cubeProjection (d : ℕ) (z : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => (Set.projIcc (0:ℝ) 1 (by norm_num) (z i) : ℝ))

theorem actual_ambient_center_projection_lies_inside_the_unit_cube
    (d : ℕ) (z : EuclideanSpace ℝ (Fin d)) : cubeProjection d z∈unitCube d := by
  intro i
  exact (Set.projIcc (0:ℝ) 1 (by norm_num) (z i)).property

theorem actual_center_projection_never_increases_distance_to_any_cube_point
    (d : ℕ) (x z : EuclideanSpace ℝ (Fin d)) (hx : x∈unitCube d) :
    dist x (cubeProjection d z) ≤ dist x z := by
  have hcoord : ∀ i : Fin d, |x i-cubeProjection d z i| ≤ |x i-z i| := by
    intro i
    have hp:=Set.abs_projIcc_sub_projIcc (a:=(0:ℝ)) (b:=1) (c:=x i) (d:=z i)
      (by norm_num : (0:ℝ) ≤ 1)
    have he : (Set.projIcc (0:ℝ) 1 (by norm_num) (x i) : ℝ)=x i := by
      exact congrArg Subtype.val (Set.projIcc_of_mem (by norm_num : (0:ℝ) ≤ 1) (hx i))
    simpa only [he,cubeProjection,PiLp.toLp_apply] using hp
  have hs : dist x (cubeProjection d z)^2 ≤ dist x z^2 := by
    rw [EuclideanSpace.dist_sq_eq,EuclideanSpace.dist_sq_eq]
    apply Finset.sum_le_sum
    intro i hi
    have h:=(sq_le_sq₀ (abs_nonneg (x i-cubeProjection d z i)) (abs_nonneg (x i-z i))).mpr (hcoord i)
    simpa only [Real.dist_eq,sq_abs] using h
  exact (sq_le_sq₀ (dist_nonneg (x:=x) (y:=cubeProjection d z))
    (dist_nonneg (x:=x) (y:=z))).mp hs

theorem actual_any_ambient_finite_cover_has_an_in_cube_cover_with_no_more_centers
    (d : ℕ) (tau : ℝ) (Z : Finset (EuclideanSpace ℝ (Fin d)))
    (hcover : ∀ x∈unitCube d,∃ z∈Z,dist x z ≤ tau) :
    ∃ Z' : Finset (EuclideanSpace ℝ (Fin d)),IsFiniteNet (unitCube d) Z' tau ∧ Z'.card ≤ Z.card := by
  classical
  refine ⟨Z.image (cubeProjection d),⟨?_,?_⟩,Finset.card_image_le⟩
  · intro y hy
    obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hy
    exact actual_ambient_center_projection_lies_inside_the_unit_cube d z
  · intro x hx
    obtain ⟨z,hz,he⟩:=hcover x hx
    exact ⟨cubeProjection d z,Finset.mem_image.mpr ⟨z,hz,rfl⟩,
      (actual_center_projection_never_increases_distance_to_any_cube_point d x z hx).trans he⟩

theorem actual_least_covering_number_also_minimizes_over_all_ambient_centered_balls
    (d : ℕ) (tau : ℝ) (ht : 0 < tau) :
    ∃ M : ℕ,IsLeast {n : ℕ | ∃ Z : Finset (EuclideanSpace ℝ (Fin d)),
      (∀ x∈unitCube d,∃ z∈Z,dist x z ≤ tau) ∧ Z.card=n} M ∧
      M ≤ Nat.ceil (Real.sqrt d/(2*tau))^d := by
  classical
  obtain ⟨M,hM,hcount⟩:=actual_covering_number_exists_and_obeys_source_bound d tau ht
  refine ⟨M,⟨?_,?_⟩,hcount⟩
  · obtain ⟨Z,hZ,hcard⟩:=hM.1
    exact ⟨Z,hZ.2,hcard⟩
  · rintro n ⟨Z,hZ,hcard⟩
    obtain ⟨Z',hZ',hcard'⟩:=actual_any_ambient_finite_cover_has_an_in_cube_cover_with_no_more_centers d tau Z hZ
    have hmin : M ≤ Z'.card := hM.2 ⟨Z',hZ',rfl⟩
    exact hmin.trans (hcard'.trans hcard.le)

end SafeLearning.CompleteFoundationsCubeRadiusAndNetMargin32

#print axioms SafeLearning.CompleteFoundationsCubeRadiusAndNetMargin32.actual_arbitrary_side_centered_cube_lies_in_its_half_diagonal_Euclidean_ball
#print axioms SafeLearning.CompleteFoundationsCubeRadiusAndNetMargin32.actual_cube_corner_attains_the_half_diagonal_radius
#print axioms SafeLearning.CompleteFoundationsCubeRadiusAndNetMargin32.actual_isometric_cube_image_has_the_same_half_diagonal_ball
#print axioms SafeLearning.CompleteFoundationsCubeRadiusAndNetMargin32.actual_general_finite_net_transfers_every_sampled_lower_margin
#print axioms SafeLearning.CompleteFoundationsCubeRadiusAndNetMargin32.actual_printed_ceiling_grid_cardinality_coverage_and_full_margin_compose
#print axioms SafeLearning.CompleteFoundationsCubeRadiusAndNetMargin32.actual_ambient_center_projection_lies_inside_the_unit_cube
#print axioms SafeLearning.CompleteFoundationsCubeRadiusAndNetMargin32.actual_center_projection_never_increases_distance_to_any_cube_point
#print axioms SafeLearning.CompleteFoundationsCubeRadiusAndNetMargin32.actual_any_ambient_finite_cover_has_an_in_cube_cover_with_no_more_centers
#print axioms SafeLearning.CompleteFoundationsCubeRadiusAndNetMargin32.actual_least_covering_number_also_minimizes_over_all_ambient_centered_balls
